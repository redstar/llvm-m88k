//===-- M88kFrameLowering.cpp - Frame lowering for M88k -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the M88k implementation of TargetFrameLowering class.
//
//===----------------------------------------------------------------------===//

#include "M88kFrameLowering.h"
#include "M88kInstrInfo.h"
#include "M88kMachineFunctionInfo.h"
#include "M88kRegisterInfo.h"
#include "M88kSubtarget.h"
#include "MCTargetDesc/M88kMCTargetDesc.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/RegisterScavenging.h"
#include "llvm/CodeGen/TargetFrameLowering.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Target/TargetMachine.h"
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <vector>

/*
 * The M88k stack layout:
 * +------------------------------+ High Address
 * |                              |
 * |                              |
 * | Argument Area                | <- SP before call
 * +------------------------------+    Pointer to last allocated word
 * |                              |    16-byte aligned
 * | Temporary Space /            |
 * | Local Variable Space         |
 * | (optional)                   |
 * | return address               |
 * | previous FP                  | <- FP after prologue
 * +------------------------------+    16-byte aligned
 * | Preserved registers r25..r14 |
 * | Preserved registers x29..x22 |
 * | Dynamic allocated space      |
 * | Argument Area                | <- SP after call
 * +------------------------------+    16-byte aligned
 * |                              |
 * |                              |
 * +------------------------------+ <- Low Address
 *
 * Prologue pattern:
 * 1. Allocate new stack frame
 * 2. Store r30 (FP) and r1 (RA)
 * 3. Setup new frame pointer
 *
 * The stack frame consists of the local variable space and the argument area.
 * The frame pointer is set up in the way that
 * - r30: previous frame pointer r30
 * - r30 + 4: return address r1
 * - r30 + 8: first free local variable slot
 *
 * E.g.
 *   subu     %r31,%r31,32 | Allocate 32 bytes
 *   st       %r1,%r31,20  | Store r1 aka RA
 *   st       %r30,%r31,16 | Store r30 aka FP
 *   addu     %r30,%r31,16 | Establish new FP
 *
 * or with callee-saved registers:
 *   subu     %r31,%r31,64 | Allocate 64 bytes
 *   st       %r1,%r31,52  | Store r1 aka RA
 *   st       %r30,%r31,48 | Store r30 aka FP
 *   st.d     %r24,%r31,40 | Store r24 and r25 (callee saved) 
 *   st.d     %r22,%r31,32 | Store r22 and r23 (callee saved) 
 *   st.d     %r20,%r31,24 | Store r20 and r21 (callee saved) 
 *   st.d     %r18,%r31,16 | Store r18 and r19 (callee saved) 
 *   st.d     %r16,%r31,8  | Store r16 and r17 (callee saved) 
 *   addu     %r30,%r31,48 | Establish new FP
 *
 * SP and FP are 16-byte aligned.
 *
 * The frame pointer can be omitted in leaf functions upon request.
 *
 * Registers r1 and r30 must be saved when generating debug information.
 *
 * Epilogue for the latter prologue example:
 *   subu     %r31,%r30,48 | Adjust SP
 *   ld       %r1,%r31,52  | Load r1 aka RA
 *   ld       %r30,%r31,48 | Load r30 aka FP
 *   ld.d     %r24,%r31,40 | Load r24 and r25 (callee saved)
 *   ld.d     %r22,%r31,32 | Store r22 and r23 (callee saved)
 *   ld.d     %r20,%r31,24 | Store r20 and r21 (callee saved)
 *   ld.d     %r18,%r31,16 | Store r18 and r19 (callee saved)
 *   ld.d     %r16,%r31,8  | Store r16 and r17 (callee saved)
 *   addu     %r31,%r31,64 | Deallocate stack frame
 *   jmp      %r1          | Return to caller
 */

using namespace llvm;

#define DEBUG_TYPE "m88kframelowering" 

M88kFrameLowering::M88kFrameLowering(const M88kSubtarget &Subtarget)
    : TargetFrameLowering(TargetFrameLowering::StackGrowsDown, Align(16),
                          /*LocalAreaOffset=*/0, Align(8),
                          /*StackRealignable=*/false),
      STI(Subtarget) {}

bool M88kFrameLowering::hasFP(const MachineFunction &MF) const {
  const MachineFrameInfo &MFI = MF.getFrameInfo();

  // ABI-required frame pointer.
  if (MF.getTarget().Options.DisableFramePointerElim(MF))
    return true;

  // Frame pointer required for use within this function.
  return (MFI.hasCalls() || MFI.hasVarSizedObjects() ||
          MFI.isFrameAddressTaken());
}

bool M88kFrameLowering::hasReservedCallFrame(const MachineFunction &MF) const {
  // The argument area is allocated by the caller.
  return true;
}

void M88kFrameLowering::determineCalleeSaves(MachineFunction &MF,
                                             BitVector &SavedRegs,
                                             RegScavenger *RS) const {
  TargetFrameLowering::determineCalleeSaves(MF, SavedRegs, RS);

  MachineFrameInfo &MFFrame = MF.getFrameInfo();

  // If the function calls other functions, record that the return
  // address register will be clobbered.
  if (MFFrame.hasCalls())
    SavedRegs.set(M88k::R1);

  // If the function uses a FP, then add %r30 to the list.
  if (hasFP(MF))
    SavedRegs.set(M88k::R30);
}

bool M88kFrameLowering::assignCalleeSavedSpillSlots(
    MachineFunction &MF, const TargetRegisterInfo *TRI,
    std::vector<CalleeSavedInfo> &CSI) const {
  MachineFrameInfo &MFI = MF.getFrameInfo();
  M88kMachineFunctionInfo *FuncInfo = MF.getInfo<M88kMachineFunctionInfo>();

  for (std::vector<CalleeSavedInfo>::iterator I = CSI.begin(); I != CSI.end();
       ++I) {
    Register Reg = I->getReg();

    // Replace an odd numbered register followed by the previous even numbered
    // register with an even/odd register pair. 
    if (M88k::GPRRegClass.contains(Reg)) {
      if (((Reg - M88k::R0) & 1) && I + 1 != CSI.end() &&
          (I + 1)->getReg() == Reg - 1) {
        Reg = TRI->getMatchingSuperReg(Reg, M88k::sub_lo, &M88k::GPR64RegClass);
        I = CSI.erase(I);
        *I = CalleeSavedInfo(Reg);
      }
    }

    // Create the spill slots. The spill slot of the previous frame pointer
    // must have stack alignment.
    const TargetRegisterClass *RC = TRI->getMinimalPhysRegClass(Reg);
    Align Alignment =
        (Reg == M88k::R30) ? getStackAlign() : TRI->getSpillAlign(*RC);
    unsigned Size = TRI->getSpillSize(*RC);
    I->setFrameIdx(MFI.CreateSpillStackObject(Size, Alignment));
    if (Reg == M88k::R30)
      FuncInfo->setFramePointerIndex(I->getFrameIdx());
  }
  LLVM_DEBUG(MFI.dump(MF));
  return true;
}

bool M88kFrameLowering::spillCalleeSavedRegisters(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    ArrayRef<CalleeSavedInfo> CSI, const TargetRegisterInfo *TRI) const {
  MachineFunction *MF = MBB.getParent();
  const TargetSubtargetInfo &STI = MF->getSubtarget();
  const TargetInstrInfo *TII = STI.getInstrInfo();
  const Register RAReg = STI.getRegisterInfo()->getRARegister();

  for (auto &CS : CSI) {
    // Add the callee-saved register as live-in.
    Register Reg = CS.getReg();
    if (!MBB.isLiveIn(Reg))
      MBB.addLiveIn(Reg);

    // Check if register is the return address register and if the return
    // address was taken. Do not kill the register in this case.
    bool IsRAAndRetAddrIsTaken =
        Reg == RAReg && MF->getFrameInfo().isReturnAddressTaken();

    // Save in the normal TargetInstrInfo way.
    const TargetRegisterClass *RC = TRI->getMinimalPhysRegClass(Reg);
    TII->storeRegToStackSlot(MBB, MBBI, Reg, /*isKill=*/!IsRAAndRetAddrIsTaken,
                             CS.getFrameIdx(), RC, TRI, Register());

    // Mark the store with the FrameSetup flag.
    std::prev(MBBI)->setFlag(MachineInstr::FrameSetup);
  }

  return true;
}

void M88kFrameLowering::emitPrologue(MachineFunction &MF,
                                     MachineBasicBlock &MBB) const {
  assert(&MF.front() == &MBB && "Shrink-wrapping not yet supported");

  MachineFrameInfo &MFI = MF.getFrameInfo();
  const M88kInstrInfo &LII = *STI.getInstrInfo();
  MachineBasicBlock::iterator MBBI = MBB.begin();
  M88kMachineFunctionInfo *FuncInfo = MF.getInfo<M88kMachineFunctionInfo>();

  // Debug location must be unknown since the first debug location is used
  // to determine the end of the prologue.
  DebugLoc DL;

  unsigned StackSize = MFI.getStackSize();

  unsigned MaxCallFrameSize = MFI.getMaxCallFrameSize();

  bool SetupFP = hasFP(MF);
  assert((SetupFP || MaxCallFrameSize == 0) && "Call frame without FP");

  if (StackSize) {
    if (isInt<16>(StackSize)) {
      // Create subu %r31, %r31, StackSize
      BuildMI(MBB, MBBI, DL, LII.get(M88k::SUBUri), M88k::R31)
          .addReg(M88k::R31)
          .addImm(StackSize)
          .setMIFlag(MachineInstr::FrameSetup);
    } else {
      // Load stack size into scratch register r10.
      BuildMI(MBB, MBBI, DL, LII.get(M88k::ORriu), M88k::R10)
          .addReg(M88k::R0)
          .addImm(StackSize >> 16)
          .setMIFlag(MachineInstr::FrameSetup);
      BuildMI(MBB, MBBI, DL, LII.get(M88k::ORri), M88k::R10)
          .addReg(M88k::R10)
          .addImm(StackSize & 0xFFFF)
          .setMIFlag(MachineInstr::FrameSetup);
      // Create subu %r31, %r31, %r10
      BuildMI(MBB, MBBI, DL, LII.get(M88k::SUBUrr), M88k::R31)
          .addReg(M88k::R31)
          .addReg(M88k::R10, RegState::Kill)
          .setMIFlag(MachineInstr::FrameSetup);
    }

    // Skip over the register spills.
    while (MBBI->getFlag(MachineInstr::FrameSetup))
      ++MBBI;

    if (SetupFP) {
      int64_t Offset =
          StackSize + MFI.getObjectOffset(FuncInfo->getFramePointerIndex());

      // Install FP: addu %r30, %r31, MaxCallFrameSize
      BuildMI(MBB, MBBI, DL, LII.get(M88k::ADDUri))
          .addReg(M88k::R30, RegState::Define)
          .addReg(M88k::R31)
          .addImm(Offset)
          .setMIFlag(MachineInstr::FrameSetup);
    }
  }
}

void M88kFrameLowering::emitEpilogue(MachineFunction &MF,
                                     MachineBasicBlock &MBB) const {
  MachineFrameInfo &MFI = MF.getFrameInfo();
  const M88kInstrInfo &LII =
      *static_cast<const M88kInstrInfo *>(STI.getInstrInfo());
  MachineBasicBlock::iterator MBBI = MBB.getLastNonDebugInstr();
  DebugLoc DL = MBBI->getDebugLoc();

  unsigned StackSize = MFI.getStackSize();

  if (StackSize) {
    if (isInt<16>(StackSize)) {
      // Restore %r31: add %r31, %r31, StackSize
      BuildMI(MBB, MBBI, DL, LII.get(M88k::ADDUri), M88k::R31)
          .addReg(M88k::R31)
          .addImm(StackSize)
          .setMIFlag(MachineInstr::FrameDestroy);
    } else {
      // Load stack size into scratch register r10.
      BuildMI(MBB, MBBI, DL, LII.get(M88k::ORriu), M88k::R10)
          .addReg(M88k::R0)
          .addImm(StackSize >> 16);
      BuildMI(MBB, MBBI, DL, LII.get(M88k::ORri), M88k::R10)
          .addReg(M88k::R10)
          .addImm(StackSize & 0xFFFF);
      // Create subu %r31, %r31, %r10
      BuildMI(MBB, MBBI, DL, LII.get(M88k::ADDUrr), M88k::R31)
          .addReg(M88k::R31)
          .addReg(M88k::R10, RegState::Kill);
    }
  }
}

void M88kFrameLowering::processFunctionBeforeFrameIndicesReplaced(
    MachineFunction &MF, RegScavenger *RS) const {
  M88kMachineFunctionInfo *FuncInfo = MF.getInfo<M88kMachineFunctionInfo>();
  MachineFrameInfo &MFI = MF.getFrameInfo();
  std::vector<CalleeSavedInfo> &CSI = MFI.getCalleeSavedInfo();

  // Adjust offset of spill slot of the return address register. Due to the
  // alignment of the spill slot of the previous frame register, there may be a
  // gap between both slots. The adjustment moves the spill slot together.
  auto RetAddr =
      std::find_if(CSI.begin(), CSI.end(), [](const CalleeSavedInfo &CS) {
        return CS.getReg() == M88k::R1;
      });
  if (RetAddr != CSI.end() && FuncInfo->getFramePointerIndex())
    MFI.setObjectOffset(RetAddr->getFrameIdx(),
                        MFI.getObjectOffset(FuncInfo->getFramePointerIndex()) +
                            4);
}
