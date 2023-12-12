//===-- M88kRegisterInfo.cpp - M88k Register Information ------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the M88k implementation of the TargetRegisterInfo class.
//
//===----------------------------------------------------------------------===//

#include "M88kRegisterInfo.h"
#include "M88kFrameLowering.h"
#include "M88kMachineFunctionInfo.h"
#include "M88kSubtarget.h"
#include "MCTargetDesc/M88kMCTargetDesc.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/MC/MCRegister.h"
#include "llvm/Support/MathExtras.h"
#include <cassert>
#include <cstdint>
#include <vector>

using namespace llvm;

#define GET_REGINFO_TARGET_DESC
#include "M88kGenRegisterInfo.inc"

M88kRegisterInfo::M88kRegisterInfo() : M88kGenRegisterInfo(M88k::R1) {}

const MCPhysReg *
M88kRegisterInfo::getCalleeSavedRegs(const MachineFunction *MF) const {
  //if (MF->getSubtarget<M88kSubtarget>().isMC88110())
  //  return CSR_M88k_MC88110_SaveList;
  return CSR_M88k_SaveList;
}

BitVector M88kRegisterInfo::getReservedRegs(const MachineFunction &MF) const {
  BitVector Reserved(getNumRegs());

  // R0 is always reserved.
  Reserved.set(M88k::R0);

  // X0 is always reserved on the MC88110.
  if (MF.getSubtarget<M88kSubtarget>().isMC88110())
    Reserved.set(M88k::X0);

  // R28 and R29 are always reserved according to SYS-V ABI.
  Reserved.set(M88k::R28);
  Reserved.set(M88k::R29);

  // R31 is the stack pointer.
  Reserved.set(M88k::R31);

  // If the function uses the frame pointer, then R30 is reserved.
  if (getFrameLowering(MF)->hasFP(MF))
    Reserved.set(M88k::R30);

  // X30 and X31 are reserved for future ABI use.
  if (MF.getSubtarget<M88kSubtarget>().isMC88110()) {
    Reserved.set(M88k::X30);
    Reserved.set(M88k::X31);
  }

  return Reserved;
}

const uint32_t *
M88kRegisterInfo::getCallPreservedMask(const MachineFunction &MF,
                                       CallingConv::ID CC) const {
  return CSR_M88k_RegMask;
}

bool M88kRegisterInfo::eliminateFrameIndex(MachineBasicBlock::iterator II,
                                           int SPAdj, unsigned FIOperandNum,
                                           RegScavenger *RS) const {
  assert(SPAdj == 0 && "Unexpected stack adjustment");

  MachineInstr &MI = *II;
  MachineFunction &MF = *MI.getParent()->getParent();
  MachineFrameInfo &MFI = MF.getFrameInfo();

  int FrameIndex = MI.getOperand(FIOperandNum).getIndex();

  const std::vector<CalleeSavedInfo> &CSI = MFI.getCalleeSavedInfo();
  int MinCSFI = 0;
  int MaxCSFI = -1;

  if (CSI.size()) {
    MinCSFI = CSI[0].getFrameIdx();
    MaxCSFI = CSI[CSI.size() - 1].getFrameIdx();
  }

  // The following stack frame objects are always referenced relative to r31:
  //  1. Outgoing arguments.
  //  2. Pointer to dynamically allocated stack space.
  //  3. Locations for callee-saved registers.
  // Everything else is referenced relative to whatever register
  // getFrameRegister() returns.
  Register FrameReg;
  if (FrameIndex >= MinCSFI && FrameIndex <= MaxCSFI)
    FrameReg = M88k::R31;
  else if (hasStackRealignment(MF)) {
    if (MFI.hasVarSizedObjects() && !MFI.isFixedObjectIndex(FrameIndex))
      FrameReg = M88k::R31;
    else if (MFI.isFixedObjectIndex(FrameIndex))
      FrameReg = getFrameRegister(MF);
    else
      FrameReg = M88k::R31;
  } else
    FrameReg = getFrameRegister(MF);

  uint64_t StackSize = MFI.getStackSize();
  int64_t SPOffset = MFI.getObjectOffset(FrameIndex);

  int64_t Offset = SPOffset + static_cast<int64_t>(StackSize);
  // If the location is addressed using the frame pointer register, then we need
  // to adjust the offset by the distance between the stack pointer and the
  // frame pointer.
  if (FrameReg == M88k::R30) {
    M88kMachineFunctionInfo *FuncInfo = MF.getInfo<M88kMachineFunctionInfo>();
    Offset -= (MFI.getObjectOffset(FuncInfo->getFramePointerIndex()) + static_cast<int64_t>(StackSize));
  }
  Offset += MI.getOperand(FIOperandNum + 1).getImm();

  // TODO Implement offsets larger 16k.
  assert(isInt<16>(Offset) && "m88k: Larger offsets not yet supported.");
  MI.getOperand(FIOperandNum).ChangeToRegister(FrameReg, /*isDef=*/false);
  MI.getOperand(FIOperandNum + 1).ChangeToImmediate(Offset);
  return false;
}

Register M88kRegisterInfo::getFrameRegister(const MachineFunction &MF) const {
  if (getFrameLowering(MF)->hasFP(MF))
    return M88k::R30;
  return M88k::R31;
}

const TargetRegisterClass *
M88kRegisterInfo::getPointerRegClass(const MachineFunction &MF,
                                     unsigned Kind) const {
  return &M88k::GPRRegClass;
}
