//===-- M88kCallLowering.cpp - Call lowering --------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file implements the lowering of LLVM calls to machine code calls for
/// GlobalISel.
//
//===----------------------------------------------------------------------===//

#include "M88kCallLowering.h"
#include "M88kCallingConv.h"
#include "M88kInstrInfo.h"
#include "M88kMachineFunctionInfo.h"
#include "M88kRegisterInfo.h"
#include "M88kSubtarget.h"
#include "MCTargetDesc/M88kMCTargetDesc.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/CodeGen/CallingConvLower.h"
#include "llvm/CodeGen/GlobalISel/CallLowering.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineMemOperand.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/TargetCallingConv.h"
#include "llvm/CodeGen/TargetFrameLowering.h"
#include "llvm/CodeGenTypes/LowLevelType.h"
#include "llvm/Support/Alignment.h"
#include <cassert>
#include <cstdint>
#include <functional>

using namespace llvm;

M88kCallLowering::M88kCallLowering(const M88kTargetLowering &TLI)
    : CallLowering(&TLI) {}

namespace {

struct OutgoingArgHandler : public CallLowering::OutgoingValueHandler {
  OutgoingArgHandler(MachineIRBuilder &MIRBuilder, MachineRegisterInfo &MRI,
                     MachineInstrBuilder MIB)
      : OutgoingValueHandler(MIRBuilder, MRI), MIB(MIB), SPReg() {}

  void assignValueToReg(Register ValVReg, Register PhysReg,
                        const CCValAssign &VA) override;

  unsigned assignCustomValue(CallLowering::ArgInfo &Arg,
                             ArrayRef<CCValAssign> VAs,
                             std::function<void()> *Thunk = nullptr) override;

  void assignValueToAddress(Register ValVReg, Register Addr, LLT MemTy,
                            const MachinePointerInfo &MPO,
                            const CCValAssign &VA) override;

  Register getStackAddress(uint64_t Size, int64_t Offset,
                           MachinePointerInfo &MPO,
                           ISD::ArgFlagsTy Flags) override;

  MachineInstrBuilder MIB;
  Register SPReg;
};

struct M88kIncomingValueHandler : public CallLowering::IncomingValueHandler {
  M88kIncomingValueHandler(MachineIRBuilder &MIRBuilder,
                           MachineRegisterInfo &MRI)
      : CallLowering::IncomingValueHandler(MIRBuilder, MRI) {}

  void assignValueToReg(Register ValVReg, Register PhysReg,
                        const CCValAssign &VA) override;

  void assignValueToAddress(Register ValVReg, Register Addr, LLT MemTy,
                            const MachinePointerInfo &MPO,
                            const CCValAssign &VA) override;

  Register getStackAddress(uint64_t Size, int64_t Offset,
                           MachinePointerInfo &MPO,
                           ISD::ArgFlagsTy Flags) override;

  unsigned assignCustomValue(CallLowering::ArgInfo &Arg,
                             ArrayRef<CCValAssign> VAs,
                             std::function<void()> *Thunk = nullptr) override;

  /// Marking a physical register as used is different between formal
  /// parameters, where it's a basic block live-in, and call returns, where it's
  /// an implicit-def of the call instruction.
  virtual void markPhysRegUsed(unsigned PhysReg) = 0;
};

struct FormalArgHandler : public M88kIncomingValueHandler {
  FormalArgHandler(MachineIRBuilder &MIRBuilder, MachineRegisterInfo &MRI)
      : M88kIncomingValueHandler(MIRBuilder, MRI) {}

  void markPhysRegUsed(unsigned PhysReg) override {
    MIRBuilder.getMRI()->addLiveIn(PhysReg);
    MIRBuilder.getMBB().addLiveIn(PhysReg);
  }
};

struct CallReturnHandler : public M88kIncomingValueHandler {
  CallReturnHandler(MachineIRBuilder &MIRBuilder, MachineRegisterInfo &MRI,
                    MachineInstrBuilder MIB)
      : M88kIncomingValueHandler(MIRBuilder, MRI), MIB(MIB) {}

  void markPhysRegUsed(unsigned PhysReg) override {
    MIB.addDef(PhysReg, RegState::Implicit);
  }

  MachineInstrBuilder MIB;
};

} // namespace

void OutgoingArgHandler::assignValueToReg(Register ValVReg, Register PhysReg,
                                          const CCValAssign &VA) {
  MIB.addUse(PhysReg, RegState::Implicit);
  Register ExtReg = extendRegister(ValVReg, VA);
  MIRBuilder.buildCopy(PhysReg, ExtReg);
}

unsigned OutgoingArgHandler::assignCustomValue(CallLowering::ArgInfo &Arg,
                                               ArrayRef<CCValAssign> VAs,
                                               std::function<void()> *Thunk) {
  assert(Arg.Regs.size() == 1 && "Can't handle multple regs yet");

  CCValAssign HiVA = VAs[0];
  assert(HiVA.needsCustom() && "Value doesn't need custom handling");

  // Custom lowering for other types, such as f16, is currently not supported.
  if (HiVA.getValVT() != MVT::f64 && HiVA.getValVT() != MVT::i64)
    return 0;

  CCValAssign LoVA = VAs[1];
  assert(LoVA.needsCustom() && "Value doesn't need custom handling");
  assert((LoVA.getValVT() == MVT::f64 || HiVA.getValVT() == MVT::i64) &&
         "Unsupported type");

  assert(HiVA.getValNo() == LoVA.getValNo() &&
         "Values belong to different arguments");

  assert(HiVA.isRegLoc() && "Value should be in reg");
  assert(LoVA.isRegLoc() && "Value should be in reg");

  Register NewRegs[] = {MRI.createGenericVirtualRegister(LLT::scalar(32)),
                        MRI.createGenericVirtualRegister(LLT::scalar(32))};
  MIRBuilder.buildUnmerge(NewRegs, Arg.Regs[0]);

  if (Thunk) {
    *Thunk = [=]() {
      assignValueToReg(NewRegs[0], LoVA.getLocReg(), LoVA);
      assignValueToReg(NewRegs[1], HiVA.getLocReg(), HiVA);
    };
    return 2;
  }
  assignValueToReg(NewRegs[0], LoVA.getLocReg(), LoVA);
  assignValueToReg(NewRegs[1], HiVA.getLocReg(), HiVA);
  return 2;
}

void OutgoingArgHandler::assignValueToAddress(Register ValVReg, Register Addr,
                                              LLT MemTy,
                                              const MachinePointerInfo &MPO,
                                              const CCValAssign &VA) {
  MachineFunction &MF = MIRBuilder.getMF();
  uint64_t LocMemOffset = VA.getLocMemOffset();

  auto *MMO = MF.getMachineMemOperand(
      MPO, MachineMemOperand::MOStore, MemTy,
      commonAlignment(Align(16) /*STI.getStackAlignment()*/, LocMemOffset));

  Register ExtReg = extendRegister(ValVReg, VA);
  MIRBuilder.buildStore(ExtReg, Addr, *MMO);
}

Register OutgoingArgHandler::getStackAddress(uint64_t Size, int64_t Offset,
                                             MachinePointerInfo &MPO,
                                             ISD::ArgFlagsTy Flags) {
  MachineFunction &MF = MIRBuilder.getMF();
  MPO = MachinePointerInfo::getStack(MF, Offset);

  LLT P0 = LLT::pointer(0, 32);
  LLT S32 = LLT::scalar(32);
  if (!SPReg)
    SPReg = MIRBuilder.buildCopy(P0, Register(M88k::R31)).getReg(0);

  auto OffsetReg = MIRBuilder.buildConstant(S32, Offset);
  auto AddrReg = MIRBuilder.buildPtrAdd(P0, SPReg, OffsetReg);
  return AddrReg.getReg(0);
}

void M88kIncomingValueHandler::assignValueToReg(Register ValVReg,
                                                Register PhysReg,
                                                const CCValAssign &VA) {
  assert(VA.isRegLoc() && "Value shouldn't be assigned to reg");
  assert(VA.getLocReg() == PhysReg && "Assigning to the wrong reg?");

  uint64_t ValSize = VA.getValVT().getFixedSizeInBits();
  uint64_t LocSize = VA.getLocVT().getFixedSizeInBits();

  assert(ValSize <= 64 && "Unsupported value size");
  assert(LocSize <= 64 && "Unsupported location size");

  markPhysRegUsed(PhysReg);
  if (ValSize == LocSize) {
    MIRBuilder.buildCopy(ValVReg, PhysReg);
  } else {
    assert(ValSize < LocSize && "Extensions not supported");

    // We cannot create a truncating copy, nor a trunc of a physical register.
    // Therefore, we need to copy the content of the physical register into a
    // virtual one and then truncate that.
    auto PhysRegToVReg = MIRBuilder.buildCopy(LLT::scalar(LocSize), PhysReg);
    MIRBuilder.buildTrunc(ValVReg, PhysRegToVReg);
  }
}

void M88kIncomingValueHandler::assignValueToAddress(
    Register ValVReg, Register Addr, LLT MemTy, const MachinePointerInfo &MPO,
    const CCValAssign &VA) {
  MachineFunction &MF = MIRBuilder.getMF();
  auto *MMO = MF.getMachineMemOperand(MPO, MachineMemOperand::MOLoad, MemTy,
                                      inferAlignFromPtrInfo(MF, MPO));
  MIRBuilder.buildLoad(ValVReg, Addr, *MMO);
}

Register M88kIncomingValueHandler::getStackAddress(uint64_t Size,
                                                   int64_t Offset,
                                                   MachinePointerInfo &MPO,
                                                   ISD::ArgFlagsTy Flags) {
  auto &MFI = MIRBuilder.getMF().getFrameInfo();
  const bool IsImmutable = !Flags.isByVal();
  int FI = MFI.CreateFixedObject(Size, Offset, IsImmutable);
  MPO = MachinePointerInfo::getFixedStack(MIRBuilder.getMF(), FI);

  // Build Frame Index
  llvm::LLT FramePtr = LLT::pointer(0, 32);
  MachineInstrBuilder AddrReg = MIRBuilder.buildFrameIndex(FramePtr, FI);
  return AddrReg.getReg(0);
}

unsigned
M88kIncomingValueHandler::assignCustomValue(CallLowering::ArgInfo &Arg,
                                            ArrayRef<CCValAssign> VAs,
                                            std::function<void()> *Thunk) {
  assert(Arg.Regs.size() == 1 && "Can't handle multple regs yet");

  CCValAssign HiVA = VAs[0];
  assert(HiVA.needsCustom() && "Value doesn't need custom handling");

  // Custom lowering for other types is currently not supported.
  if (HiVA.getValVT() != MVT::f64 && HiVA.getValVT() != MVT::i64)
    return 0;

  CCValAssign LoVA = VAs[1];
  assert(LoVA.needsCustom() && "Value doesn't need custom handling");
  assert((LoVA.getValVT() == MVT::f64 || LoVA.getValVT() == MVT::i64) &&
         "Unsupported type");

  assert(HiVA.getValNo() == LoVA.getValNo() &&
         "Values belong to different arguments");

  assert(HiVA.isRegLoc() && "Value should be in reg");
  assert(LoVA.isRegLoc() && "Value should be in reg");

  Register NewRegs[] = {MRI.createGenericVirtualRegister(LLT::scalar(32)),
                        MRI.createGenericVirtualRegister(LLT::scalar(32))};

  assignValueToReg(NewRegs[0], LoVA.getLocReg(), LoVA);
  assignValueToReg(NewRegs[1], HiVA.getLocReg(), HiVA);

  MIRBuilder.buildMergeLikeInstr(Arg.Regs[0], NewRegs);

  return 2;
}

bool M88kCallLowering::lowerReturn(MachineIRBuilder &MIRBuilder,
                                   const Value *Val, ArrayRef<Register> VRegs,
                                   FunctionLoweringInfo &FLI,
                                   Register SwiftErrorVReg) const {
  MachineFunction &MF = MIRBuilder.getMF();
  const Function &F = MF.getFunction();
  MachineRegisterInfo &MRI = MF.getRegInfo();
  auto &DL = F.getParent()->getDataLayout();

  auto MIB = MIRBuilder.buildInstrNoInsert(M88k::RET);

  bool Success = true;
  if (!VRegs.empty()) {
    SmallVector<ArgInfo, 8> SplitArgs;
    ArgInfo OrigArg{VRegs, Val->getType(), 0};
    setArgFlags(OrigArg, AttributeList::ReturnIndex, DL, F);
    splitToValueTypes(OrigArg, SplitArgs, DL, F.getCallingConv());
    OutgoingValueAssigner ArgAssigner(RetCC_M88k);
    OutgoingArgHandler ArgHandler(MIRBuilder, MRI, MIB);
    Success = determineAndHandleAssignments(ArgHandler, ArgAssigner, SplitArgs,
                                            MIRBuilder, F.getCallingConv(),
                                            F.isVarArg());
  }

  MIRBuilder.insertInstr(MIB);
  return Success;
}

bool M88kCallLowering::lowerFormalArguments(MachineIRBuilder &MIRBuilder,
                                            const Function &F,
                                            ArrayRef<ArrayRef<Register>> VRegs,
                                            FunctionLoweringInfo &FLI) const {
  MachineFunction &MF = MIRBuilder.getMF();
  MachineRegisterInfo &MRI = MF.getRegInfo();
  const auto &DL = F.getParent()->getDataLayout();

  SmallVector<ArgInfo, 8> SplitArgs;
  unsigned I = 0;
  for (const auto &Arg : F.args()) {
    ArgInfo OrigArg{VRegs[I], Arg.getType(), I};
    setArgFlags(OrigArg, I + AttributeList::FirstArgIndex, DL, F);
    splitToValueTypes(OrigArg, SplitArgs, DL, F.getCallingConv());
    ++I;
  }

  IncomingValueAssigner ArgAssigner(CC_M88k);
  FormalArgHandler ArgHandler(MIRBuilder, MRI);
  SmallVector<CCValAssign, 16> ArgLocs;
  CCState CCInfo(F.getCallingConv(), F.isVarArg(), MF, ArgLocs, F.getContext());
  if (!determineAssignments(ArgAssigner, SplitArgs, CCInfo) ||
      !handleAssignments(ArgHandler, SplitArgs, CCInfo, ArgLocs, MIRBuilder))
    return false;

  if (F.isVarArg()) {
    // TODO Is there a better place for this array?
    static constexpr size_t ArgRegsSize = 8;
    static const MCPhysReg ArgRegs[ArgRegsSize] = {M88k::R2, M88k::R3, M88k::R4,
                                                   M88k::R5, M88k::R6, M88k::R7,
                                                   M88k::R8, M88k::R9};
    static constexpr size_t ArgPairRegsSize = 4;
    static const MCPhysReg ArgPairRegs[ArgPairRegsSize] = {
        M88k::R2_R3, M88k::R4_R5, M88k::R6_R7, M88k::R8_R9};

    M88kMachineFunctionInfo *FuncInfo = MF.getInfo<M88kMachineFunctionInfo>();
    MachineFrameInfo &MFI = MF.getFrameInfo();

    unsigned FirstVariadicReg = CCInfo.getFirstUnallocated(ArgRegs);
    unsigned GPRSaveSize = 4 * (ArgRegsSize - FirstVariadicReg);
    if (GPRSaveSize != 0) {
      const LLT P0 = LLT::pointer(0, 32);
      const LLT S32 = LLT::scalar(32);
      const LLT S64 = LLT::scalar(64);

      // Align the size of the save area to 8. The first slot will be empty if
      // an odd number of registers need to be saved.
      unsigned GPRIdx =
          MFI.CreateStackObject(alignTo(GPRSaveSize, 8), Align(8), false);
      auto FIN = MIRBuilder.buildFrameIndex(P0, GPRIdx);
      auto Offset =
          MIRBuilder.buildConstant(MRI.createGenericVirtualRegister(S32), 8);

      // Assign the registers. The first register requires special handling if
      // it has a odd number, because st.d cannot be used in this case.
      unsigned OddRegNo = FirstVariadicReg & 0x1;
      unsigned FirstVariadicPairReg = (FirstVariadicReg + OddRegNo) >> 1;
      if (OddRegNo) {
        auto Offset =
            MIRBuilder.buildConstant(MRI.createGenericVirtualRegister(S32), 4);
        Register Val = MRI.createGenericVirtualRegister(S32);
        ArgHandler.assignValueToReg(
            Val, ArgRegs[I],
            CCValAssign::getReg(I + MF.getFunction().getNumOperands(), MVT::i32,
                                ArgRegs[I], MVT::i32, CCValAssign::Full));
        auto MPO = MachinePointerInfo::getFixedStack(MF, GPRIdx, 4);
        FIN = MIRBuilder.buildPtrAdd(MRI.createGenericVirtualRegister(P0),
                                     FIN.getReg(0), Offset);
        MIRBuilder.buildStore(Val, FIN, MPO, inferAlignFromPtrInfo(MF, MPO));
        FIN = MIRBuilder.buildPtrAdd(MRI.createGenericVirtualRegister(P0),
                                     FIN.getReg(0), Offset);
      }
      for (unsigned I = FirstVariadicPairReg, E = ArgPairRegsSize; I < E;
           ++I) {
        Register Val = MRI.createGenericVirtualRegister(S64);
        ArgHandler.assignValueToReg(
            Val, ArgPairRegs[I],
            CCValAssign::getReg(I + MF.getFunction().getNumOperands(), MVT::i64,
                                ArgPairRegs[I], MVT::i64, CCValAssign::Full));
        auto MPO = MachinePointerInfo::getFixedStack(MF, GPRIdx, I * 8);
        MIRBuilder.buildStore(Val, FIN, MPO, inferAlignFromPtrInfo(MF, MPO));

        FIN = MIRBuilder.buildPtrAdd(MRI.createGenericVirtualRegister(P0),
                                     FIN.getReg(0), Offset);
      }

      FuncInfo->setVarArgsFirstReg(FirstVariadicReg);
      FuncInfo->setVarArgsRegIndex(GPRIdx);
    }

    // Create frame index of first var arg stack parameter.
    FuncInfo->setStackIndex(
        MFI.CreateFixedObject(4, CCInfo.getStackSize(), false));
  }
  return true;
}

bool M88kCallLowering::lowerCall(MachineIRBuilder &MIRBuilder,
                                 CallLoweringInfo &Info) const {
  MachineFunction &MF = MIRBuilder.getMF();
  const Function &F = MF.getFunction();
  MachineRegisterInfo &MRI = MF.getRegInfo();
  auto &DL = F.getParent()->getDataLayout();

  SmallVector<ArgInfo, 8> OutArgs;
  for (const auto &OrigArg : Info.OrigArgs) {
    splitToValueTypes(OrigArg, OutArgs, DL, Info.CallConv);
  }

  SmallVector<ArgInfo, 8> InArgs;
  if (!Info.OrigRet.Ty->isVoidTy())
    splitToValueTypes(Info.OrigRet, InArgs, DL, Info.CallConv);

  // TODO Handle tail calls.

  // Create a temporarily-floating call instruction so we can add the implicit
  // uses of arg registers.
  unsigned Opc = Info.Callee.isReg() ? M88k::JSR : M88k::BSR;

  auto MIB = MIRBuilder.buildInstrNoInsert(Opc);
  MIB.add(Info.Callee);

  // Tell the call which registers are clobbered.
  const uint32_t *Mask;
  const M88kSubtarget &Subtarget = MF.getSubtarget<M88kSubtarget>();
  const auto *TRI = Subtarget.getRegisterInfo();

  // Do the actual argument marshalling.
  OutgoingValueAssigner ArgAssigner(CC_M88k);
  OutgoingArgHandler Handler(MIRBuilder, MRI, MIB); //, /*IsReturn*/ false);
  if (!determineAndHandleAssignments(Handler, ArgAssigner, OutArgs, MIRBuilder,
                                     Info.CallConv, Info.IsVarArg))
    return false;

  Mask = TRI->getCallPreservedMask(MF, Info.CallConv);
  MIB.addRegMask(Mask);

  // Now we can add the actual call instruction to the correct basic block.
  MIRBuilder.insertInstr(MIB);

  // If Callee is a reg, since it is used by a target specific
  // instruction, it must have a register class matching the
  // constraint of that instruction.
  if (Info.Callee.isReg())
    constrainOperandRegClass(MF, *TRI, MRI, *Subtarget.getInstrInfo(),
                             *Subtarget.getRegBankInfo(), *MIB, MIB->getDesc(),
                             Info.Callee, 0);

  // Finally we can copy the returned value back into its virtual-register. In
  // symmetry with the arguments, the physical register must be an
  // implicit-define of the call instruction.
  if (!Info.OrigRet.Ty->isVoidTy()) {
    OutgoingValueAssigner ArgAssigner(RetCC_M88k);
    CallReturnHandler ReturnedArgHandler(MIRBuilder, MRI, MIB);
    if (!determineAndHandleAssignments(ReturnedArgHandler, ArgAssigner, InArgs,
                                       MIRBuilder, Info.CallConv,
                                       Info.IsVarArg))
      return false;
  }

  MachineFrameInfo &MFI = MF.getFrameInfo();
  const TargetFrameLowering *TFL = MF.getSubtarget().getFrameLowering();
  assert(TFL->hasReservedCallFrame(MF) &&
         "ADJSTACKDOWN and ADJSTACKUP should be no-ops");
  // Set the MaxCallFrameSize value. There is no need to emit the
  // ADJCALLSTACKDOWN/ADJCALLSTACKUP instructions since it serves no further
  // purpose as the call frame is statically reserved in the prolog. Set
  // AdjustsStack as MI is *not* mapped as a frame instruction.
  unsigned AlignedCallFrameSize =
      alignTo(ArgAssigner.StackSize, TFL->getStackAlign());
  if (AlignedCallFrameSize > MFI.getMaxCallFrameSize())
    MFI.setMaxCallFrameSize(AlignedCallFrameSize);
  MFI.setAdjustsStack(true);

  return true;
}
