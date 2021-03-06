//===-- M88kISelLowering.cpp - M88k DAG lowering implementation -----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the M88kTargetLowering class.
//
//===----------------------------------------------------------------------===//

#include "M88kISelLowering.h"
#include "M88kTargetMachine.h"

using namespace llvm;

#define DEBUG_TYPE "m88k-lower"

M88kTargetLowering::M88kTargetLowering(const TargetMachine &TM,
                                       const M88kSubtarget &STI)
    : TargetLowering(TM), Subtarget(STI) {
  addRegisterClass(MVT::i32, &M88k::GPRRCRegClass);
  addRegisterClass(MVT::f32, &M88k::GPRRCRegClass);
  addRegisterClass(MVT::f64, &M88k::GPR64RCRegClass);

  // Compute derived properties from the register classes
  computeRegisterProperties(Subtarget.getRegisterInfo());

  // Set up special registers.
  setStackPointerRegisterToSaveRestore(M88k::R31);

  // How we extend i1 boolean values.
  setBooleanContents(ZeroOrOneBooleanContent);

  // Architecture has bit extract instruction.
  setHasExtractBitsInsn();

  setMinFunctionAlignment(Align(4));
  setPrefFunctionAlignment(Align(4));
}

bool M88kTargetLowering::isSelectSupported(SelectSupportKind /*kind*/) const {
  // No kind of select is supported.
  return false;
}

bool M88kTargetLowering::isIndexingLegal(MachineInstr &MI, Register Base,
                                         Register Offset, bool IsPre,
                                         MachineRegisterInfo &MRI) const {
  // Combination 32bit Base+Offset is supported, but preincrement not.
  return !IsPre && MRI.getType(Base).getScalarSizeInBits() == 32 &&
         MRI.getType(Offset).getScalarSizeInBits() == 32;
}

#define GET_REGISTER_MATCHER
#include "M88kGenAsmMatcher.inc"

Register
M88kTargetLowering::getRegisterByName(const char *RegName, LLT Ty,
                                      const MachineFunction &MF) const {
  if (Register Reg = MatchRegisterName(RegName))
    return Reg;
  report_fatal_error(
      Twine("Invalid register name \"" + StringRef(RegName) + "\"."));
}

bool M88kTargetLowering::isConstantUnsignedBitfieldExtractLegal(unsigned Opc,
                                                                LLT Ty1,
                                                                LLT Ty2) const {
  return Ty1 == LLT::scalar(32) && Ty2 == LLT::scalar(32);
}
