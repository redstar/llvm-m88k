//===-- M88kRegisterInfo.cpp - M88k Register Information
//------------------===//
//
// Part of the LLVM Project, under the Apache License
// v2.0 with LLVM Exceptions. See
// https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH
// LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the M88k implementation of the
// TargetRegisterInfo class.
//
//===----------------------------------------------------------------------===//

#include "M88kRegisterInfo.h"
#include "M88kFrameLowering.h"
#include "MCTargetDesc/M88kMCTargetDesc.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/MC/MCRegister.h"

using namespace llvm;

#define GET_REGINFO_TARGET_DESC
#include "M88kGenRegisterInfo.inc"

M88kRegisterInfo::M88kRegisterInfo()
    : M88kGenRegisterInfo(M88k::R1) {}

const MCPhysReg *M88kRegisterInfo::getCalleeSavedRegs(
    const MachineFunction *MF) const {
  return CSR_M88k_SaveList;
}

BitVector M88kRegisterInfo::getReservedRegs(
    const MachineFunction &MF) const {
  BitVector Reserved(getNumRegs());

  // R31 is the stack pointer.
  Reserved.set(M88k::R31);

  return Reserved;
}

bool M88kRegisterInfo::eliminateFrameIndex(
    MachineBasicBlock::iterator MI, int SPAdj,
    unsigned FIOperandNum, RegScavenger *RS) const {
  return false;
}

Register M88kRegisterInfo::getFrameRegister(
    const MachineFunction &MF) const {
  return M88k::R30;
}
