//===-- M88kRegisterInfo.h - M88k Register Information Impl -----*- C++ -*-===//
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

#ifndef LLVM_LIB_TARGET_M88K_M88KREGISTERINFO_H
#define LLVM_LIB_TARGET_M88K_M88KREGISTERINFO_H

#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/MC/MCRegister.h"
#include <cstdint>

#define GET_REGINFO_HEADER
#include "M88kGenRegisterInfo.inc"

namespace llvm {

struct M88kRegisterInfo : public M88kGenRegisterInfo {
  M88kRegisterInfo();

  bool isArgumentRegister(const MachineFunction &MF,
                          MCRegister Reg) const override;

  const MCPhysReg *getCalleeSavedRegs(const MachineFunction *MF) const override;

  BitVector getReservedRegs(const MachineFunction &MF) const override;

  bool requiresRegisterScavenging(const MachineFunction &MF) const override;

  bool eliminateFrameIndex(MachineBasicBlock::iterator II, int SPAdj,
                           unsigned FIOperandNum,
                           RegScavenger *RS = nullptr) const override;

  Register getFrameRegister(const MachineFunction &MF) const override;

  const uint32_t *getCallPreservedMask(const MachineFunction &MF,
                                       CallingConv::ID CC) const override;

  const TargetRegisterClass *
  getPointerRegClass(const MachineFunction &MF,
                     unsigned Kind = 0) const override;

#if 0
  const uint32_t* getRTCallPreservedMask(CallingConv::ID CC) const;

  bool canRealignStack(const MachineFunction &MF) const override;
#endif
};

} // end namespace llvm

#endif
