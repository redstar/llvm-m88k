//== llvm/CodeGen/GlobalISel/BURSInstructionSelect.h -------------*- C++ -*-==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file This file describes the interface of the MachineFunctionPass
/// responsible for selecting (possibly generic) machine instructions to
/// target-specific instructions.
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_GLOBALISEL_BURSINSTRUCTIONSELECT_H
#define LLVM_CODEGEN_GLOBALISEL_BURSINSTRUCTIONSELECT_H

#include "llvm/ADT/StringRef.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/Support/CodeGen.h"

namespace llvm {

class BlockFrequencyInfo;
class ProfileSummaryInfo;

/// This pass is responsible for selecting generic machine instructions to
/// target-specific instructions.  It relies on the InstructionSelector provided
/// by the target.
/// Selection is done by examining blocks in post-order, and instructions are
/// first labelled in normal order, and then reduced in reverse order.
///
/// \post for all inst in MF: not isPreISelGenericOpcode(inst.opcode)
class BURSInstructionSelect : public MachineFunctionPass {
public:
  static char ID;
  StringRef getPassName() const override { return "BURSInstructionSelect"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override;

  MachineFunctionProperties getRequiredProperties() const override {
    return MachineFunctionProperties()
        .set(MachineFunctionProperties::Property::IsSSA)
        .set(MachineFunctionProperties::Property::Legalized)
        .set(MachineFunctionProperties::Property::RegBankSelected);
  }

  MachineFunctionProperties getSetProperties() const override {
    return MachineFunctionProperties().set(
        MachineFunctionProperties::Property::Selected);
  }

  BURSInstructionSelect(CodeGenOptLevel OL);
  BURSInstructionSelect();

  bool runOnMachineFunction(MachineFunction &MF) override;

protected:
  BlockFrequencyInfo *BFI = nullptr;
  ProfileSummaryInfo *PSI = nullptr;

  CodeGenOptLevel OptLevel = CodeGenOptLevel::None;
};
} // End namespace llvm.

#endif
