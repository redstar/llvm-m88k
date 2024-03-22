//===- llvm/CodeGen/GlobalISel/BURSInstructionSelector.h --------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file This file declares the API for the BURS instruction selector.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_GLOBALISEL_BURSINSTRUCTIONSELECTOR_H
#define LLVM_CODEGEN_GLOBALISEL_BURSINSTRUCTIONSELECTOR_H

#include <llvm/ADT/DenseMap.h>
#include <cstdint>

namespace llvm {
class BlockFrequencyInfo;
class CodeGenCoverage;
class GISelKnownBits;
class MachineBasicBlock;
class MachineFunction;
class MachineInstr;
class MachineOptimizationRemarkEmitter;
class ProfileSummaryInfo;
class TargetPassConfig;

class BURSInstructionSelector {
  // The mapping of MIs to a state.
  DenseMap<MachineInstr *, uint32_t> States;

public:
  virtual ~BURSInstructionSelector();

  // The tablegen-erated functions.
  virtual void label(MachineInstr &I) = 0;
  virtual bool reduce(MachineInstr &I) = 0;

protected:
  /// A lowering phase that runs before any selection attempts.
  /// Returns true if the instruction was modified.
  virtual bool preISelLower(MachineInstr &I) { return false; }

  /// An early selection function that runs before the reduce() call.
  /// Returns true if the instruction was selected.
  virtual bool earlySelect(MachineInstr &I) { return false; }

  /// Select the (possibly generic) instruction \p I to only use target-specific
  /// opcodes. It is OK to insert multiple instructions, but they cannot be
  /// generic pre-isel instructions.
  ///
  /// \returns whether selection succeeded.
  /// \pre  I.getParent() && I.getParent()->getParent()
  /// \post
  ///   if returns true:
  ///     for I in all mutated/inserted instructions:
  ///       !isPreISelGenericOpcode(I.getOpcode())
  virtual bool select(MachineInstr &I) = 0;

public:
  void setTargetPassConfig(const TargetPassConfig *T) { TPC = T; }

  void setRemarkEmitter(MachineOptimizationRemarkEmitter *M) { MORE = M; }

protected:
  CodeGenCoverage *CoverageInfo = nullptr;
  GISelKnownBits *KB = nullptr;
  MachineFunction *MF = nullptr;
  ProfileSummaryInfo *PSI = nullptr;
  BlockFrequencyInfo *BFI = nullptr;
  // For some predicates, we need to track the current MBB.
  MachineBasicBlock *CurMBB = nullptr;

public:
  virtual void setupGeneratedPerFunctionState(MachineFunction &MF) = 0;

  /// Setup per-MF executor state.
  virtual void setupMF(MachineFunction &MF, GISelKnownBits *KB,
                       CodeGenCoverage *CoverageInfo = nullptr,
                       ProfileSummaryInfo *PSI = nullptr,
                       BlockFrequencyInfo *BFI = nullptr) {
    this->CoverageInfo = CoverageInfo;
    this->KB = KB;
    this->MF = &MF;
    this->PSI = PSI;
    this->BFI = BFI;
    this->CurMBB = nullptr;
    setupGeneratedPerFunctionState(MF);
  }

  void setCurMBB(MachineBasicBlock *CurMBB) {
    this->CurMBB = CurMBB;
    // Clear the recorded states for a new MBB.
    // Cannot give a good default, since MBB.size() is in O(N).
    States.clear();
  }

protected:
  const TargetPassConfig *TPC = nullptr;
  MachineOptimizationRemarkEmitter *MORE = nullptr;
};
} // namespace llvm

#endif
