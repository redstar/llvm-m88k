//===-- M88kMachineFunctionInfo.h - M88k machine function info ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file declares the M88k specific subclass of MachineFunctionInfo.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_M88K_M88KMACHINEFUNCTIONINFO_H
#define LLVM_LIB_TARGET_M88K_M88KMACHINEFUNCTIONINFO_H

#include "llvm/CodeGen/MachineFunction.h"

namespace llvm {

class M88kMachineFunctionInfo : public MachineFunctionInfo {
  virtual void anchor();

  /// FramePointerIndex - Frame index of where the old frame pointer is
  /// stored.
  int FramePointerIndex = 0;

public:
  M88kMachineFunctionInfo(const Function &F, const TargetSubtargetInfo *STI) {}

  MachineFunctionInfo *
  clone(BumpPtrAllocator &Allocator, MachineFunction &DestMF,
        const DenseMap<MachineBasicBlock *, MachineBasicBlock *> &Src2DstMBB)
      const override;

  int getFramePointerIndex() const { return FramePointerIndex; }
  void setFramePointerIndex(int Idx) { FramePointerIndex = Idx; }
};
} // end namespace llvm

#endif
