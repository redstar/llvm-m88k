//===-- M88kMachineFunctionInfo.cpp - M88k machine function info ----------===//
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

#include "M88kMachineFunctionInfo.h"

using namespace llvm;

// Pin vtable to this file.
void M88kMachineFunctionInfo::anchor() {}

MachineFunctionInfo *M88kMachineFunctionInfo::clone(
    BumpPtrAllocator &Allocator, MachineFunction &DestMF,
    const DenseMap<MachineBasicBlock *, MachineBasicBlock *> &Src2DstMBB)
    const {
  return DestMF.cloneInfo<M88kMachineFunctionInfo>(*this);
}
