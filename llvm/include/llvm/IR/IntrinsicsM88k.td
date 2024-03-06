//===- IntrinsicsM88k.td - Defines m88k intrinsics ---------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines all of the m88k-specific intrinsics.
//
//===----------------------------------------------------------------------===//

let TargetPrefix = "m88k" in {

// Find first set.
def int_m88k_ff1 : Intrinsic<[llvm_i32_ty], [llvm_i32_ty],
                             [IntrNoMem, IntrSpeculatable, IntrWillReturn]>;

// Find first cleared.
def int_m88k_ff0 : Intrinsic<[llvm_i32_ty], [llvm_i32_ty],
                             [IntrNoMem, IntrSpeculatable, IntrWillReturn]>;

}