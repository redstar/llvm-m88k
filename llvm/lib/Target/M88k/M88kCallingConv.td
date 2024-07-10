//===-- M88kCallingConv.td - M88k Calling Conventions ------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This describes the calling conventions for the M88k architectures.
// Only the OpenBSD variant is supported.
//
//===----------------------------------------------------------------------===//

// M88k 32-bit ELF C Calling convention.
let Entry = 1 in
def CC_M88k : CallingConv<[
  // Aggregates are passed on the stack.
  CCIfByVal<CCPassByVal<4, 4>>,

  // Promote i8/i16 args to i32.
  CCIfType<[i1, i8, i16], CCPromoteToType<i32>>,

  // Register R12 is used to pass structure return pointer.
  CCIfSRet<CCIfType<[i32], CCAssignToReg<[R12]>>>,

  // Because i64 and f64 values are split into two 32bit values and passed in
  // an even/odd register pairs, we have to handle it with a custom action.
  CCIfType<[i64, f64], CCCustom<"CC_M88k_Custom_64">>,

  // Registers R2 to R9 are used for passing parameters.
  CCIfType<[i32, f32], CCAssignToReg<[R2, R3, R4, R5, R6, R7, R8, R9]>>,

  // Pass 64-bit values aligned on the stack.
  CCIfType<[i64, f64], CCAssignToStack<8, 8>>,

  // Other arguments are passed on the stack, at least 4-byte-aligned.
  CCAssignToStack<4, 4>
]>;

// M88k 32-bit ELF C return-value convention.
let Entry = 1 in
def RetCC_M88k : CallingConv<[
  // 64-bit values are returned in register pair R2:R3.
  CCIfType<[i64, f64], CCCustom<"RetCC_M88k_Custom_64">>,

  // 32-bit values are returned in R2.
  CCIfType<[i32, f32], CCAssignToReg<[R2, R3]>>
]>;

// M88k 32-bit ELF C callee saved registers.
def CSR_M88k : CalleeSavedRegs<(add R1, R30, (sequence "R%d", 25, 14))>;

// X22 to X29 are callee saved registers when targetting MC88110.
def CSR_M88k_MC88110 : CalleeSavedRegs<(add CSR_M88k, (sequence "X%d", 29, 22))>;
