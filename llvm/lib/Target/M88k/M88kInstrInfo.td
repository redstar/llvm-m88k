//===-- M88kInstrInfo.td - M88k Instructions ---------------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file describes the M88k instructions in TableGen format.
//
//===----------------------------------------------------------------------===//

// ---------------------------------------------------------------------------//
// Logic and bit field instructions.
// ---------------------------------------------------------------------------//

// Multiclass for logical instructions with triadic registers.
multiclass Logic<bits<5> Func, string OpcStr, SDNode OpNode> {
  let isCommutable = 1 in
    def rr : F_LR<Func, /*comp=*/0b0, OpcStr,
                  [(set i32:$rd, (OpNode GPROpnd:$rs1, GPROpnd:$rs2))]>;
  def rrc : F_LR<Func, /*comp=*/0b1, OpcStr,
                 [(set i32:$rd, (OpNode GPROpnd:$rs1, (not GPROpnd:$rs2)))]>;
}

defm AND : Logic<0b01000, "and", and>;
defm XOR : Logic<0b01010, "xor", xor>;
defm OR  : Logic<0b01011, "or", or>;
