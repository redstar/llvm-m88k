//===-- M88kInstrFormats.td - M88k Instruction Formats -----*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

class InstM88k<dag outs, dag ins, string asm, string operands,
               list<dag> pattern = []>
  : Instruction {
  bits<32> Inst;

  bits<32> SoftFail = 0; // Needed by disassembler.

  let Namespace = "M88k";
  let Size = 4;

  dag OutOperandList = outs;
  dag InOperandList = ins;
  // Construct the assembler string from template parameters asm and operands.
  // If the instruction has a delay slot, then append ".n" to the mnemonic.
  let AsmString = !if(!eq(operands, ""), asm,
                      !strconcat(asm, " ", operands));
  let Pattern = pattern;

  let DecoderNamespace = "M88k";
}

//===----------------------------------------------------------------------===//
// The formats follow the categories specified in the User Manual.
//===----------------------------------------------------------------------===//

// Category: Logical.
class F_L<dag outs, dag ins, string asm, string operands,
          list<dag> pattern = []>
   : InstM88k<outs, ins, asm, operands, pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
}

// Format: Logical with triadic register.
class F_LR<bits<5> func, bits<1> comp, string asm, list<dag> pattern = []>
   : F_L<(outs GPROpnd:$rd), (ins GPROpnd:$rs1, GPROpnd:$rs2),
         !if(comp, !strconcat(asm, ".c"), asm), "$rd, $rs1, $rs2", pattern> {
  bits<5>  rs2;
  let Inst{31-26} = 0b111101;
  let Inst{15-11} = func;
  let Inst{10}    = comp;
  let Inst{9-5}   = 0b00000;
  let Inst{4-0}   = rs2;
}
