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
  let AsmString = !if(!eq(operands, ""),
                     !if(hasDelaySlot, !strconcat(asm, ".n"), asm),
                     !strconcat(!if(hasDelaySlot, !strconcat(asm, ".n"), asm), " ", operands));
  let Pattern = pattern;

  let DecoderNamespace = "M88k";

  // Store the base opcode to enable grouping of instructions.
  // For example, branch instructions with and without a delay slot have the
  // same base opcode.
  // TODO Works currently only for branches/jumps with and without a delay slot.
  string Opcode = asm;
}

class Pseudo<dag outs, dag ins, list<dag> pattern>
  : InstM88k<outs, ins, "", "", pattern> {
  let isCodeGenOnly       = 1;
  let isPseudo            = 1;
  let hasNoSchedulingInfo = 1;
}

//===----------------------------------------------------------------------===//
// Mappings between instructions
//===----------------------------------------------------------------------===//

// Return the version of an instruction with delay slot.
def getOpcodeWithDelaySlot : InstrMapping {
  let FilterClass = "InstM88k";
  let RowFields = ["Opcode"];
  let ColFields = ["hasDelaySlot"];
  let KeyCol = ["0"];
  let ValueCols = [["1"]];
}

// Return the version of an instruction without delay slot.
def getOpcodeWithoutDelaySlot : InstrMapping {
  let FilterClass = "InstM88k";
  let RowFields = ["Opcode"];
  let ColFields = ["hasDelaySlot"];
  let KeyCol = ["0"];
  let ValueCols = [["1"]];
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

// Format: Logical with 16bit immediate.
class F_LI<bits<2> func, bits<1> upper, DAGOperand vt, string asm,
           list<dag> pattern = []>
   : F_L<(outs GPROpnd:$rd), (ins GPROpnd:$rs1, vt:$imm16),
         !if(upper, !strconcat(asm, ".u"), asm),
         "$rd, $rs1, $imm16", pattern> {
  bits<16> imm16;
  let Inst{31-29} = 0b010;
  let Inst{28-27} = func;
  let Inst{26}    = upper;
  let Inst{15-0}  = imm16;
  let isReMaterializable = 1;
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

// Category: Bit-fields.
class F_B<bits<6> func, dag outs, dag ins, string asm, string operands,
          list<dag> pattern = []>
   : F_L<outs, ins, asm, operands, pattern> {
  let Inst{31-27} = 0b11110;
  let Inst{15-10} = func;
}

// Format: Bit-field with triadic register.
class F_BR<bits<6> func, string asm, list<dag> pattern = []>
   : F_B<func, (outs GPROpnd:$rd), (ins GPROpnd:$rs1, GPROpnd:$rs2), asm,
         "$rd, $rs1, $rs2", pattern> {
  bits<5> rs2;
  let Inst{26}  = 0b1;
  let Inst{9-5} = 0b00000;
  let Inst{4-0} = rs2;
}

// Format: Bit-field with dyadic register.
class F_BF<bits<6> func, dag outs, dag ins, string asm, list<dag> pattern =[]>
   : F_B<func, outs, ins, asm, "$rd, $rs2", pattern> {
  bits<5> rs2;
  let rs1 = 0;
  let Inst{26}  = 0b1;
  let Inst{9-5} = 0b00000;
  let Inst{4-0} = rs2;
}

// Format: Bit-field with 10-bit width / offset.
class F_BI<bits<6> func, dag ins, string asm, list<dag> pattern = []>
   : F_B<func, (outs GPROpnd:$rd), ins, asm, "$rd, $rs1, $w5<$o5>", pattern> {
  bits<5> w5;
  bits<5> o5;

  let Inst{26}  = 0b0;
  let Inst{9-5} = w5;
  let Inst{4-0} = o5;
}

// Format: Bit-field with 5-bit offset.
class F_BIOFS<bits<6> func, dag ins, string asm, list<dag> pattern = []>
   : F_B<func, (outs GPROpnd:$rd), ins, asm, "$rd, $rs1, <$o5>", pattern> {
  bits<5> o5;
  let Inst{26}  = 0b0;
  let Inst{9-5} = 0b00000;
  let Inst{4-0} = o5;
}

// Category: Integer.
class F_I<dag outs, dag ins, string asm, string operands, list<dag> pattern = []>
   : InstM88k<outs, ins, asm, operands, pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
}

// Format: Integer with 16bit immediate.
class F_II<bits<6> func, dag ins, string asm, list<dag> pattern = []>
   : F_I<(outs GPROpnd:$rd), ins, asm, "$rd, $rs1, $imm16", pattern> {
  bits<16> imm16;

  let Inst{31-26} = func;
  let Inst{15-0}  = imm16;
}

// Format: Integer with triadic register and carry.
class F_IRC<bits<6> func, bits<1> carryin, bits<1> carryout,
            string asm, list<dag> pattern = []>
   : F_I<(outs GPROpnd:$rd), (ins GPROpnd:$rs1, GPROpnd:$rs2),
         !strconcat(asm, !cond(!not(!or(carryin, carryout)) : "",
                               !and(carryin, !not(carryout)) : ".ci",
                               !and(!not(carryin), carryout) : ".co",
                               !and(carryin, carryout) : ".cio")),
         "$rd, $rs1, $rs2", pattern> {
  bits<5> rs2;

  let Inst{31-26} = 0b111101;
  let Inst{15-10} = func;
  let Inst{9}     = carryin;
  let Inst{8}     = carryout;
  let Inst{7-5}   = 0b000;
  let Inst{4-0}   = rs2;
}

// Format: Integer with triadic register and register pair destination.
class F_IRCD<bits<6> func, RegisterOperand rc1, RegisterOperand rc2,
             string asm, list<dag> pattern = []>
   : F_I<(outs GPR64Opnd:$rd), (ins rc1:$rs1, rc2:$rs2), asm,
         "$rd, $rs1, $rs2", pattern> {
  bits<5> rs2;

  let Inst{31-26} = 0b111101;
  let Inst{15-10} = func;
  let Inst{9}     = 0b0;
  let Inst{8}     = 0b1;
  let Inst{7-5}   = 0b000;
  let Inst{4-0}   = rs2;
}

// Category: Load/Store/Exchange

// Format: Load/Store register indirect with immediate index
class F_LSINDEX<dag outs, dag ins, string asm, list<dag> pattern = []>
   : InstM88k<outs, ins, asm, "$rd, $rs1, $si16", pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  bits<16> si16;

  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
  let Inst{15-0}  = si16;
}

// Format: Load/Store register indirect with immediate index (GRF)
class F_LS<bits<4> func, bits<2> ty,
               dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDEX<outs, ins, asm, pattern> {
  let Inst{31-28} = func;
  let Inst{27-26} = ty;
}

// Format: Load register indirect with immediate index (GRF, unsigned)
class F_LU<bits<1> b,
               dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDEX<outs, ins, asm, pattern> {
  let Inst{31-27} = 0b00001;
  let Inst{26}    = b;
}

// Format: Load register indirect with immediate index (XRF)
class F_LX<bits<6> func,
           dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDEX<outs, ins, asm, pattern> {
  let Inst{31-26} = func;
}

// Format: Load/Store register indirect with scaled or unscaled index
class F_LSINDIRECT<bits<4> func, bits<2> ty, bits<1> scaled, bits<1> user,
                   dag outs, dag ins, string asm, string operands,
                   list<dag> pattern = []>
   : InstM88k<outs, ins, asm, operands, pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  bits<5>  rs2;

  bits<1>  regfile;
  bits<1>  through;

  let Inst{31-27} = 0b11110;
  let Inst{26}    = regfile;
  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
  let Inst{15-12} = func;
  let Inst{11-10} = ty;
  let Inst{9}     = scaled;
  let Inst{8}     = user;
  let Inst{7}     = !if(!eq(func, 0b0001), 0b0, through);
  let Inst{6-5}   = 0b00;
  let Inst{4-0}   = rs2;
}

class F_LSINDUSC<bits<4> func, bits<2> ty, bits<1> user,
                 dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDIRECT<func, ty, /*scaled=*/ 0b0, user, outs, ins, asm,
                  "$rd, $rs1, $rs2", pattern>;

class F_LSINDSC<bits<4> func, bits<2> ty, bits<1> user,
                dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDIRECT<func, ty, /*scaled=*/ 0b1, user, outs, ins, asm,
                  "$rd, $rs1[$rs2]", pattern>;

// Format: Load register indirect with scaled or unscaled index (GRF, unsigned)
class F_LSINDIRECTUNSIGNED<bits<1> ty, bits<1> scaled, bits<1> user,
                           dag outs, dag ins, string asm, string operands,
                          list<dag> pattern = []>
   : InstM88k<outs, ins, asm, operands, pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  bits<5>  rs2;

  let Inst{31-26} = 0b111101;
  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
  let Inst{15-11} = 0b00001;
  let Inst{10}    = ty;
  let Inst{9}     = scaled;
  let Inst{8}     = user;
  let Inst{7-5}   = 0b000;
  let Inst{4-0}   = rs2;
}

class F_LSINDUSCUNS<bits<1> ty, bits<1> user,
                    dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDIRECTUNSIGNED<ty, /*scaled=*/ 0b0, user, outs, ins, asm,
                          "$rd, $rs1, $rs2", pattern>;

class F_LSINDSCUNS<bits<1> ty, bits<1> user,
                   dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDIRECTUNSIGNED<ty, /*scaled=*/ 0b1, user, outs, ins, asm,
                          "$rd, $rs1[$rs2]", pattern>;

class F_XMEMUNS<bits<1> ty, bits<1> user,
             dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDIRECTUNSIGNED<ty, /*scaled=*/ 0b0, user, outs, ins, asm,
                          "$rd, $rs1, $rs2", pattern> {
  let Inst{15-11} = 0b00000;
}

class F_XMEMSC<bits<1> ty, bits<1> user,
               dag outs, dag ins, string asm, list<dag> pattern = []>
   : F_LSINDIRECTUNSIGNED<ty, /*scaled=*/ 0b1, user, outs, ins, asm,
                          "$rd, $rs1[$rs2]", pattern> {
  let Inst{15-11} = 0b00000;
}

class F_XMEMIMM<bits<2> ty, dag outs, dag ins, string asm,
                list<dag> pattern = []>
   : InstM88k<outs, ins, asm, "$rd, $rs1, $imm16", pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  bits<16> imm16;

  let Inst{31-28} = 0b0000;
  let Inst{27-26} = ty;
  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
  let Inst{15-0}  = imm16;
}

// Format: Load/Store register indirect with scaled or unscaled index
class F_LADDR<bits<2> ty, bits<1> scl, dag outs, dag ins, string asm,
              list<dag> pattern = []>
   : InstM88k<outs, ins, asm,
              !if(!eq(scl, 0b0), "$rd, $rs1, $rs2", "$rd, $rs1[$rs2]"),
              pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  bits<5>  rs2;

  let Inst{31-26} = 0b111101;
  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
  let Inst{15-12} = 0b0011;
  let Inst{11-10} = ty;
  let Inst{9}     = scl;
  let Inst{8-5}   = 0b0000;
  let Inst{4-0}   = rs2;
}

// Category: Flow control.

// Format: JMP/JSR
class F_JMP<bits<5> func, string asm, list<dag> pattern = []>
   : InstM88k<(outs), (ins GPROpnd:$rs2), asm, "$rs2", pattern> {
  bits<5> rs2;

  let Inst{31-26} = 0b111101;
  let Inst{25-16} = 0b0000000000;
  let Inst{15-11} = func;
  let Inst{10}    = hasDelaySlot;
  let Inst{9-5}   = 0b00000;
  let Inst{4-0}   = rs2;
}

// Format: BR/BSR
class F_BRANCH<bits<5> func, dag ins, string asm, list<dag> pattern = []>
   : InstM88k<(outs), ins, asm, "$d26", pattern> {
  bits<26> d26;

  let Inst{31-27} = func;
  let Inst{26}    = !if(hasDelaySlot, 1, 0);
  let Inst{25-0}  = d26;
}

// Format: BB0/BB1/BCND
class F_BCOND<bits<5> func, dag outs, dag ins, string asm>
   : InstM88k<outs, ins, asm, "$m5, $rs1, $d16", []> {
  bits<5>  m5;
  bits<5>  rs1;
  bits<16> d16;

  let Inst{31-27} = func;
  let Inst{26}    = !if(hasDelaySlot, 1, 0);
  let Inst{25-21} = m5;
  let Inst{20-16} = rs1;
  let Inst{15-0}  = d16;
}

// Format: TB0/TB1
class F_TB<bits<7> func, dag outs, dag ins, string asm>
   : InstM88k<outs, ins, asm, "$b5, $rs1, $vec9", []> {
  bits<5>  b5;
  bits<5>  rs1;
  bits<9>  vec9;

  let Inst{31-26} = 0b111100;
  let Inst{25-21} = b5;
  let Inst{20-16} = rs1;
  let Inst{15-9}  = func;
  let Inst{8-0}   = vec9;
}

// Format: TCND
class F_TCND<dag outs, dag ins, string asm>
   : InstM88k<outs, ins, asm, "$m5, $rs1, $vec9", []> {
  bits<5>  m5;
  bits<5>  rs1;
  bits<9>  vec9;

  let Inst{31-26} = 0b111100;
  let Inst{25-21} = m5;
  let Inst{20-16} = rs1;
  let Inst{15-9}  = 0b1110100;
  let Inst{8-0}   = vec9;
}

// Format: TBND
class F_TBND<dag outs, dag ins, string asm>
   : InstM88k<outs, ins, asm, "$rs1, $rs2", []> {
  bits<5>  rs1;
  bits<5>  rs2;

  let Inst{31-26} = 0b111101;
  let Inst{25-21} = 0b00000;
  let Inst{20-16} = rs1;
  let Inst{15-5}  = 0b11111000000;
  let Inst{4-0}   = rs2;
}

// Format: TBNDIMM
class F_TBNDIMM<dag outs, dag ins, string asm>
   : InstM88k<outs, ins, asm, "$rs1, $imm16", []> {
  bits<5>  rs1;
  bits<16> imm16;

  let Inst{31-26} = 0b111110;
  let Inst{25-21} = 0b00000;
  let Inst{20-16} = rs1;
  let Inst{15-0}  = imm16;
}

// Format: RTE/ILLOP
class F_RTEILLOP<bits<2> il, string asm>
   : InstM88k<(outs), (ins), asm, "", []> {
  let Inst{31-26} = 0b111101;
  let Inst{25-16} = 0b0000000000;
  let Inst{15-2} = 0b11111100000000;
  let Inst{1-0}   = il;
}

// Category: Floating point/graphics.

// Format: Special function unit.
class F_SFU<dag outs, dag ins, string asm, string operands,
            list<dag> pattern = []>
   : InstM88k<outs, ins, asm, operands, pattern> {
  bits<5>  rd;
  bits<5>  rs1;
  bits<5>  rs2;

  let Inst{31-29} = 0b100;
  let Inst{25-21} = rd;
  let Inst{20-16} = rs1;
  let Inst{4-0} = rs2;
}

// Format: SFU 0 - Control register.
class F_SFU0CR<bits<5> func, dag outs, dag ins, string asm, string operands>
   : F_SFU<outs, ins, asm, operands, []> {

  bits<6>  cr;

  let Inst{28-26} = 0b000;
  let Inst{15-11} = func;
  let Inst{10-5} = cr;
}

class F_SFU0CR2<bits<5> func, dag outs, dag ins, string asm, string operands>
   : F_SFU0CR<func, outs, ins, asm, operands> {
  let rs2 = rs1;
}

// Format: SFU 1 - Floating point instructions.
class F_SFU1<bits<4> func, bits<2> td, bits<2> t1, bits<2> t2,
             dag outs, dag ins, string asm, string operands,
             list<dag> pattern = []>
   : F_SFU<outs, ins, asm, operands, pattern> {
  bits<1>  regfile;

  // All floating point instructions may raise an FP exception.
  let mayRaiseFPException = 1;

  let Inst{28-26} = 0b001;
  let Inst{15} = regfile;
  let Inst{14-11} = func;
  let Inst{10-9} = t1;
  let Inst{8-7} = t2;
  let Inst{6-5} = td;
}

// Format: Triadic register.
class F_SFU1T<bits<4> func, bits<2> td, bits<2> t1, bits<2> t2,
              dag outs, dag ins, string asmstr, list<dag> pattern = []>
   : F_SFU1<func, td, t1, t2, outs, ins, asmstr, "$rd, $rs1, $rs2", pattern> {
}

// Format: Dyadic register.
class F_SFU1D<bits<4> func, bits<2> td, bits<2> t1, bits<2> t2,
              dag outs, dag ins, string asmstr, list<dag> pattern = []>
   : F_SFU1<func, td, t1, t2, outs, ins, asmstr, "$rd, $rs2", pattern> {
  let rs1 = 0b00000;
}

// Format: Dyadic register, for flt.
class F_SFU1FLT<bits<2> td, dag outs, dag ins, string asmstr,
                list<dag> pattern = []>
   : F_SFU<outs, ins, asmstr, "$rd, $rs2", pattern> {
  bits<1>  regfile;

  let rs1 = 0b00000;

  // All floating point instructions may raise an FP exception.
  let mayRaiseFPException = 1;

  let Inst{28-26} = 0b001;
  let Inst{15-10} = 0b001000;
  let Inst{9} = regfile;
  let Inst{8-7} = 0b00;
  let Inst{6-5} = td;
}

// Format: SFU 2 - Graphics instructions.
class F_SFU2<bits<5> func, bits<2> ty,
             dag outs, dag ins, string asm, string operands,
             list<dag> pattern = []>
   : F_SFU<outs, ins, asm, operands, pattern> {
  let Inst{28-26} = 0b010;
  let Inst{15-11} = func;
  let Inst{6-5}   = ty;
}

// Format: Triadic register.
class F_SFU2T<bits<5> func, bits<2> sat, bits<2> ty,
              dag outs, dag ins, string asmstr, list<dag> pattern = []>
   : F_SFU2<func, ty, outs, ins, asmstr, "$rd, $rs1, $rs2", pattern> {
  let Inst{10-9} = 0;
  let Inst{8-7} = sat;
}

// Format: Dyadic register.
class F_SFU2D<bits<5> func, bits<2> sat, bits<2> ty,
              dag outs, dag ins, string asmstr, list<dag> pattern = []>
   : F_SFU2<func, ty, outs, ins, asmstr, "$rd, $rs1", pattern> {
  let rs2 = 0b00000;

  let Inst{10-9} = 0;
  let Inst{8-7} = sat;
}

// Format: Triadic register - ppack.
class F_SFU2PPACK<bits<5> func, bits<4> r, bits<2> ty,
                  dag outs, dag ins, string asmstr, list<dag> pattern = []>
   : F_SFU2<func, ty, outs, ins, asmstr, "$rd, $rs1, $rs2", pattern> {
  let Inst{10-7}  = r;
}

// Format: Dyadic register with 6 bit immediate - prot.
class F_SFU2PROT<bits<5> func, dag outs, dag ins, string asmstr,
                 list<dag> pattern = []>
   : F_SFU2<func, /*ty=*/0b00, outs, ins, asmstr, "$rd, $rs1, $o6", pattern> {
  bits<6> o6;
  let rs2 = 0b00000;
  let Inst{10-7}  = o6{5-2};
}
