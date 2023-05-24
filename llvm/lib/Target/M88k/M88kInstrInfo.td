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


def Graphics   : Predicate<"Subtarget->hasGraphics()">;
def MC88110    : Predicate<"Subtarget->isMC88110()">,
                           AssemblerPredicate<(all_of Proc88110), "MC88110">;
def NotMC88110 : Predicate<"!Subtarget->isMC88110()">,
                           AssemblerPredicate<(all_of (not Proc88110)), "!MC88110">;

// ---------------------------------------------------------------------------//
// Selection DAG Nodes.
// ---------------------------------------------------------------------------//

// Selection DAG types.

// These are target-independent nodes, but have target-specific formats.
def SDT_CallSeqStart : SDCallSeqStart<[SDTCisVT<0, i32>, SDTCisVT<1, i32>]>;
def SDT_CallSeqEnd   : SDCallSeqEnd<[SDTCisVT<0, i32>, SDTCisVT<1, i32>]>;
def SDT_Call         : SDTypeProfile<0, -1, [SDTCisPtrTy<0>]>;

// Selection DAG nodes.

def call             : SDNode<"M88kISD::CALL", SDT_Call,
                              [SDNPHasChain, SDNPOptInGlue, SDNPOutGlue,
                              SDNPVariadic]>;
def retflag          : SDNode<"M88kISD::RET_FLAG", SDTNone,
                              [SDNPHasChain, SDNPOptInGlue, SDNPVariadic]>;
def callseq_start : SDNode<"ISD::CALLSEQ_START", SDT_CallSeqStart,
                                [SDNPHasChain, SDNPOutGlue]>;
def callseq_end   : SDNode<"ISD::CALLSEQ_END", SDT_CallSeqEnd,
                                [SDNPHasChain, SDNPOptInGlue, SDNPOutGlue]>;

// Hi16 and Lo16 nodes are used to handle global addresses.
def m88k_hi : SDNode<"M88kISD::Hi16", SDTIntUnaryOp>;
def m88k_lo : SDNode<"M88kISD::Lo16", SDTIntUnaryOp>;

// ---------------------------------------------------------------------------//
// Operands.
// ---------------------------------------------------------------------------//

class ImmediateAsmOperand<string name> : AsmOperandClass {
  let Name = name;
  let RenderMethod = "addImmOperands";
}

class ImmediateOp<ValueType vt, string asmop> : Operand<vt> {
  let PrintMethod = "print"#asmop#"Operand";
  let DecoderMethod = "decode"#asmop#"Operand";
  let ParserMatchClass = !cast<AsmOperandClass>(asmop);
  let OperandType = "OPERAND_IMMEDIATE";
}

class ImmOpWithPattern<ValueType vt, string asmop, code pred, SDNodeXForm xform> :
  ImmediateOp<vt, asmop>, IntImmLeaf<vt, pred, xform>;

multiclass Immediate<ValueType vt, code pred, SDNodeXForm xform, string asmop> {
  def "" : ImmOpWithPattern<vt, asmop, pred, xform>;

//  def _timm : ImmOpWithPattern<vt, asmop, pred, xform, timm>;
}


// Constructs an asm operand for a PC-relative address.  SIZE says how
// many bits there are.
class PCRelAsmOperand<string size> : ImmediateAsmOperand<"PCRel"#size> {
  let PredicateMethod = "isImm";
  let ParserMethod = "parsePCRel"#size;
}

// Constructs an operand for a PC-relative address with address type VT.
// ASMOP is the associated asm operand.
class PCRelOperand<ValueType vt, AsmOperandClass asmop> : Operand<vt> {
  let PrintMethod = "printPCRelOperand";
  let ParserMatchClass = asmop;
  let OperandType = "OPERAND_PCREL";
}

// Signed and unsigned operands.
def U5Imm : ImmediateAsmOperand<"U5Imm">;
def S16Imm : ImmediateAsmOperand<"S16Imm">;
def U16Imm : ImmediateAsmOperand<"U16Imm">;
def Vec9 : ImmediateAsmOperand<"Vec9">, ImmediateOp<i32, "Vec9">;

// Bitfield width operand.
def BFWidth : AsmOperandClass {
  let Name = "BFWidth";
  let RenderMethod = "addBFWidthOperands";
  let ParserMethod = "parseBFWidth";
  let DiagnosticString = "operand must between 0 and 31";
  let DiagnosticType = "InvalidBitfieldWidth";
}
def bfwidth : ImmOpWithPattern<i32, "BFWidth", [{
  return isUInt<5>(Imm.getZExtValue());
}], NOOP_SDNodeXForm> {
  let PrintMethod = "printBFWidthOperand";
  let DecoderMethod = "decodeBFWidthOperand";
  let OperandNamespace = "M88kOp";
  let OperandType = "OPERAND_BFWIDTH";
}

// Bitfield offset operand.
def BFOffset : AsmOperandClass {
  let Name = "BFOffset";
  let RenderMethod = "addBFOffsetOperands";
  let ParserMethod = "parseBFOffset";
  let DiagnosticString = "operand must between 0 and 31";
  let DiagnosticType = "InvalidBitfieldOffset";
}
def bfoffset : ImmOpWithPattern<i32, "BFOffset", [{
  return isUInt<5>(Imm.getZExtValue());
}], NOOP_SDNodeXForm> {
  let PrintMethod = "printBFOffsetOperand";
  let DecoderMethod = "decodeBFOffsetOperand";
  let OperandNamespace = "M88kOp";
  let OperandType = "OPERAND_BFOFFSET";
}

// Pixel rotation size operand.
def PixelRot : AsmOperandClass {
  let Name = "PixelRot";
  let RenderMethod = "addPixelRotOperands";
  let ParserMethod = "parsePixelRot";
  let DiagnosticString = "operand must be a multiple of 4 between 0 and 60";
  let DiagnosticType = "InvalidPixelRotationSize";
}
def pixelrot : ImmOpWithPattern<i32, "PixelRot", [{
  return isUInt<6>(Imm.getZExtValue());
}], NOOP_SDNodeXForm> {
  let PrintMethod = "printPixelRotOperand";
  let DecoderMethod = "decodePixelRotOperand";
  let OperandNamespace = "M88kOp";
  let OperandType = "OPERAND_PIXELROTATE";
}

// Condition code operands.
def CCode : AsmOperandClass {
  let Name = "CCode";
  let RenderMethod = "addConditionCodeOperands";
  let ParserMethod = "parseConditionCode";
}
def ccode : ImmediateOp<i8, "CCode"> {
  let OperandNamespace = "M88kOp";
  let OperandType = "OPERAND_CONDITION_CODE";
}

// PC-relative asm operands.
def PCRel16 : PCRelAsmOperand<"16">;
def PCRel26 : PCRelAsmOperand<"26">;

// PC-relative offsets of a basic block.  The offset is sign-extended
// and shifted left by 2 bits.
def brtarget16 : PCRelOperand<OtherVT, PCRel16> {
  let EncoderMethod = "getPC16Encoding";
  let DecoderMethod = "decodePC16BranchOperand";
}

def brtarget26 : PCRelOperand<OtherVT, PCRel26> {
  let EncoderMethod = "getPC26Encoding";
  let DecoderMethod = "decodePC26BranchOperand";
}

// Extracting immediate operands from nodes.
// Bits 0-15.
def LO16 : SDNodeXForm<imm, [{
  uint32_t Value = N->getZExtValue() & 0x000000000000FFFFULL;
  return CurDAG->getTargetConstant(Value, SDLoc(N), MVT::i32);
}]>;

def gi_LO16 : GICustomOperandRenderer<"renderLO16">, GISDNodeXFormEquiv<LO16>;

// Bits 16-31 (counting from the lsb).
def HI16 : SDNodeXForm<imm, [{
  uint64_t Value = (N->getZExtValue() & 0x00000000FFFF0000ULL) >> 16;
  return CurDAG->getTargetConstant(Value, SDLoc(N), MVT::i32);
}]>;

def gi_HI16 : GICustomOperandRenderer<"renderHI16">, GISDNodeXFormEquiv<HI16>;

// Negate a 16 bit immediate.
def NEG16 : SDNodeXForm<imm, [{
  int64_t Value = N->getSExtValue();
  return CurDAG->getTargetConstant(-Value, SDLoc(N), MVT::i16);
}]>;

def gi_NEG16 : GICustomOperandRenderer<"renderNEG16">,
                                       GISDNodeXFormEquiv<NEG16>;

// Count population modulo 32.
def CPOP : SDNodeXForm<imm, [{
  uint64_t Val = countPopulation(Imm.getZExtValue()) & 0x1f;
  return CurDAG->getTargetConstant(Val, SDLoc(N), MVT::i8);
}]>;
def : GICustomOperandRenderer<"renderCPOP">, GISDNodeXFormEquiv<CPOP>;

// Count traling zeroes modulo 32.
def CTZ : SDNodeXForm<imm, [{
  uint64_t Val = countr_zero(Imm.getZExtValue()) & 0x1f;
  return CurDAG->getTargetConstant(Val, SDLoc(N), MVT::i8);
}]>;
def : GICustomOperandRenderer<"renderCTZ">, GISDNodeXFormEquiv<CTZ>;

// Count population modulo 32 on inverted (1-complement) 32 bit value.
def CPOPINV : SDNodeXForm<imm, [{
  uint64_t Val = countPopulation(~Imm.getZExtValue() & 0xffffffff) & 0x1f;
  return CurDAG->getTargetConstant(Val, SDLoc(N), MVT::i8);
}]>;
def : GICustomOperandRenderer<"renderCPOPINV">, GISDNodeXFormEquiv<CPOPINV>;

// Count traling zeroes modulo 32 on inverted (1-complement) 32 bit value.
def CTZINV : SDNodeXForm<imm, [{
  uint64_t Val = countr_zero(~Imm.getZExtValue() & 0xffffffff) & 0x1f;
  return CurDAG->getTargetConstant(Val, SDLoc(N), MVT::i8);
}]>;
def : GICustomOperandRenderer<"renderCTZINV">, GISDNodeXFormEquiv<CTZINV>;


// Immediates for the lower and upper 16 bits of an i32, with the other
// bits of the i32 being zero.
defm imm32lo16 : Immediate<i32, [{
  return (Imm.getZExtValue() & ~0x000000000000ffffULL) == 0;
}], LO16, "U16Imm">;

defm imm32hi16 : Immediate<i32, [{
  return (Imm.getZExtValue() & ~0x00000000ffff0000ULL) == 0;
}], HI16, "U16Imm">;

// Immediates for the lower and upper 16 bits of an i32, with the other
// bits of the i32 being one.
defm imm32lo16c : Immediate<i32, [{
  uint64_t Val = Imm.getZExtValue();
  return (uint32_t(~Val) & ~0x000000000000ffffULL) == 0;
}], LO16, "U16Imm">;

defm imm32hi16c : Immediate<i32, [{
  return (uint32_t(~Imm.getZExtValue()) & ~0x00000000ffff0000ULL) == 0;
}], HI16, "U16Imm">;

defm imm32zx5 : Immediate<i32, [{
  return (Imm.getZExtValue() & ~0x000000000000001fULL) == 0;
}], NOOP_SDNodeXForm, "U5Imm">;

defm uimm16 : Immediate<i32, [{
  return isUInt<16>(Imm.getZExtValue());
}], NOOP_SDNodeXForm, "U16Imm">;

// Predicate: Arbitrary 32 bit value.
def uimm32 : IntImmLeaf<i32, [{
  uint64_t Val = Imm.getZExtValue();
  return isUInt<32>(Val);
}]>;

// Predicate: Negative 16 bit value.
def simm16Neg : IntImmLeaf<i32, [{
  int64_t Val = Imm.getSExtValue();
  return Val < 0 && Val > -65536;
}]>;

// Predicate: Mask.
def mask32 : IntImmLeaf<i32, [{
  uint64_t Val = Imm.getZExtValue();
  return isUInt<32>(Val) && isShiftedMask_64(Val)
         && countr_zero(Val) == 0;
}]>;

// Predicate: Shifted mask.
def shmask32 : IntImmLeaf<i32, [{
  uint64_t Val = Imm.getZExtValue();
  return isUInt<32>(Val) && isShiftedMask_64(Val);
}]>;

// Predicate: Inverted (1-complement) shifted mask.
def invshmask32 : IntImmLeaf<i32, [{
  uint64_t Val = Imm.getZExtValue();
  return isUInt<32>(Val) && isShiftedMask_64(~Val & 0xffffffff);
}]>;

// ---------------------------------------------------------------------------//
// Pseudo instructions.
// ---------------------------------------------------------------------------//
let hasSideEffects = 1 in {
def ADJCALLSTACKDOWN : Pseudo<(outs), (ins i32imm:$amt1, i32imm:$amt2),
                              [(callseq_start timm:$amt1, timm:$amt2)]>;
def ADJCALLSTACKUP : Pseudo<(outs), (ins i32imm:$amt1, i32imm:$amt2),
                            [(callseq_end timm:$amt1, timm:$amt2)]>;
}

// ---------------------------------------------------------------------------//
// Generic patterns.
// ---------------------------------------------------------------------------//

multiclass BinaryOpPat<string Inst, SDPatternOperator OpNode> {
  def : Pat<(OpNode GPR:$rs1, GPR:$rs2),
            (!cast<InstM88k>(Inst#"rr") GPR:$rs1, GPR:$rs2)>;
  def : Pat<(OpNode GPR:$rs1, uimm16:$imm16),
            (!cast<InstM88k>(Inst#"ri") GPR:$rs1, uimm16:$imm16)>;
}

class UnaryOpPat<InstM88k Inst, SDPatternOperator OpNode>
  : Pat<(OpNode GPR:$rs1), (Inst GPR:$rs1)>;

// ---------------------------------------------------------------------------//
// Logic and bit field instructions.
// ---------------------------------------------------------------------------//

// Multiclass for logical instructions with immediates.
// The pattern for "and" is slightly different.
multiclass LogicImm<bits<2> FuncI, string OpcStr, SDNode OpNode> {
  defvar OPLO = !if(!eq(OpcStr, "and"), imm32lo16c, imm32lo16);
  defvar OPHI = !if(!eq(OpcStr, "and"), imm32hi16c, imm32hi16);

  def ri  : F_LI<FuncI, /*upper=*/0b0, OPLO, OpcStr,
                 [(set i32:$rd, (OpNode GPR:$rs1, OPLO:$imm16))]>;
  def riu : F_LI<FuncI, /*upper=*/0b1, OPHI, OpcStr,
                 [(set i32:$rd, (OpNode GPR:$rs1, OPHI:$imm16))]>;
}

// Multiclass for logical instructions with triadic registers or immediates.
multiclass Logic<bits<5> FuncR, bits<2> FuncI, string OpcStr, SDNode OpNode>
  : LogicImm<FuncI, OpcStr, OpNode> {
  let isCommutable = 1 in
    def rr : F_LR<FuncR, /*comp=*/0b0, OpcStr,
                  [(set i32:$rd, (OpNode GPR:$rs1, GPR:$rs2))]>;
  def rrc : F_LR<FuncR, /*comp=*/0b1, OpcStr,
                 [(set i32:$rd, (OpNode GPR:$rs1, (not GPR:$rs2)))]>;
}

defm MASK : LogicImm<0b01, "mask", and>;
defm AND : Logic<0b01000, 0b00, "and", and>;
defm XOR : Logic<0b01010, 0b10, "xor", xor>;
defm OR  : Logic<0b01011, 0b11, "or", or>;

// Multiclass for bit-field instructions with triadic registers or immediates.
multiclass Bitfield<bits<6> Func, string OpcStr> {
  def rr  : F_BR<Func, OpcStr>;
  if !eq(OpcStr, "rot") then {
    def rwo : F_BIOFS<Func, (ins GPR:$rs1, bfoffset:$o5), OpcStr>;
  } else {
    def rwo : F_BI<Func, (ins GPR:$rs1, bfwidth:$w5, bfoffset:$o5), OpcStr>;
  }
}

defm CLR  : Bitfield<0b100000, "clr">;
defm SET  : Bitfield<0b100010, "set">;
defm EXT  : Bitfield<0b100100, "ext">;
defm EXTU : Bitfield<0b100110, "extu">;
defm MAK  : Bitfield<0b101000, "mak">;
defm ROT  : Bitfield<0b101010, "rot">;

// Pattern for shifts
def : Pat<(sra GPR:$rs1, GPR:$rs2), (EXTrr GPR:$rs1, GPR:$rs2)>;
def : Pat<(srl GPR:$rs1, GPR:$rs2), (EXTUrr GPR:$rs1, GPR:$rs2)>;
def : Pat<(shl GPR:$rs1, GPR:$rs2), (MAKrr GPR:$rs1, GPR:$rs2)>;
def : Pat<(rotr GPR:$rs1, GPR:$rs2), (ROTrr GPR:$rs1, GPR:$rs2)>;
def : Pat<(sra GPR:$rs1, bfoffset:$o5), (EXTrwo GPR:$rs1, 0, bfoffset:$o5)>;
def : Pat<(srl GPR:$rs1, bfoffset:$o5), (EXTUrwo GPR:$rs1, 0, bfoffset:$o5)>;
def : Pat<(shl GPR:$rs1, bfoffset:$o5), (MAKrwo GPR:$rs1, 0, bfoffset:$o5)>;
def : Pat<(rotr GPR:$rs1, bfoffset:$o5), (ROTrwo GPR:$rs1, bfoffset:$o5)>;

class FindBF<bits<6> Func, string OpcStr> :
  F_BF<Func, (outs GPR:$rd), (ins GPR:$rs2), OpcStr>;

def FF1r : FindBF<0b111010, "ff1">;
def FF0r : FindBF<0b111011, "ff0">;

// ctlz = ff1 ^ 0x1f
// This inverts the lower 5 bits, returning the required range.
def : Pat<(ctlz GPR:$rs), (XORri (FF1r GPR:$rs), 31)>;

// ctlz_zero_undef is similar.
// But since 0 is poison some simple patterns allow for better code.
def : Pat<(sub 31, (ctlz_zero_undef GPR:$rs)), (FF1r GPR:$rs)>;
def : Pat<(xor (ctlz_zero_undef GPR:$rs), 31), (FF1r GPR:$rs)>;
def : Pat<(ctlz_zero_undef GPR:$rs), (XORri (FF1r GPR:$rs), 31)>;

// ---------------------------------------------------------------------------//
// Integer arithmetic instructions.
// ---------------------------------------------------------------------------//

// Multiclass for arithmetic instructions with triadic registers or immediates.
multiclass ArithTri<bits<6> Func, string OpcStr, bit IsReMat = 0> {
  def rr : F_IRC<Func, /*carryin=*/0b0, /*carryout=*/0b0, OpcStr>;
  let isReMaterializable = IsReMat in
    def ri : F_II<Func, (ins GPR:$rs1, uimm16:$imm16), OpcStr>;
}

// Multiclass for arithmetic instructions with triadic registers or immediates,
// and carry setting or using variants.
multiclass ArithTriCarry<bits<6> Func, string OpcStr, bit IsReMat = 0>
  : ArithTri<Func, OpcStr, IsReMat> {
  let Uses = [CARRY] in
    def rrci  : F_IRC<Func, /*carryin=*/0b1, /*carryout=*/0b0, OpcStr>;
  let Defs = [CARRY] in
    def rrco  : F_IRC<Func, /*carryin=*/0b0, /*carryout=*/0b1, OpcStr>;
  let Uses = [CARRY], Defs = [CARRY] in
    def rrcio : F_IRC<Func, /*carryin=*/0b1, /*carryout=*/0b1, OpcStr>;
}

let isCommutable = 1 in {
  let isAdd = 1 in {
    defm ADDU : ArithTriCarry<0b011000, "addu", 1>;
    defm ADD : ArithTriCarry<0b011100, "add", 1>;
  }
  defm MULU : ArithTri<0b011011, "mulu">;
}
defm SUBU : ArithTriCarry<0b011001, "subu", 1>;
defm SUB : ArithTriCarry<0b011101, "sub", 1>;
defm DIVU : ArithTri<0b011010, "divu">;
defm DIVS : ArithTri<0b011110, "divs">;
let isCompare = 1 in
  defm CMP : ArithTri<0b011111, "cmp">;

let Predicates = [MC88110] in {
  def DIVUrrd : F_IRCD<0b011010, GPR64, GPR, "divu.d">;
  let isCommutable = 1 in
    def MULUrrd : F_IRCD<0b011011, GPR, GPR, "mulu.d">;
}

// TODO Aliases div -> divs, mul -> mulu. Renames from 88100
defm : BinaryOpPat<"ADDU", add>;
defm : BinaryOpPat<"SUBU", sub>;
defm : BinaryOpPat<"MULU", mul>;
defm : BinaryOpPat<"DIVU", udiv>;
defm : BinaryOpPat<"DIVS", sdiv>;
//def : Pat<(umullohi GPR:$rs1, GPR:$rs2), (MULUrrd GPR:$rs1, GPR:$rs2)>;
def : Pat<(ineg GPR:$rs2), (SUBUrr (i32 R0), GPR:$rs2)>;

// ---------------------------------------------------------------------------//
// Integer compare.
// ---------------------------------------------------------------------------//

multiclass SetCCPat<CondCode CC, bits<5> w5, bits<5> o5> {
  def : Pat<(setcc (i32 GPR:$lhs), (i32 GPR:$rhs), CC),
            (EXTUrwo (CMPrr GPR:$lhs, GPR:$rhs), w5, o5)>;
  def : Pat<(setcc (i32 GPR:$lhs), uimm16:$rhs, CC),
            (EXTUrwo (CMPrr GPR:$lhs, uimm16:$rhs), w5, o5)>;
}

defm : SetCCPat<SETEQ, 1, 2>;
defm : SetCCPat<SETNE, 1, 3>;
defm : SetCCPat<SETGT, 1, 4>;
defm : SetCCPat<SETLE, 1, 5>;
defm : SetCCPat<SETLT, 1, 6>;
defm : SetCCPat<SETGE, 1, 7>;
defm : SetCCPat<SETUGT, 1, 8>;
defm : SetCCPat<SETULE, 1, 8>;
defm : SetCCPat<SETULT, 1, 10>;
defm : SetCCPat<SETUGE, 1, 11>;

// ---------------------------------------------------------------------------//
// Materialize immediates & constants.
// ---------------------------------------------------------------------------//

// Match G_SHL $dst, (G_AND $src, (2**width - 1)), offset
// Lower to MAKrwo $dst, $src, width<offset>
def : Pat<(shl (and GPR:$rs1, mask32:$imm), bfoffset:$ofs),
          (MAKrwo GPR:$rs1, (CPOP $imm), bfoffset:$ofs)>;

// Pattern for logial operations with shifted masks.
def : Pat<(or GPR:$rs1, shmask32:$imm),
          (SETrwo GPR:$rs1, (CPOP $imm), (CTZ $imm))>;
def : Pat<(and GPR:$rs1, invshmask32:$imm),
          (CLRrwo GPR:$rs1, (CPOPINV $imm), (CTZINV $imm))>;

// Pattern for logial operations with 32 bit constants.
def : Pat<(and GPR:$rs1, uimm32:$imm),
          (ANDri (ANDriu GPR:$rs1, (HI16 i32:$imm)), (LO16 i32:$imm))>;
def : Pat<(or GPR:$rs1, uimm32:$imm),
          (ORri (ORriu GPR:$rs1, (HI16 i32:$imm)), (LO16 i32:$imm))>;
def : Pat<(xor GPR:$rs1, uimm32:$imm),
          (XORri (XORriu GPR:$rs1, (HI16 i32:$imm)), (LO16 i32:$imm))>;

// Zero constant.
def : Pat<(i32 0), (ORri (i32 R0), 0)>;

// Constant -65536 aka 4294901760 = 0xffff0000.
def : Pat<(i32 4294901760), (SETrwo (i32 R0), 16, 16)>;

// Constants < 0 and > -65536
def : Pat<(i32 simm16Neg:$imm), (SUBUri (i32 R0), (NEG16 i32:$imm))>;

// 16-bit constants.
def : Pat<(i32 imm32lo16:$imm), (ORri (i32 R0), (LO16 i32:$imm))>;
def : Pat<(i32 imm32hi16:$imm), (ORriu (i32 R0), (HI16 i32:$imm))>;

// 32-bit constants.
def : Pat<(i32 imm:$imm),
          (ORri (ORriu (i32 R0), (HI16 i32:$imm)), (LO16 i32:$imm))>;

// ---------------------------------------------------------------------------//
// Load & Store.
// ---------------------------------------------------------------------------//

// Complex pattern which also declare the GI complex operand.
multiclass ComplexPatternWithGIEquiv<ValueType vty, LLT sty, int numops,
                                     string fn,
                                     list<SDNode> roots = [],
                                     list<SDNodeProperty> props = [],
                                     int complexity = -1> {
  def "" : ComplexPattern<vty, numops, fn, roots, props, complexity>;
  def : GIComplexOperandMatcher<sty, fn>,
        GIComplexPatternEquiv<!cast<ComplexPattern>(NAME)>;
}

/*
Addressing modes:
Register indirect with immediate index: ld rD, rS1, si16
Register indirect with index:           ld rD, rS1, rS2
Register indirect with scaled index:    ld rD, rS1, [rS2]
*/
defm ADDRri : ComplexPatternWithGIEquiv<i32, s32, 2, "selectAddrRegImm", [], [], 10>;
defm ADDRrr : ComplexPatternWithGIEquiv<i32, s32, 2, "selectAddrRegReg", [], []>;
defm ADDRrs1 : ComplexPatternWithGIEquiv<i32, s32, 2, "selectAddrRegScaled<1>", [], [], 15>;
defm ADDRrs2 : ComplexPatternWithGIEquiv<i32, s32, 2, "selectAddrRegScaled<2>", [], [], 15>;
defm ADDRrs4 : ComplexPatternWithGIEquiv<i32, s32, 2, "selectAddrRegScaled<4>", [], [], 15>;
defm ADDRrs8 : ComplexPatternWithGIEquiv<i32, s32, 2, "selectAddrRegScaled<8>", [], [], 15>;
defm ADDRrs16 : ComplexPatternWithGIEquiv<i32, s32, 2, "selectAddrRegScaled<16>", [], [], 15>;

// Instruction formats with semantics.
class FLoadIndexImm<bits<4> func, bits<2> ty, string option,
                    RegisterOperand cls, ValueType vt,
                    SDPatternOperator operator>
  : F_LS<func, ty, (outs cls:$rd), (ins GPR:$rs1, uimm16:$si16),
         !if(!eq(option,""), "ld", !strconcat("ld.", option)),
         [(set (vt cls:$rd), (operator (ADDRri (i32 GPR:$rs1), uimm16:$si16)))]> {}

class FStoreIndexImm<bits<4> func, bits<2> ty, string option,
                     RegisterOperand cls, ValueType vt,
                     SDPatternOperator operator>
  : F_LS<func, ty, (outs), (ins cls:$rd, GPR:$rs1, uimm16:$si16),
         !if(!eq(option,""), "st", !strconcat("st.", option)),
         [(operator (vt cls:$rd), (ADDRri (i32 GPR:$rs1), uimm16:$si16))]> {}

// Multiclass for load and store instructions.
multiclass LoadIndexImm {
  defvar Func = 0b0001;
  def riw  : FLoadIndexImm<Func, /*ty=*/ 0b01, "", GPR, i32, load>;
  def rib  : FLoadIndexImm<Func, /*ty=*/ 0b11, "b", GPR, i32, sextloadi8>;
  def rih  : FLoadIndexImm<Func, /*ty=*/ 0b10, "h", GPR, i32, sextloadi16>;
  def rid  : FLoadIndexImm<Func, /*ty=*/ 0b00, "d", GPR64, i64, load>;
  let Predicates = [MC88110], DecoderNamespace = "MC88110" in {
    def xi  : FLoadIndexImm<0b0000, /*ty=*/ 0b01, "", XR, f32, load>;
    def xid  : FLoadIndexImm<0b0000, /*ty=*/ 0b00, "d", XR, f64, load>;
    def xix  : FLoadIndexImm<0b0011, /*ty=*/ 0b11, "x", XR, f80, load>;
  }
}

multiclass StoreIndexImm {
  defvar FuncG = 0b0010;
  def riw  : FStoreIndexImm<FuncG, /*ty=*/ 0b01, "", GPR, i32, store>;
  def rib  : FStoreIndexImm<FuncG, /*ty=*/ 0b11, "b", GPR, i32, truncstorei8>;
  def rih  : FStoreIndexImm<FuncG, /*ty=*/ 0b10, "h", GPR, i32, truncstorei16>;
  def rid  : FStoreIndexImm<FuncG, /*ty=*/ 0b00, "d", GPR64, i64, store>;
  let Predicates = [MC88110], DecoderNamespace = "MC88110" in {
    defvar FuncX = 0b0011;
    def xis  : FStoreIndexImm<FuncX, /*ty=*/ 0b01, "", XR, f32, store>;
    def xid  : FStoreIndexImm<FuncX, /*ty=*/ 0b00, "d", XR, f64, store>;
    def xix  : FStoreIndexImm<FuncX, /*ty=*/ 0b10, "x", XR, f80, store>;
  }
}

multiclass FLoadUnsigned<bits<1> ty, string option, RegisterOperand cls,
                         ValueType vt, SDPatternOperator operator,
                         ComplexPattern addr> {
  def u # option : F_LSINDUSCUNS</*ty=*/ ty, /*user=*/ 0b0, (outs cls:$rd),
                                 (ins GPR:$rs1, GPR:$rs2),
                                 !strconcat("ld.", option, "u"),
                                 [(set (vt cls:$rd),
                                       (operator (ADDRrr (i32 GPR:$rs1),
                                                         (i32 GPR:$rs2))))]> {}
  def u # option # u : F_LSINDUSCUNS</*ty=*/ ty, /*user=*/ 0b1, (outs cls:$rd),
                                     (ins GPR:$rs1, GPR:$rs2),
                                     !strconcat("ld.", option, "u.usr")> {}
  def s # option : F_LSINDSCUNS</*ty=*/ ty, /*user=*/ 0b0, (outs cls:$rd),
                                (ins GPR:$rs1, GPR:$rs2),
                                !strconcat("ld.", option, "u"),
                                [(set (vt cls:$rd),
                                      (operator (addr (i32 GPR:$rs1),
                                                      (i32 GPR:$rs2))))]> {}
  def s # option # u : F_LSINDSCUNS</*ty=*/ ty, /*user=*/ 0b1, (outs cls:$rd),
                                    (ins GPR:$rs1, GPR:$rs2),
                                    !strconcat("ld.", option, "u.usr")> {}
}

multiclass LoadUnsigned {
  def urih : F_LU<0b0, (outs GPR:$rd), (ins GPR:$rs1, uimm16:$si16),
                  "ld.hu",
                  [(set (i32 GPR:$rd), (zextloadi16 (ADDRri (i32 GPR:$rs1), uimm16:$si16)))]>;
  def urib : F_LU<0b1, (outs GPR:$rd), (ins GPR:$rs1, uimm16:$si16),
                  "ld.bu",
                  [(set (i32 GPR:$rd), (zextloadi8 (ADDRri (i32 GPR:$rs1), uimm16:$si16)))]>;
  defm urr : FLoadUnsigned</*ty=*/ 0b1, "b", GPR, i32, zextloadi8, ADDRrs1>;
  defm urr : FLoadUnsigned</*ty=*/ 0b0, "h", GPR, i32, zextloadi16, ADDRrs2>;
}

// Instruction formats with semantics.
multiclass FLoadUnscaled<bits<4> func, bits<2> ty, string option,
                         RegisterOperand cls, ValueType vt,
                         SDPatternOperator operator> {
  def "" : F_LSINDUSC<func, ty, /*user=*/ 0b0, (outs cls:$rd), (ins GPR:$rs1, GPR:$rs2),
                      !if(!eq(option,""), "ld", !strconcat("ld.", option)),
                      [(set (vt cls:$rd), (operator (ADDRrr (i32 GPR:$rs1),
                                                            (i32 GPR:$rs2))))]> {}
  def u : F_LSINDUSC<func, ty, /*user=*/ 0b1, (outs cls:$rd), (ins GPR:$rs1, GPR:$rs2),
                     !if(!eq(option,""), "ld.usr", !strconcat("ld.", option, ".usr"))> {}
}

multiclass LoadUnscaled {
  defvar Func = 0b0001;
  let regfile = 1 in {
    defm rrud  : FLoadUnscaled<Func, /*ty=*/ 0b00, "d", GPR64, i64, load>;
    defm rruw  : FLoadUnscaled<Func, /*ty=*/ 0b01, "", GPR, i32, load>;
    defm rrub  : FLoadUnscaled<Func, /*ty=*/ 0b11, "b", GPR, i32, sextloadi8>;
    defm rruh  : FLoadUnscaled<Func, /*ty=*/ 0b10, "h", GPR, i32, sextloadi16>;
  }
  let regfile = 0, Predicates = [MC88110] in {
    defm xxuw  : FLoadUnscaled<Func, /*ty=*/ 0b01, "", XR, f32, load>;
    defm xxud  : FLoadUnscaled<Func, /*ty=*/ 0b00, "d", XR, f64, load>;
    defm xxuq  : FLoadUnscaled<Func, /*ty=*/ 0b10, "x", XR, f80, load>;
  }
}

// Instruction formats with semantics.
multiclass FLoadScaled<bits<4> func, bits<2> ty, string option,
                       RegisterOperand cls, ValueType vt,
                       SDPatternOperator operator, ComplexPattern addr> {
  def "" : F_LSINDSC<func, ty, /*user=*/ 0b0, (outs cls:$rd), (ins GPR:$rs1, GPR:$rs2),
               !if(!eq(option,""), "ld", !strconcat("ld.", option)),
               [(set (vt cls:$rd), (operator (addr (i32 GPR:$rs1),
                                                   (i32 GPR:$rs2))))]>;
  def u : F_LSINDSC<func, ty, /*user=*/ 0b1, (outs cls:$rd), (ins GPR:$rs1, GPR:$rs2),
               !if(!eq(option,""), "ld.usr", !strconcat("ld.", option, ".usr"))>;
}

multiclass LoadScaled {
  defvar Func = 0b0001;
  let regfile = 1 in {
    defm rrsd  : FLoadScaled<Func, /*ty=*/ 0b00, "d", GPR64, i64, load, ADDRrs8>;
    defm rrsw  : FLoadScaled<Func, /*ty=*/ 0b01, "", GPR, i32, load, ADDRrs4>;
    defm rrsb  : FLoadScaled<Func, /*ty=*/ 0b11, "b", GPR, i32, sextloadi8, ADDRrs1>;
    defm rrsh  : FLoadScaled<Func, /*ty=*/ 0b10, "h", GPR, i32, sextloadi16, ADDRrs2>;
  }
  let regfile = 0, Predicates = [MC88110] in {
    defm xxsw  : FLoadScaled<Func, /*ty=*/ 0b01, "", XR, f32, load, ADDRrs4>;
    defm xxsd  : FLoadScaled<Func, /*ty=*/ 0b00, "d", XR, f64, load, ADDRrs8>;
    defm xxsq  : FLoadScaled<Func, /*ty=*/ 0b10, "x", XR, f80, load, ADDRrs16>;
  }
}

multiclass FStoreUnscaled<bits<4> func, bits<2> ty, string option,
                          RegisterOperand cls, ValueType vt,
                          SDPatternOperator operator> {
  let through = 0 in {
  def "" : F_LSINDUSC<func, /*ty=*/ ty, /*user=*/ 0b0,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st", !strconcat("st.", option)),
               [(operator (vt cls:$rd), (ADDRrr (i32 GPR:$rs1), (i32 GPR:$rs2)))]>;
  def u : F_LSINDUSC<func, /*ty=*/ ty, /*user=*/ 0b1,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st.usr", !strconcat("st.", option, ".usr"))>;
  }
  let through = 1 in {
  def t : F_LSINDUSC<func, /*ty=*/ ty, /*user=*/ 0b0,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st.wt", !strconcat("st.", option, ".wt"))>;
  def ut : F_LSINDUSC<func, /*ty=*/ ty, /*user=*/ 0b1,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st.usr.wt", !strconcat("st.", option, ".usr.wt"))>;
  }
}

multiclass StoreUnscaled {
  defvar Func = 0b0010;
  let regfile = 1 in {
    defm rrud : FStoreUnscaled<Func, /*ty=*/ 0b00, "d", GPR64, i64, store>;
    defm rruw : FStoreUnscaled<Func, /*ty=*/ 0b01, "", GPR, i32, store>;
    defm rrub : FStoreUnscaled<Func, /*ty=*/ 0b11, "b", GPR, i32, truncstorei8>;
    defm rruh : FStoreUnscaled<Func, /*ty=*/ 0b10, "h", GPR, i32, truncstorei16>;
  }
  let regfile = 0, Predicates = [MC88110] in {
    defm xrus : FStoreUnscaled<Func, /*ty=*/ 0b01, "", XR, f32, store>;
    defm xrud : FStoreUnscaled<Func, /*ty=*/ 0b00, "d", XR, f64, store>;
    defm xrux : FStoreUnscaled<Func, /*ty=*/ 0b10, "x", XR, f80, store>;
  }
}

multiclass FStoreScaled<bits<4> func, bits<2> ty, string option,
                          RegisterOperand cls, ValueType vt,
                          SDPatternOperator operator, ComplexPattern addr> {
  let through = 0 in {
  def "" : F_LSINDSC<func, /*ty=*/ ty, /*user=*/ 0b0,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st", !strconcat("st.", option)),
               [(operator (vt cls:$rd), (addr (i32 GPR:$rs1), (i32 GPR:$rs2)))]>;
  def u : F_LSINDSC<func, /*ty=*/ ty, /*user=*/ 0b1,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st.usr", !strconcat("st.", option, ".usr"))>;
  }
  let through = 1 in {
  def t : F_LSINDSC<func, /*ty=*/ ty, /*user=*/ 0b0,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st.wt", !strconcat("st.", option, ".wt"))>;
  def ut : F_LSINDSC<func, /*ty=*/ ty, /*user=*/ 0b1,
               (outs), (ins cls:$rd, GPR:$rs1, GPR:$rs2),
               !if(!eq(option, ""), "st.usr.wt", !strconcat("st.", option, ".usr.wt"))>;
  }
}

multiclass StoreScaled {
  defvar Func = 0b0010;
  let regfile = 1 in {
    defm rrsd : FStoreScaled<Func, /*ty=*/ 0b00, "d", GPR64, i64, store, ADDRrs8>;
    defm rrsw : FStoreScaled<Func, /*ty=*/ 0b01, "", GPR, i32, store, ADDRrs4>;
    defm rrsb : FStoreScaled<Func, /*ty=*/ 0b11, "b", GPR, i32, truncstorei8, ADDRrs1>;
    defm rrsh : FStoreScaled<Func, /*ty=*/ 0b10, "h", GPR, i32, truncstorei16, ADDRrs2>;
  }
  let regfile = 0, Predicates = [MC88110] in {
    defm xrss : FStoreScaled<Func, /*ty=*/ 0b01, "", XR, f32, store, ADDRrs4>;
    defm xrsd : FStoreScaled<Func, /*ty=*/ 0b00, "d", XR, f64, store, ADDRrs8>;
    defm xrsx : FStoreScaled<Func, /*ty=*/ 0b10, "x", XR, f80, store, ADDRrs16>;
  }
}

multiclass LoadAddr<string OpcStr> {
  def ds : F_LADDR</*ty=*/ 0b00, /*scl=*/ 0b1,
                   (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                   !strconcat(OpcStr, ".d")>;
  def ws : F_LADDR</*ty=*/ 0b01, /*scl=*/ 0b1,
                   (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                   OpcStr>;
  def hs : F_LADDR</*ty=*/ 0b10, /*scl=*/ 0b1,
                   (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                   !strconcat(OpcStr, ".h")>;

  let Predicates = [NotMC88110] in
    def bs : F_LADDR</*ty=*/ 0b11, /*scl=*/ 0b1,
                     (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                     !strconcat(OpcStr, ".b")>;
  let Predicates = [MC88110], DecoderNamespace = "MC88110" in
    def xs : F_LADDR</*ty=*/ 0b11, /*scl=*/ 0b1,
                     (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                     !strconcat(OpcStr, ".x")>;

  // The unscaled versions with imm or register are only defined for MC88100.
  let Predicates = [NotMC88110] in {
    def du : F_LADDR</*ty=*/ 0b00, /*scl=*/ 0b0,
                     (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                     !strconcat(OpcStr, ".d")>;
    def wu : F_LADDR</*ty=*/ 0b01, /*scl=*/ 0b0,
                     (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                     OpcStr>;
    def hu : F_LADDR</*ty=*/ 0b10, /*scl=*/ 0b0,
                     (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                     !strconcat(OpcStr, ".h")>;
    def bu : F_LADDR</*ty=*/ 0b11, /*scl=*/ 0b0,
                     (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                     !strconcat(OpcStr, ".b")>;

    def rid  : F_LS</*func=*/ 0b0011, /*ty=*/ 0b00,
                    (outs GPR:$rd), (ins GPR:$rs1, uimm16:$si16),
                    !strconcat(OpcStr, ".d")>;
    def riw  : F_LS</*func=*/ 0b0011, /*ty=*/ 0b01,
                    (outs GPR:$rd), (ins GPR:$rs1, uimm16:$si16),
                    OpcStr>;
    def rih  : F_LS</*func=*/ 0b0011, /*ty=*/ 0b10,
                    (outs GPR:$rd), (ins GPR:$rs1, uimm16:$si16),
                    !strconcat(OpcStr, ".h")>;
    def rib  : F_LS</*func=*/ 0b0011, /*ty=*/ 0b11,
                    (outs GPR:$rd), (ins GPR:$rs1, uimm16:$si16),
                    !strconcat(OpcStr, ".b")>;
  }
}

multiclass Xmem {
  let Predicates = [NotMC88110] in {
    def bi : F_XMEMIMM</*ty=*/ 0b00,
                        (outs GPR:$rd), (ins GPR:$rs1, uimm16:$imm16),
                        "xmem.bu">;
    def wi : F_XMEMIMM</*ty=*/ 0b01,
                        (outs GPR:$rd), (ins GPR:$rs1, uimm16:$imm16),
                        "xmem">;
  }

  foreach U = 0-1 in {
    defvar Suffix = !if(U, ".usr", "");
    defvar S = !if(U, "u", "");
    def urrub#S : F_XMEMUNS</*ty=*/ 0b0, /*user=*/ U,
                            (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                            !strconcat("xmem.bu", Suffix)>;
    def urruh#S : F_XMEMUNS</*ty=*/ 0b1, /*user=*/ U,
                            (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                            !strconcat("xmem", Suffix)>;
    def urrsb#S : F_XMEMSC</*ty=*/ 0b0, /*user=*/ U,
                           (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                           !strconcat("xmem.bu", Suffix)>;
    def urrsh#S : F_XMEMSC</*ty=*/ 0b1, /*user=*/ U,
                           (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
                           !strconcat("xmem", Suffix)>;
  }
}

let mayLoad = 1 in {
  defm LD : LoadIndexImm;
  defm LD : LoadUnsigned;
  defm LD : LoadUnscaled;
  defm LD : LoadScaled;
}

defm LDA : LoadAddr<"lda">;

let mayStore = 1 in {
  defm ST : StoreIndexImm;
  defm ST : StoreUnscaled;
  defm ST : StoreScaled;
}

defm XMEM : Xmem;

// Additional patterns for floating point types.
def : Pat<(f32 (load (ADDRrs4 (i32 GPR:$rs1), (i32 GPR:$rs2)))),
          (LDrrsw GPR:$rs1, GPR:$rs2)>;
def : Pat<(f64 (load (ADDRrs8 (i32 GPR:$rs1), (i32 GPR:$rs2)))),
          (LDrrsd GPR:$rs1, GPR:$rs2)>;
def : Pat<(f32 (load (ADDRri (i32 GPR:$rs1), uimm16:$si16))),
          (LDriw GPR:$rs1, uimm16:$si16)>;
def : Pat<(f64 (load (ADDRri (i32 GPR:$rs1), uimm16:$si16))),
          (LDrid GPR:$rs1, uimm16:$si16)>;
def : Pat<(f32 (load (ADDRrr (i32 GPR:$rs1), (i32 GPR:$rs2)))),
          (LDrruw GPR:$rs1, GPR:$rs2)>;
def : Pat<(f64 (load (ADDRrr (i32 GPR:$rs1), (i32 GPR:$rs2)))),
          (LDrrud GPR:$rs1, GPR:$rs2)>;

def : Pat<(store (f32 GPR:$rd), (ADDRrs4 (i32 GPR:$rs1), (i32 GPR:$rs2))),
          (STrrsw (f32 GPR:$rd), GPR:$rs1, GPR:$rs2)>;
def : Pat<(store (f64 GPR64:$rd), (ADDRrs8 (i32 GPR:$rs1), (i32 GPR:$rs2))),
          (STrrsd (f64 GPR64:$rd), GPR:$rs1, GPR:$rs2)>;
def : Pat<(store (f32 GPR:$rd), (ADDRri (i32 GPR:$rs1), uimm16:$si16)),
          (STriw (f32 GPR:$rd), GPR:$rs1, uimm16:$si16)>;
def : Pat<(store (f64 GPR64:$rd), (ADDRri (i32 GPR:$rs1), uimm16:$si16)),
          (STrid (f64 GPR64:$rd), GPR:$rs1, uimm16:$si16)>;
def : Pat<(store (f32 GPR:$rd), (ADDRrr (i32 GPR:$rs1), (i32 GPR:$rs2))),
          (STrruw (f32 GPR:$rd), GPR:$rs1, GPR:$rs2)>;
def : Pat<(store (f64 GPR64:$rd), (ADDRrr (i32 GPR:$rs1), (i32 GPR:$rs2))),
          (STrrud (f64 GPR64:$rd), GPR:$rs1, GPR:$rs2)>;

// Storing a zero constant.
def : Pat<(store (i32 0), (ADDRrs4 (i32 GPR:$rs1), (i32 GPR:$rs2))),
          (STrrsw (i32 R0), GPR:$rs1, GPR:$rs2)>;
def : Pat<(store (i32 0), (ADDRri (i32 GPR:$rs1), uimm16:$si16)),
          (STriw (i32 R0), GPR:$rs1, uimm16:$si16)>;
def : Pat<(store (i32 0), (ADDRrr (i32 GPR:$rs1), (i32 GPR:$rs2))),
          (STrruw (i32 R0), GPR:$rs1, GPR:$rs2)>;

// Patterns to replace add/shl sequence with lda instruction.
def : Pat<(add GPR:$rs1, (shl GPR:$rs2, (i32 1))), (LDAhs GPR:$rs1, GPR:$rs2)>;
def : Pat<(add GPR:$rs1, (shl GPR:$rs2, (i32 2))), (LDAws GPR:$rs1, GPR:$rs2)>;
let Predicates = [MC88110] in
  def : Pat<(add GPR:$rs1, (shl GPR:$rs2, (i32 3))), (LDAxs GPR:$rs1, GPR:$rs2)>;

// GlobalAddress, ExternalSymbol, Jumptable, ConstantPool
def : Pat<(m88k_hi tglobaladdr:$dst), (ORriu (i32 R0), tglobaladdr:$dst)>;
//def : Pat<(m88k_lo tglobaladdr:$dst), (OR_I_LO (i32 R0), tglobaladdr:$dst)>;

// ---------------------------------------------------------------------------//
// Flow control
// ---------------------------------------------------------------------------//

let isBarrier = 1, isBranch = 1, isTerminator = 1, isIndirectBranch = 1 in {
  def JMP : F_JMP<0b11000, "jmp", [(brind GPR:$rs2)]>;
  let hasDelaySlot = 1 in
    def JMPn : F_JMP<0b11000, "jmp">;
}

let isCall = 1, Defs = [R1] in {
  def JSR : F_JMP<0b11001, "jsr">;
  let hasDelaySlot = 1 in
    def JSRn : F_JMP<0b11001, "jsr">;

  def BSR : F_BRANCH<0b11001, (ins brtarget26:$d26), "bsr">;
  let hasDelaySlot = 1 in
    def BSRn : F_BRANCH<0b11001, (ins brtarget26:$d26), "bsr">;
}

let isReturn = 1, isTerminator = 1, isBarrier = 1, Uses = [R1],
    Opcode = "RET" in {
  def RET : Pseudo<(outs), (ins), [(retflag)]>;
  let hasDelaySlot = 1 in
    def RETn : Pseudo<(outs), (ins), [(retflag)]>;
}

let isBranch = 1, isTerminator = 1, isBarrier = 1 in {
  def BR : F_BRANCH<0b11000, (ins brtarget26:$d26), "br",
                    [(br bb:$d26)]>;
  let hasDelaySlot = 1 in
    def BRn : F_BRANCH<0b11000, (ins brtarget26:$d26), "br">;
}

let isBranch = 1, isTerminator = 1 in {
  def BB0 : F_BCOND<0b11010,
                    (outs), (ins imm32zx5:$m5, GPR:$rs1, brtarget16:$d16),
                    "bb0">;
  def BB1 : F_BCOND<0b11011,
                    (outs), (ins imm32zx5:$m5, GPR:$rs1, brtarget16:$d16),
                    "bb1">;
  def BCND : F_BCOND<0b11101,
                     (outs), (ins ccode:$m5, GPR:$rs1, brtarget16:$d16),
                     "bcnd">;
  let hasDelaySlot = 1 in {
    def BB0n : F_BCOND<0b11010,
                       (outs), (ins imm32zx5:$m5, GPR:$rs1, brtarget16:$d16),
                       "bb0">;
    def BB1n : F_BCOND<0b11011,
                      (outs), (ins imm32zx5:$m5, GPR:$rs1, brtarget16:$d16),
                      "bb1">;
    def BCNDn : F_BCOND<0b11101,
                        (outs), (ins ccode:$m5, GPR:$rs1, brtarget16:$d16),
                        "bcnd">;
  }
}

let isTrap = 1, isBarrier = 1 in {
  def TB0 : F_TB<0b1101000, (outs), (ins imm32zx5:$b5, GPR:$rs1, Vec9:$vec9),
                 "tb0">;
  def TB1 : F_TB<0b1101100, (outs), (ins imm32zx5:$b5, GPR:$rs1, Vec9:$vec9),
                 "tb1">;
  def TCND : F_TCND<(outs), (ins ccode:$m5, GPR:$rs1, Vec9:$vec9), "tcnd">;
  def TBNDi : F_TBNDIMM<(outs), (ins GPR:$rs1, uimm16:$imm16), "tbnd">;
  def TBND : F_TBND<(outs), (ins GPR:$rs1, GPR:$rs2), "tbnd">;

  let isTerminator = 1, isCodeGenOnly = 1 in {
    // Raises trap with vector 502 if bit 0 of %rs1 is not set. This is used to
    // generate the trap after a zero division. Marked as terminator to allow
    // instruction to be last of basic block.
    def TRAP503 : InstM88k<(outs), (ins GPR:$rs1), "tb0", "0, $rs1, 503", []> {
      bits<5>  b5;
      bits<5>  rs1;
      bits<9>  vec9;

      let Inst{31-26} = 0b111100;
      let Inst{25-21} = 0b00000;
      let Inst{20-16} = rs1;
      let Inst{15-9}  = 0b1101000;
      let Inst{8-0}   = 0b111110111;
    }
  }
}

// Compares against zero use bcond instruction.
def : Pat<(brcc SETEQ, GPR:$rs1, 0, bb:$dst),
          (BCND 0b00010, GPR:$rs1, bb:$dst)>;
def : Pat<(brcc SETNE, GPR:$rs1, 0, bb:$dst),
          (BCND 0b01101, GPR:$rs1, bb:$dst)>;
def : Pat<(brcc SETGT, GPR:$rs1, 0, bb:$dst),
          (BCND 0b00001, GPR:$rs1, bb:$dst)>;
def : Pat<(brcc SETLT, GPR:$rs1, 0, bb:$dst),
          (BCND 0b01100, GPR:$rs1, bb:$dst)>;
def : Pat<(brcc SETGE, GPR:$rs1, 0, bb:$dst),
          (BCND 0b00011, GPR:$rs1, bb:$dst)>;
def : Pat<(brcc SETLE, GPR:$rs1, 0, bb:$dst),
          (BCND 0b01110, GPR:$rs1, bb:$dst)>;

// Generate patterns for brcc and bcond nodes.
multiclass BranchPat<CondCode CC, PatFrag ccop, bits<5> m5> {
  def : Pat<(brcc CC, (i32 GPR:$rs1), (i32 GPR:$rs2), bb:$dst),
             (BB1 m5, (CMPrr GPR:$rs1, GPR:$rs2), bb:$dst)>;
  def : Pat<(brcc CC, (i32 GPR:$rs1), uimm16:$imm16, bb:$dst),
             (BB1 m5, (CMPri GPR:$rs1, uimm16:$imm16), bb:$dst)>;
  def : Pat<(brcond (i32 (ccop (i32 GPR:$lhs), (i32 GPR:$rhs))), bb:$dst),
             (BB1 m5, (CMPrr GPR:$lhs, GPR:$rhs), bb:$dst)>;
  def : Pat<(brcond (i32 (ccop (i32 GPR:$lhs), uimm16:$rhs)), bb:$dst),
             (BB1 m5, (CMPri GPR:$lhs, uimm16:$rhs), bb:$dst)>;
}

// Compare integer registers / integer register and immediate.
defm : BranchPat<SETEQ, seteq, 2>;
defm : BranchPat<SETNE, setne, 3>;
defm : BranchPat<SETGT, setgt, 4>;
defm : BranchPat<SETLE, setle, 5>;
defm : BranchPat<SETLT, setlt, 6>;
defm : BranchPat<SETGE, setge, 7>;
defm : BranchPat<SETUGT, setugt, 8>;
defm : BranchPat<SETULE, setule, 9>;
defm : BranchPat<SETULT, setult, 10>;
defm : BranchPat<SETUGE, setuge, 11>;

let isTerminator = 1, isBarrier = 1 in {
  def RTE : F_RTEILLOP<0b00, "rte">;
  def ILLOP1 : F_RTEILLOP<0b01, "illop1">;
  def ILLOP2 : F_RTEILLOP<0b10, "illop2">;
  def ILLOP3 : F_RTEILLOP<0b11, "illop3">;
}

// Alias for no operation.
def : InstAlias<"nop", (ORrr R0, R0, R0)>;

// ---------------------------------------------------------------------------//
// Floating point instructions.
// ---------------------------------------------------------------------------//

// Helper classes to select floating point operands.

class FloatType<string optionin, ValueType vtin, int sizein, RegisterOperand clsin,
                bits<2> encin> {
  string option = optionin;
  ValueType vt = vtin;
  int size = sizein; // TODO Get from RegisterClass
  RegisterOperand cls = clsin;
  bits<2> enc = encin;
}

def FTG32 : FloatType<"s", f32, 32, GPR, 0>;
def FTG64 : FloatType<"d", f64, 64, GPR64, 1>;
def FTX32 : FloatType<"s", f32, 32, XR, 0>;
def FTX64 : FloatType<"d", f64, 64, XR, 1>;
def FTX80 : FloatType<"x", f80, 80, XR, 2>;

class FloatSrc1<FloatType S1, FloatType S2> {
  dag val = !if(!lt(S1.size, S2.size),
                (S2.vt (fpextend (S1.vt S1.cls:$rs1))),
                (S1.vt S1.cls:$rs1));
}
class FloatSrc2<FloatType S1, FloatType S2> {
  dag val = !if(!gt(S1.size, S2.size),
                (S1.vt (fpextend (S2.vt S2.cls:$rs2))),
                (S2.vt S2.cls:$rs2));
}
class FloatPat<FloatType D, FloatType S1, FloatType S2, SDPatternOperator op> {
  defvar dags1 = FloatSrc1<S1, S2>.val;
  defvar dags2 = FloatSrc2<S1, S2>.val;
  defvar extend = !and(!gt(D.size, S1.size), !gt(D.size, S2.size));
  defvar round = !or(!lt(D.size, S1.size), !lt(D.size, S2.size));
  dag val = !cond(extend : (D.vt (fpextend (op dags1, dags2))),
                  round : (D.vt (fpround (op dags1, dags2))),
                  true: (op dags1, dags2));
}

// Multiclass for triadic register floating point instructions.
multiclass FArith<bits<4> Func, string OpcStr, SDPatternOperator op> {
  foreach D = [FTG32, FTG64] in {
    foreach S1 = [FTG32, FTG64] in {
      foreach S2 =[FTG32, FTG64] in {
        let regfile = 0 in {
          def g # D.option # S1.option # S2.option :
                  F_SFU1<Func, D.enc, S1.enc, S2.enc,
                      (outs D.cls:$rd), (ins S1.cls:$rs1, S2.cls:$rs2),
                      !strconcat(OpcStr, ".", D.option, S1.option, S2.option),
                      [(set (D.vt D.cls:$rd), FloatPat<D, S1, S2, op>.val)]>;
        }
      }
    }
  }
  foreach D = [FTX32, FTX64, FTX80] in {
    foreach S1 = [FTX32, FTX64, FTX80] in {
      foreach S2 =[FTX32, FTX64, FTX80] in {
        let regfile = 1 in {
          def x # D.option # S1.option # S2.option :
                  F_SFU1<Func, D.enc, S1.enc, S2.enc,
                      (outs D.cls:$rd), (ins S1.cls:$rs1, S2.cls:$rs2),
                      !strconcat(OpcStr, ".", D.option, S1.option, S2.option),
                      [(set (D.vt D.cls:$rd), FloatPat<D, S1, S2, op>.val)]>;
        }
      }
    }
  }
}

// Multiclass for dyadic register floating point instructions, single prec.
multiclass FArith2<bits<4> Func, string OpcStr> {
  foreach S2 = [FTG32, FTG64] in {
    let regfile = 0 in {
      def gs # S2.option :
              F_SFU1D<Func, /*td=*/ 0b00, /*t1=*/ 0b00, /*t2=*/ S2.enc,
                      (outs GPR:$rd), (ins S2.cls:$rs2),
                      !strconcat(OpcStr, ".s", S2.option)>;
    }
  }
  foreach S2 = [FTX32, FTX64, FTX80] in {
    let regfile = 1 in {
      def xs # S2.option :
              F_SFU1D<Func, /*td=*/ 0b00, /*t1=*/ 0b00, /*t2=*/ S2.enc,
                      (outs GPR:$rd), (ins S2.cls:$rs2),
                      !strconcat(OpcStr, ".s", S2.option)>;
    }
  }
}

// Multiclass for dyadic register floating point instructions, unary.
multiclass FUnary<bits<4> Func, string OpcStr, bit eq> {
  foreach D = [FTG32, FTG64] in {
    foreach S2 = [FTG32, FTG64] in {
      defvar IsLegal = !or(eq, !ne(D, S2));
      if IsLegal then {
        let regfile = 0 in {
          def g # D.option # S2.option :
              F_SFU1D<Func, D.enc, /*t1=*/ 0b00, S2.enc,
                      (outs D.cls:$rd), (ins S2.cls:$rs2),
                      !strconcat(OpcStr, ".", D.option, S2.option)>;
        }
      }
    }
  }
  foreach D = [FTX32, FTX64, FTX80] in {
    foreach S2 = [FTX32, FTX64, FTX80] in {
      defvar IsLegal = !or(eq, !ne(D, S2));
      if IsLegal then {
        let regfile = 1 in {
          def x # D.option # S2.option :
              F_SFU1D<Func, D.enc, /*t1=*/ 0b00, S2.enc,
                      (outs D.cls:$rd), (ins S2.cls:$rs2),
                      !strconcat(OpcStr, ".", D.option, S2.option)>;
        }
      }
    }
  }
}

// Multiclass for triadic register floating point instructions fcmp/fcmpu.
multiclass FCmp<bits<4> Func, bits<2> td, string OpcStr> {
  foreach S1 = [FTG32, FTG64] in {
    foreach S2 = [FTG32, FTG64] in {
      let regfile = 0 in {
        def gs # S1.option # S2.option :
            F_SFU1<Func, /*td=*/ td, /*t1=*/ S1.enc, /*t2=*/ S2.enc,
                   (outs GPR:$rd), (ins S1.cls:$rs1, S2.cls:$rs2),
                   !strconcat(OpcStr, ".s", S1.option, S2.option)>;
      }
    }
  }
  foreach S1 = [FTX32, FTX64, FTX80] in {
    foreach S2 = [FTX32, FTX64, FTX80] in {
      let regfile = 1 in {
        def xs # S1.option # S2.option :
            F_SFU1<Func, /*td=*/ td, /*t1=*/ S1.enc, /*t2=*/ S2.enc,
                   (outs GPR:$rd), (ins S1.cls:$rs1, S2.cls:$rs2),
                   !strconcat(OpcStr, ".s", S1.option, S2.option)>;
      }
    }
  }
}

defm FMUL : FArith<0b0000, "fmul", fmul>;
defm FADD : FArith<0b0101, "fadd", fadd>;
defm FSUB : FArith<0b0110, "fsub", fsub>;
defm FDIV : FArith<0b1110, "fdiv", fdiv>;

defm INT : FArith2<0b1001, "int">;
defm NINT : FArith2<0b1010, "nint">;
defm TRNC : FArith2<0b1011, "trnc">;

let Predicates = [MC88110] in {
  defm FCVT : FUnary<0b0001, "fcvt", false>;
  defm FSQRT : FUnary<0b1111, "fsqrt", true>;

  def : Pat<(fpextend (f32 GPR:$rs1)),
            (FCVTgds GPR:$rs1)>;
  def : Pat<(fpround (f64 GPR64:$rs1)),
            (FCVTgsd GPR64:$rs1)>;

  def : Pat<(f64 (fpextend (f32 XR:$rs1))),
            (FCVTxds XR:$rs1)>;
  def : Pat<(f80 (fpextend (f32 XR:$rs1))),
            (FCVTxxs XR:$rs1)>;
  def : Pat<(f80 (fpextend (f64 XR:$rs1))),
            (FCVTxxd XR:$rs1)>;
  def : Pat<(f32 (fpround (f64 XR:$rs1))),
            (FCVTxsd XR:$rs1)>;
  def : Pat<(f32 (fpround (f80 XR:$rs1))),
            (FCVTxsx XR:$rs1)>;
  def : Pat<(f64 (fpround (f80 XR:$rs1))),
            (FCVTxdx XR:$rs1)>;
}

def : Pat<(fpextend (f32 GPR:$rs1)),
          (FSUBgdss GPR:$rs1, (f32 R0))>;
def : Pat<(fpround (f64 GPR64:$rs1)),
          (FSUBgsds GPR64:$rs1, (f32 R0))>;

// Missing: fcmp, fcmpu
defm FCMP : FCmp<0b0111, 0b00, "fcmp">;
let Predicates = [MC88110] in
  defm FCMPU : FCmp<0b0111, 0b01, "fcmpu">;

let regfile = 0 in {
def FLTgss : F_SFU1FLT</*td=*/ 0b00,
                       (outs GPR:$rd), (ins GPR:$rs2),
                       "flt.ss",
                       [(set (f32 GPR:$rd), (sint_to_fp (i32 GPR:$rs2)))]>;
def FLTgds : F_SFU1FLT</*td=*/ 0b01,
                       (outs GPR64:$rd), (ins GPR:$rs2),
                       "flt.ds",
                       [(set (f64 GPR64:$rd), (sint_to_fp (i32 GPR:$rs2)))]>;
}
let regfile = 1, Predicates = [MC88110] in {
def FLTxss : F_SFU1FLT</*td=*/ 0b00,
                       (outs XR:$rd), (ins GPR:$rs2),
                       "flt.ss",
                       [(set (f32 XR:$rd), (sint_to_fp (i32 GPR:$rs2)))]>;
def FLTxds : F_SFU1FLT</*td=*/ 0b01,
                       (outs XR:$rd), (ins GPR:$rs2),
                       "flt.ds",
                       [(set (f64 XR:$rd), (sint_to_fp (i32 GPR:$rs2)))]>;
def FLTxxs : F_SFU1FLT</*td=*/ 0b10,
                       (outs XR:$rd), (ins GPR:$rs2),
                       "flt.xs",
                       [(set (f80 XR:$rd), (sint_to_fp (i32 GPR:$rs2)))]>;
}

let regfile = 1, isMoveReg = 1, Predicates = [MC88110] in {
def MOVrxs : F_SFU1D<0b1000, /*td*/ 0b00, /*t1*/0b00, /*t2*/0b00,
                     (outs GPR:$rd), (ins XR:$rs2),
                     "mov.s",
                     [(set GPR:$rd, (f32 XR:$rs2))]>;
def MOVrxd : F_SFU1D<0b1000, /*td*/ 0b00, /*t1*/0b00, /*t2*/0b01,
                     (outs GPR64:$rd), (ins XR:$rs2),
                     "mov.d",
                     [(set GPR64:$rd, (f64 XR:$rs2))]>;
def MOVxx : F_SFU1D<0b1000, /*td*/ 0b00, /*t1*/0b01, /*t2*/0b11,
                    (outs XR:$rd), (ins XR:$rs2),
                    "mov">;
//                    [(set XR:$rd, XR:$rs2)]>;
}

let regfile = 0, isMoveReg = 1, Predicates = [MC88110] in {
def MOVxrs : F_SFU1D<0b1000, /*td*/ 0b00, /*t1*/0b01, /*t2*/0b00,
                     (outs XR:$rd), (ins GPR:$rs2),
                     "mov.s",
                     [(set (f32 XR:$rd), GPR:$rs2)]>;
def MOVxrd : F_SFU1D<0b1000, /*td*/ 0b00, /*t1*/0b01, /*t2*/0b01,
                     (outs XR:$rd), (ins GPR64:$rs2),
                     "mov.d",
                     [(set (f64 XR:$rd), GPR64:$rs2)]>;
}

// ---------------------------------------------------------------------------//
// Control register instructions.
// ---------------------------------------------------------------------------//

let rs1 = 0, rs2 = 0 in {
def LDCR : F_SFU1CR<0b01000, (outs GPR:$rd), (ins CR:$cr),
                    "ldcr", "$rd, $cr">;
def FLDCR : F_SFU1CR<0b01001, (outs GPR:$rd), (ins FCR:$cr),
                     "fldcr", "$rd, $cr">;
}

let rd = 0 in {
def STCR : F_SFU1CR2<0b10000, (outs CR:$cr), (ins GPR:$rs1),
                     "stcr", "$rs1, $cr">;
def FSTCR : F_SFU1CR2<0b10001, (outs FCR:$cr), (ins GPR:$rs1),
                      "fstcr", "$rs1, $cr">;
}

def XCR : F_SFU1CR2<0b11000, (outs GPR:$rd), (ins GPR:$rs1, CR:$cr),
                    "xcr", "$rd, $rs1, $cr">;
def FXCR : F_SFU1CR2<0b11001, (outs GPR:$rd), (ins GPR:$rs1, FCR:$cr),
                     "fxcr", "$rd, $rs1, $cr">;

// ---------------------------------------------------------------------------//
// Graphics/vector instructions. 881100 only.
// ---------------------------------------------------------------------------//

multiclass PArithPixel<bits<5> func, string opc, SDNode OpNode> {
  def "": F_SFU2<func, /*sat=*/ 0b00, /*ty=*/ 0b11,
                 (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                 opc,
                 [(set v2i32:$rd, (OpNode v2i32:$rs1, v2i32:$rs2))]>;
  def b : F_SFU2<func, /*sat=*/ 0b00, /*ty=*/ 0b01,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".b"),
                 [(set v8i8:$rd, (OpNode v8i8:$rs1, v8i8:$rs2))]>;
  def h : F_SFU2<func, /*sat=*/ 0b00, /*ty=*/ 0b10,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".h"),
                 [(set v4i16:$rd, (OpNode v4i16:$rs1, v4i16:$rs2))]>;
}

multiclass PArithPixelSat<bits<5> func, string opc> {
  def u: F_SFU2<func, /*sat=*/ 0b01, /*ty=*/ 0b11,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".u")>;
  def ub: F_SFU2<func, /*sat=*/ 0b01, /*ty=*/ 0b01,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".u.b")>;
  def uh: F_SFU2<func, /*sat=*/ 0b01, /*ty=*/ 0b10,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".u.h")>;
  def us: F_SFU2<func, /*sat=*/ 0b10, /*ty=*/ 0b11,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".us")>;
  def usb: F_SFU2<func, /*sat=*/ 0b10, /*ty=*/ 0b01,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".us.b")>;
  def ush: F_SFU2<func, /*sat=*/ 0b10, /*ty=*/ 0b10,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".us.h")>;
  def s: F_SFU2<func, /*sat=*/ 0b11, /*ty=*/ 0b11,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".s")>;
  def sb: F_SFU2<func, /*sat=*/ 0b11, /*ty=*/ 0b01,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".s.b")>;
  def sh: F_SFU2<func, /*sat=*/ 0b11, /*ty=*/ 0b10,
                  (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  !strconcat(opc, ".s.h")>;
}

multiclass PPack {
  defvar func = 0b01100;
  defvar opc = "ppack";
  def "32b": F_SFU2PPACK<func, /*r=*/ 0b0010, /*ty=*/ 0b11,
                         (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                         !strconcat(opc, ".32.b")>;
  def "32h": F_SFU2PPACK<func, /*r=*/ 0b0100, /*ty=*/ 0b11,
                         (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                         !strconcat(opc, ".32.h")>;
  def "32": F_SFU2PPACK<func, /*r=*/ 0b1000, /*ty=*/ 0b11,
                        (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                        !strconcat(opc, ".32")>;
  def "16h": F_SFU2PPACK<func, /*r=*/ 0b0100, /*ty=*/ 0b10,
                         (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                         !strconcat(opc, ".16.h")>;
  def "16": F_SFU2PPACK<func, /*r=*/ 0b1000, /*ty=*/ 0b10,
                        (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                        !strconcat(opc, ".16")>;
  def "8": F_SFU2PPACK<func, /*r=*/ 0b1000, /*ty=*/ 0b01,
                       (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                       !strconcat(opc, ".8")>;
}

let Predicates = [Graphics] in {

def PMUL : F_SFU2<0b00000, 0b00, 0b00,
                  (outs GPR64:$rd), (ins GPR:$rs1, GPR64:$rs2),
                  "pmul">;
def PCMP : F_SFU2<0b00111, 0b00, 0b11,
                  (outs GPR:$rd), (ins GPR64:$rs1, GPR64:$rs2),
                  "pcmp">;
defm PADD : PArithPixel<0b00100, "padd", add>;
defm PSUB : PArithPixel<0b00110, "psub", sub>;
defm PADDS : PArithPixelSat<0b00100, "padds">;
defm PSUBS : PArithPixelSat<0b00110, "psubs">;
defm PPACK : PPack;
def PROTri : F_SFU2PROT<0b01110, (outs GPR64:$rd),
                        (ins GPR64:$rs1, pixelrot:$o6), "prot">;
def PROTrr : F_SFU2<0b01111, /*sat=*/ 0b00, /*ty=*/ 0b00,
                    (outs GPR64:$rd), (ins GPR64:$rs1, GPR64:$rs2), "prot">;
def PUNPKn : F_SFU2D<0b01101, /*sat=*/ 0b00, /*ty=*/ 0b00,
                     (outs GPR64:$rd), (ins GPR64:$rs1), "punpk.n">;
def PUNPKb : F_SFU2D<0b01101, /*sat=*/ 0b00, /*ty=*/ 0b01,
                     (outs GPR64:$rd), (ins GPR64:$rs1), "punpk.b">;
def PUNPKh : F_SFU2D<0b01101, /*sat=*/ 0b00, /*ty=*/ 0b10,
                     (outs GPR64:$rd), (ins GPR64:$rs1), "punpk.h">;
}
