//===-- M88kSchedule.td - M88k Scheduling Model ------------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

def M88100SchedModel : SchedMachineModel {
  // The M88100 can issue 1 instruction.
  let IssueWidth = 1;

  // In-order CPU.
  let MicroOpBufferSize = 0;

  int LoadLatency = 3; // Assumes no wait cycle on the bus.

  // Does not support 88110 instructions.
  list<Predicate> UnsupportedFeatures = [MC88110];

  // Not finished yet.
  let CompleteModel = 0;
}

let SchedModel = M88100SchedModel in {
  // Define the processor resources.
  def M88100UnitInt : ProcResource<1> { let BufferSize = 0; }
  def M88100UnitData : ProcResource<1> { let BufferSize = 0; }
  def M88100UnitFPAdd : ProcResource<1> { let BufferSize = 0; }
  def M88100UnitFPMul : ProcResource<1> { let BufferSize = 0; }
  def M88100UnitInst : ProcResource<1> { let BufferSize = 0; }

  // The integer unit: integer arithmetic, logical and bitfield instructions.
  def M88100Int : SchedWriteRes<[M88100UnitInt]>;

  // The data unit: load, store and exchange instructions.
  // The unit has 3 stages.
  def M88100Data : SchedWriteRes<[M88100UnitData]> {
    let Latency = 3;
  }

  // The FP add unit: addition/subtraction/compare/divide instructions.
  // The unit has 5 stages.
  def M88100FPAdd : SchedWriteRes<[M88100UnitFPAdd]> {
    let Latency = 5;
  }
  def M88100Div : SchedWriteRes<[M88100UnitFPAdd]> {
    let Latency = 38;
    let ResourceCycles = [33];
  }
  def M88100DivS : SchedWriteRes<[M88100UnitFPAdd]> {
    let Latency = 30;
    let ResourceCycles = [25];
  }
  def M88100DivD : SchedWriteRes<[M88100UnitFPAdd]> {
    let Latency = 60;
    let ResourceCycles = [54];
  }

  // The FP mul unit: multiplication instructions.
  // The unit has 6 stages.
  def M88100Mul : SchedWriteRes<[M88100UnitFPMul]> {
    let Latency = 4;
  }
  def M88100MulS : SchedWriteRes<[M88100UnitFPMul]> {
    let Latency = 6;
  }
  def M88100MulD : SchedWriteRes<[M88100UnitFPMul]> {
    let Latency = 7;
  }

  // Associate the SchedWrite types with instruction.

  // Integer arithmetic, logical, and bit field instructions.
  def : InstRW<[M88100Int], (instregex "^(ADD(U)?|CMP|SUB(U)?|CLR|EXT(U)?|FF(0|1)|MAK|ROT|SET|AND|MASK|OR|XOR)")>;

  // Control register instructions.
  // TODO fstcr and stcr waive the write back slot.
  def : InstRW<[M88100Int], (instregex "^(FLDCR|FSTCR|FXCR|LDCR|STCR|XCR)")>;

  // Load, store, and exchange instructions.
  def : InstRW<[M88100Data], (instregex "^(LDA|LD(r|u|s)|ST(r|u|s)|XMEM)")>;

  // Add and sub floating point instructons.
  def : InstRW<[M88100FPAdd], (instregex "^(FADD|FSUB|FCMP|FLT|INT|NINT|TRNC)")>;

  // Div instructons.
  def : InstRW<[M88100Div], (instregex "^DIV(U)?")>;
  def : InstRW<[M88100DivS], (instregex "^FDIVgs")>;
  def : InstRW<[M88100DivD], (instregex "^FDIVgd")>;

  // Mul instructons.
  def : InstRW<[M88100Mul], (instregex "^MUL")>;
  def : InstRW<[M88100MulS], (instregex "^FMULgs")>;
  def : InstRW<[M88100MulD], (instregex "^FMULgd")>;
}

def M88110SchedModel : SchedMachineModel {
  // The M88110 can issue 2 instructions.
  let IssueWidth = 2;

  // In-order CPU.
  let MicroOpBufferSize = 0;

  int LoadLatency = 3; // Assumes no wait cycle on the bus. CHECK!

  // Does not support 88110 instructions.
  list<Predicate> UnsupportedFeatures = [NotMC88110];

  // Not finished yet.
  let CompleteModel = 0;
}

// TODO The model is way too simple!
//      - Instruction pairing and bubbles are not modelled
//      - Unpredicted branches are not modelled
let SchedModel = M88110SchedModel in {
  // Define the processor resources.
  def M88110UnitArith : ProcResource<2> { let BufferSize = 0; }   // Arithmetic/Logic
  def M88110UnitBit : ProcResource<1> { let BufferSize = 0; }     // Bit filed
  def M88110UnitMul : ProcResource<1> { let BufferSize = 0; }     // FP/Int multiply
  def M88110UnitDiv : ProcResource<1> { let BufferSize = 0; }     // FP/Int divide
  def M88110UnitFPAdd : ProcResource<1> { let BufferSize = 0; }   // FP addition
  def M88110UnitGraphic : ProcResource<1> { let BufferSize = 0; } // 3D Graphics
  def M88110UnitData : ProcResource<1> { let BufferSize = 0; }    // Load/Store
  def M88110UnitInst : ProcResource<1> { let BufferSize = 0; }    // Instructions

  // The SchedWrite types.
  def M88110Arith : SchedWriteRes<[M88110UnitArith]>;
  def M88110Bit : SchedWriteRes<[M88110UnitBit]>;
  def M88110Mul : SchedWriteRes<[M88110UnitMul]> {
    let Latency = 3;
  }
  def M88110Divf32 : SchedWriteRes<[M88110UnitDiv]> {
    let Latency = 13; // Plus 3 if either operand is 0.
  }
  def M88110Divf64 : SchedWriteRes<[M88110UnitDiv]> {
    let Latency = 23; // Plus 3 if either operand is 0.
  }
  def M88110Divf80 : SchedWriteRes<[M88110UnitDiv]> {
    let Latency = 26; // Plus 3 if either operand is 0.
  }
  def M88110Divi32 : SchedWriteRes<[M88110UnitDiv]> {
    let Latency = 18; // Plus 5 if either operand is 0.
  }
  def M88110FPAdd : SchedWriteRes<[M88110UnitFPAdd]> {
    let Latency = 3;
  }
  def M88110FPCmp : SchedWriteRes<[M88110UnitFPAdd]> {
    let Latency = 1;
  }
  def M88110Graphic : SchedWriteRes<[M88110UnitGraphic]>;
  def M88110DataSt : SchedWriteRes<[M88110UnitData]>;
  def M88110DataLd : SchedWriteRes<[M88110UnitData]> {
    let Latency = 2; // Plus 3 if cache miss.
  }
  def M88110DataLdx : SchedWriteRes<[M88110UnitData]> {
    let Latency = 3; // Plus 3 if cache miss.
  }
  def M88110DataXmem : SchedWriteRes<[M88110UnitData]> {
    let Latency = 10; // Plus serialize.
  }
  def M88110Inst : SchedWriteRes<[M88110UnitInst]>;
  def M88110InstSer : SchedWriteRes<[M88110UnitInst]> {
    let Latency = 2; // Plus serialize.
  }

  // Associate the SchedWrite types with instruction.
  def : InstRW<[M88110Arith], (instregex "^(ADD(U)?|CMP|SUB(U)?|LDA|AND|MASK|OR|XOR)")>;

  // A copy is usually replaced with a OR instruction.
  def : InstRW<[M88110Arith], (instregex "^COPY")>;

  def : InstRW<[M88110Bit], (instregex "^(CLR|EXT(U)?|FF(0|1)|MAK|ROT|SET)")>;

  def : InstRW<[M88110Divf32], (instregex "^(FDIV(g|x)s)")>;
  def : InstRW<[M88110Divf64], (instregex "^(FDIV(g|x)d)")>;
  def : InstRW<[M88110Divf80], (instregex "^(FDIVxx)")>;
  def : InstRW<[M88110Divi32], (instregex "^(DIVS|DIVU)")>;

  def : InstRW<[M88110Mul], (instregex "^(MULS|MULU|FMUL|PMUL)")>;

  def : InstRW<[M88110FPAdd], (instregex "^(FADD|FSUB|FCVT|FLT|INT|NINT|TRNC)")>;
  def : InstRW<[M88110FPCmp], (instregex "^FCMP")>;

  def : InstRW<[M88110Graphic], (instregex "^(PADD|PSUB|PCMP|PPACK|PUNPK|PROT)")>;

  def : InstRW<[M88110DataSt], (instregex "^ST")>;
  def : InstRW<[M88110DataLd], (instregex "^LD(r|u|s)")>;
  def : InstRW<[M88110DataLdx], (instregex "^LDx")>;
  def : InstRW<[M88110DataXmem], (instregex "^XMEM")>;

  def : InstRW<[M88110Inst], (instregex "^MOV")>;
  def : InstRW<[M88110InstSer], (instregex "^(FLDCR|FSTCR|FXCR)")>;
}
