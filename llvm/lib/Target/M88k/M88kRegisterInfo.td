//===-- M88kRegisterInfo.td - M88k Register definitions ----*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

class M88kReg<bits<5> Enc, string n> : Register<n> {
  let HWEncoding{15-5} = 0;
  let HWEncoding{4-0} = Enc;
  let Namespace = "M88k";
}

class M88kCRReg<bits<6> Enc, string n> : Register<n> {
  let HWEncoding{15-6} = 0;
  let HWEncoding{5-0} = Enc;
  let Namespace = "M88k";
}

// Multiclass to define RegisterClass and RegisterOperand together.
class M88kRegisterClass<list<ValueType> types, int size, int alignment,
                        dag regList, int copycost = 1>
  : RegisterClass<"M88k", types, alignment, regList> {
      let Size = size;
      let CopyCost = copycost;
}

class M88kRegisterOperand<RegisterClass RC> : RegisterOperand<RC> {
  let DecoderMethod = "decode"#RC#"RegisterClass";
}

let Namespace = "M88k" in {
  def sub_hi : SubRegIndex<32, 0>;
  def sub_lo : SubRegIndex<32, 32>;
}

// General-purpose registers
foreach I = 0-31 in {
  let isConstant = !eq(I, 0) in
    def R#I : M88kReg<I, "r"#I>;
}

// The allocation order of the registers is influenced by the use in the ABI.
// First are the temporary registers, then the preserved registers, and then
// the remaining reisters.
// TODO Check if there is a positive impact when moving r30 before r25-r14.
//      Saving the preserved registers creates a frame using r30 as frame
//      pointer, but r30 could be saved/restored without using a frame pointer.
def GPR : M88kRegisterClass<[i32, f32], 32, 32,
                            (add (sequence "R%u", 2, 9),
                                 (sequence "R%u", 25, 14),
                                 R0, R1,
                                 (sequence "R%u", 10, 13),
                                 (sequence "R%u", 26, 31))>;
def GPROpnd : M88kRegisterOperand<GPR> {
  let GIZeroRegister = R0;
}

// Register class representing a pair of even-odd GRs.
def GRPair : RegisterTuples<[sub_hi, sub_lo],
                            [(add (sequence "R%u", 0, 30, 2)),
                             (add (sequence "R%u", 1, 31, 2))]>;

def GPR64 : M88kRegisterClass<[i64, f64, v8i8, v4i16, v2i32], 64, 64,
                              (add GRPair), 2>;
def GPR64Opnd : M88kRegisterOperand<GPR64>;

// Extended (floating point) registers.
foreach I = 0-31 in {
  let isConstant = !eq(I, 0) in
    def X#I : M88kReg<I, "x"#I>;
}

def XR : M88kRegisterClass<[f32, f64, f80], 128, 32,
                           (add (sequence "X%u", 0, 31))>;
def XROpnd : M88kRegisterOperand<XR> {
  let GIZeroRegister = X0;
}

// Control registers.
foreach I = 0-63 in {
  def CR#I : M88kCRReg<I, "cr"#I>;
}

// Carry bit. This is really bit 28 of the processor status register aka cr1.
def CARRY: M88kCRReg<1, "carry"> {
  let Aliases = [CR1];
}

foreach I = 0-63 in {
  def FCR#I : M88kCRReg<I, "fcr"#I>;
}

let isAllocatable = 0 in {
  def CR : M88kRegisterClass<[i32], 32, 32, (add (sequence "CR%u", 0, 63))>;
  def FCR : M88kRegisterClass<[i32], 32, 32, (add (sequence "FCR%u", 0, 63))>;
}
def CROpnd : M88kRegisterOperand<CR>;
def FCROpnd : M88kRegisterOperand<FCR>;
