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

class M88kCRReg<bits<6> Enc, string n, string altName = "">
        : Register<n, !if(!eq(altName, ""), [], [altName])> {
  let HWEncoding{15-6} = 0;
  let HWEncoding{5-0} = Enc;
  let Namespace = "M88k";
}

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

// General-purpose registers.
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
// TODO Check if the register class should be broken up:
//      - MC88100 manual, chapter 3, 3.2.3 states:
//        If general-purpose register r0 is specified as the destination
//        register for any floating-point instruction except fster, flder, and
//        fxcr, the MC88100 takes a floating-point unimplemented opcode
//        exception as described in SECTION 6 EXCEPTIONS.
//      - the stack pointer register r31 is reserved
//      Thus, register classes without r0 and r31 could be useful. 
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
//
// The MC88100 and MC88110 have different restrictions on the use of register pairs.
// MC88110 manual, chapter 2, 2.3.2 states:
//   - Double word operands are loaded to or extracted from two adjacent
//     registers (rn and rn+1), with rn always even and always containing the
//     higher word.
//   - Any double-word and double-precision floating-point operands aligned on
//     odd-numbered register pairs (i.e r5:r6 instead of r4:r5) will cause the
//     following exceptions to occur (...)
//     The exception handler will implement double-word alignment on
//     odd-numbered register pairs in software. Since the software
//     implementation will result in slower execution time, it is recommended
//     that software and compilers align such data to even-numbered registers
//     to guarantee the best performance.
//
// MC88100 manual, chapter 2, 2.2.2 states:
//   - Word operands load or store the entire 32 bits to/from memory;
//     double-word operands load and store two adjacent registers (rn and
//     rn+1) with rn always containing the higher order word
//   - Double-word operands and double-precision floating-point operands can be
//     specified as beginning with r31, in which case r0 contains the lower
//     order word. However, rO may never be modified (writes to rO are
//     ignored).
// And in chapter 2, 2.3.2:
//   - Double-word and double-precision floating-point operands can be read
//     from and written to any two adjacent registers.
//
// Since the ABI only uses even-numbered register pairs, it does not seem worth
// to try to support use of odd-numbered register pairs for the MC88100 only.
// The pair r0:r1 is excluded from the register class, since r0 is constant.
// Likewise, r30:r31 is excluded because r31 is a reserved register.
def GRPair : RegisterTuples<[sub_hi, sub_lo],
                            [(add (sequence "R%u", 2, 28, 2)),
                             (add (sequence "R%u", 3, 29, 2))]>;

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
def CR0 : M88kCRReg<0, "cr0", "PID">;
def CR1 : M88kCRReg<1, "cr1", "PSR">;
def CR2 : M88kCRReg<2, "cr2", "EPSR">;
def CR3 : M88kCRReg<3, "cr3", "SSBR">;
def CR4 : M88kCRReg<4, "cr4", "SXIP">;
def CR5 : M88kCRReg<5, "cr5", "SNIP">;
def CR6 : M88kCRReg<6, "cr6", "SFIP">;
def CR7 : M88kCRReg<7, "cr7", "VBR">;
def CR8 : M88kCRReg<8, "cr8", "DMT0">;
def CR9 : M88kCRReg<9, "cr9", "DMD0">;
def CR10 : M88kCRReg<10, "cr10", "DMA0">;
def CR11 : M88kCRReg<11, "cr11", "DMT1">;
def CR12 : M88kCRReg<12, "cr12", "DMD1">;
def CR13 : M88kCRReg<13, "cr13", "DMA1">;
def CR14 : M88kCRReg<14, "cr14", "DMT2">;
def CR15 : M88kCRReg<15, "cr15", "DMD2">;
def CR16 : M88kCRReg<16, "cr16", "DMA2">;
def CR17 : M88kCRReg<17, "cr17", "SR0">;
def CR18 : M88kCRReg<18, "cr18", "SR1">;
def CR19 : M88kCRReg<19, "cr19", "SR2">;
def CR20 : M88kCRReg<20, "cr20", "SR3">;
foreach I = 21-63 in {
  def CR#I : M88kCRReg<I, "cr"#I>;
}

// Carry bit. This is really bit 28 of the processor status register aka cr1.
def CARRY: M88kCRReg<1, "carry"> {
  let Aliases = [CR1];
}

// Floating point control registers, with alternative names.
def FCR0 : M88kCRReg<0, "fcr0", "FPECR">;
def FCR1 : M88kCRReg<1, "fcr1", "FPHS1">;
def FCR2 : M88kCRReg<2, "fcr2", "FPLS1">;
def FCR3 : M88kCRReg<3, "fcr3", "FPHS2">;
def FCR4 : M88kCRReg<4, "fcr4", "FPLS2">;
def FCR5 : M88kCRReg<5, "fcr5", "FPPT">;
def FCR6 : M88kCRReg<6, "fcr6", "FPRH">;
def FCR7 : M88kCRReg<7, "fcr7", "FPRL">;
def FCR8 : M88kCRReg<8, "fcr8", "FPIT">;
foreach I = 9-61 in {
  def FCR#I : M88kCRReg<I, "fcr"#I>;
}
def FCR62 : M88kCRReg<62, "fcr62", "FPSR">;
def FCR63 : M88kCRReg<63, "fcr63", "FPCR">;

let isAllocatable = 0 in {
  def CR : M88kRegisterClass<[i32], 32, 32, (add (sequence "CR%u", 0, 63))>;
  def FCR : M88kRegisterClass<[i32], 32, 32, (add (sequence "FCR%u", 0, 63))>;
}
def CROpnd : M88kRegisterOperand<CR>;
def FCROpnd : M88kRegisterOperand<FCR>;

//===----------------------------------------------------------------------===//
// Register categories.
//

def GeneralPurposeRegisters : RegisterCategory<[GPR, GPR64, XR]>;
def FixedRegisters : RegisterCategory<[CR, FCR]>;
