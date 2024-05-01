//===-- M88kLegalizerInfo.cpp -----------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// This file implements the targeting of the Machinelegalizer class for M88k.
//===----------------------------------------------------------------------===//

#include "M88kLegalizerInfo.h"
#include "M88kInstrInfo.h"
#include "M88kSubtarget.h"
#include "MCTargetDesc/M88kMCTargetDesc.h"
#include "llvm/CodeGen/GlobalISel/GenericMachineInstrs.h"
#include "llvm/CodeGen/GlobalISel/LegalizerHelper.h"
#include "llvm/CodeGen/GlobalISel/LegalizerInfo.h"
#include "llvm/CodeGen/GlobalISel/LostDebugLocObserver.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineMemOperand.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/ValueTypes.h"
#include "llvm/CodeGenTypes/LowLevelType.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IntrinsicsM88k.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/TypeSize.h"
#include <cassert>
#include <cstdint>

using namespace llvm;
using namespace LegalityPredicates;

namespace {
/// True iff the given opcode is the same as the specified opcode.
inline LegalityPredicate opcodeIs(unsigned Opcode) {
  return [=](const LegalityQuery &Query) { return Query.Opcode == Opcode; };
}
} // namespace

M88kLegalizerInfo::M88kLegalizerInfo(const M88kSubtarget &ST) {
  using namespace TargetOpcode;
  const LLT S1 = LLT::scalar(1);
  const LLT S8 = LLT::scalar(8);
  const LLT S16 = LLT::scalar(16);
  const LLT S32 = LLT::scalar(32);
  const LLT S64 = LLT::scalar(64);
  const LLT S80 = LLT::scalar(80);
  const LLT S128 = LLT::scalar(128);
  const LLT V8S8 = LLT::fixed_vector(8, 8);
  const LLT V4S16 = LLT::fixed_vector(4, 16);
  const LLT V2S32 = LLT::fixed_vector(2, 32);
  const LLT P0 = LLT::pointer(0, 32);

  auto IsMC88110 = LegalityPredicate(
      [=, &ST](const LegalityQuery &Query) { return ST.isMC88110(); });

  getActionDefinitionsBuilder(G_PHI).legalFor({S64, S32, P0});
  getActionDefinitionsBuilder(G_SELECT).lower();
  getActionDefinitionsBuilder({G_IMPLICIT_DEF, G_FREEZE})
      .legalFor({S32, P0})
      .clampScalar(0, S32, S32);
  getActionDefinitionsBuilder(G_MERGE_VALUES).legalFor({{S64, S32}});
  getActionDefinitionsBuilder(G_UNMERGE_VALUES).legalFor({{S32, S64}});
  getActionDefinitionsBuilder(G_CONSTANT)
      .legalFor({S32, P0})
      .clampScalar(0, S32, S32);
  getActionDefinitionsBuilder(G_INTTOPTR)
      .legalFor({{P0, S32}})
      .minScalar(1, S32);
  getActionDefinitionsBuilder(G_PTRTOINT)
      .legalFor({{S32, P0}})
      .minScalar(0, S32);
  getActionDefinitionsBuilder(G_PTRMASK)
      .legalFor({{P0, S32}})
      .clampScalar(1, S32, S32);

  getActionDefinitionsBuilder({G_SEXT, G_ZEXT, G_ANYEXT})
      .legalFor({{S32, S16}, {S32, S8}, {S32, S1}})
      .clampScalar(0, S32, S32)
      .widenScalarToNextPow2(1, 32);
  getActionDefinitionsBuilder(G_SEXT_INREG).legalForTypeWithAnyImm({S32});
  getActionDefinitionsBuilder(G_TRUNC).alwaysLegal();
  getActionDefinitionsBuilder({G_SEXTLOAD, G_ZEXTLOAD})
      .legalForTypesWithMemDesc({{S32, P0, S8, 8}, {S32, P0, S16, 16}})
      .customIf(typePairAndMemDescInSet(/*TypeIdx0*/ 0, /*TypeIdx1*/ 1,
                                        /*MMOIdx*/ 0, {{S32, P0, S16, 8}}))
      .clampScalar(0, S32, S32)
      .lower();
  getActionDefinitionsBuilder({G_LOAD, G_STORE})
      .legalForTypesWithMemDesc({{S32, P0, S8, 8},
                                 {S32, P0, S16, 16},
                                 {S32, P0, S32, 32},
                                 {P0, P0, P0, 32},
                                 {S64, P0, S64, 64}})
      // Truncating stores are legal.
      .legalIf(all(typePairAndMemDescInSet(
                       /*TypeIdx0*/ 0, /*TypeIdx1*/ 1,
                       /*MMOIdx*/ 0, {{S32, P0, S8, 8}, {S32, P0, S16, 16}}),
                   opcodeIs(G_STORE)))
      // 80 bit floats have a mem size of 128 bit.
      .legalIf(
          all(typePairAndMemDescInSet(/*TypeIdx0*/ 0, /*TypeIdx1*/ 1,
                                      /*MMOIdx*/ 0, {{S80, P0, S128, 128}}),
              IsMC88110))
      .clampScalar(0, S32, S32)
      // Custom action if unaligned load/store.
      // TODO Does not handle f80 type.
      .customIf([=](const LegalityQuery &Query) {
        if (!Query.Types[0].isScalar() || Query.Types[1] != P0)
          return false;

        llvm::TypeSize Size = Query.Types[0].getSizeInBits();
        llvm::TypeSize QueryMemSize =
            Query.MMODescrs[0].MemoryTy.getSizeInBits();
        assert(QueryMemSize <= Size && "Scalar can't hold MemSize");

        if (Size > 32 || QueryMemSize > 32)
          return false;

        if (!isPowerOf2_64(Size))
          return false;

        if (!isPowerOf2_64(QueryMemSize))
          return false;

        return QueryMemSize > Query.MMODescrs[0].AlignInBits;
      })
      .unsupportedIfMemSizeNotPow2()
      .lower();
  getActionDefinitionsBuilder(G_PTR_ADD)
      .legalFor({{P0, S32}})
      .clampScalar(1, S32, S32);
  getActionDefinitionsBuilder({G_ADD, G_SUB})
      .legalFor({S32})
      .legalIf(all(typeInSet(0, {V8S8, V4S16, V2S32}), IsMC88110))
      .clampScalar(0, S32, S32);
  getActionDefinitionsBuilder({G_UADDO, G_UADDE, G_USUBO, G_USUBE})
      .legalFor({{S32, S32}})
      .clampScalar(0, S32, S32)
      .clampScalar(1, S32, S32)
      .lower();
  getActionDefinitionsBuilder({G_SADDO, G_SADDE, G_SSUBO, G_SSUBE}).lower();
  getActionDefinitionsBuilder({G_MUL, G_UDIV})
      .legalFor({S32})
      .customIf(all(typeInSet(0, {S64}), IsMC88110))
      .libcallFor({S64})
      .clampScalar(0, S32, S64);
  getActionDefinitionsBuilder(G_SDIV)
      .legalFor({S32})
      .libcallFor({S64})
      .clampScalar(0, S32, S64);
  getActionDefinitionsBuilder({G_SREM, G_UREM})
      .lowerFor({S32})
      .libcallFor({S64});
  getActionDefinitionsBuilder({G_UMULH, G_SMULH}).lower();
  getActionDefinitionsBuilder({G_AND, G_OR, G_XOR})
      .legalFor({S32})
      .clampScalar(0, S32, S32);
  getActionDefinitionsBuilder({G_SBFX, G_UBFX})
      .legalFor({{S32, S32}})
      .clampScalar(0, S32, S32);
  getActionDefinitionsBuilder({G_SHL, G_LSHR, G_ASHR})
      .legalFor({{S32, S32}})
      .clampScalar(0, S32, S32)
      .clampScalar(1, S32, S32);
  getActionDefinitionsBuilder(G_ROTR).legalFor({{S32}, {S32}});
  getActionDefinitionsBuilder({G_ROTL, G_FSHL, G_FSHR}).lower();
  getActionDefinitionsBuilder(G_CTLZ)
    .customFor({{S32}, {S32}});
  getActionDefinitionsBuilder(G_CTLZ_ZERO_UNDEF)
      .legalFor({{S32}, {S32}});
  getActionDefinitionsBuilder({G_CTTZ, G_CTTZ_ZERO_UNDEF, G_CTPOP}).lower();
  getActionDefinitionsBuilder({G_SMAX, G_UMAX, G_SMIN, G_UMIN}).lower();

  getActionDefinitionsBuilder({G_MEMCPY, G_MEMMOVE, G_MEMSET}).libcall();

  getActionDefinitionsBuilder(G_ICMP)
      .legalForCartesianProduct({S1}, {S32, P0})
      .clampScalar(1, S32, S32);
  getActionDefinitionsBuilder(G_BRCOND).legalFor({S1});
  getActionDefinitionsBuilder(G_BRJT).legalFor({{P0, S32}});
  getActionDefinitionsBuilder(G_BRINDIRECT).legalFor({P0});
  getActionDefinitionsBuilder(G_JUMP_TABLE).legalFor({P0});

  getActionDefinitionsBuilder(G_FRAME_INDEX).legalFor({P0});
  getActionDefinitionsBuilder(G_GLOBAL_VALUE).legalFor({P0});
  getActionDefinitionsBuilder(G_VASTART).legalFor({P0});

  getActionDefinitionsBuilder(G_FCONSTANT).customFor({S32, S64});
  getActionDefinitionsBuilder({G_FADD, G_FSUB, G_FMUL, G_FDIV})
      .legalFor({S32, S64})
      .legalIf(all(typeInSet(0, {S80}), IsMC88110));
  getActionDefinitionsBuilder({G_FNEG, G_FABS}).lower();
  getActionDefinitionsBuilder(G_FPEXT).legalFor({{S64, S32}});
  getActionDefinitionsBuilder(G_FPTRUNC).legalFor({{S32, S64}});

  getActionDefinitionsBuilder(
      {G_FCOS, G_FSIN, G_FLOG10, G_FLOG, G_FLOG2, G_FEXP, G_FEXP2, G_FPOW})
      .minScalar(0, S32)
      .libcallFor({S32, S64});
  getActionDefinitionsBuilder(G_FSQRT)
      .minScalar(0, S32)
      .legalIf(all(typeInSet(0, {S32, S64}), IsMC88110))
      .libcallFor({S32, S64});

  // FP to int conversion instructions
  getActionDefinitionsBuilder(G_FPTOSI)
      .legalForCartesianProduct({S32}, {S64, S32})
      .libcallForCartesianProduct({S64}, {S64, S32})
      .minScalar(0, S32);

  getActionDefinitionsBuilder(G_FPTOUI)
      .libcallForCartesianProduct({S64}, {S64, S32})
      .lowerForCartesianProduct({S32}, {S64, S32})
      .minScalar(0, S32);

  // Int to FP conversion instructions
  getActionDefinitionsBuilder(G_SITOFP)
      .legalForCartesianProduct({S64, S32}, {S32})
      .libcallForCartesianProduct({S64, S32}, {S64})
      .minScalar(1, S32);
  getActionDefinitionsBuilder(G_UITOFP)
      //.libcallForCartesianProduct({S64, S32}, {S64})
      // It is not really legal - it will be lowered later.
      .legalForCartesianProduct({S64, S32}, {S32})
      .minScalar(1, S32);
  getLegacyLegalizerInfo().computeTables();
}

bool M88kLegalizerInfo::legalizeCustom(
    LegalizerHelper &Helper, MachineInstr &MI,
    LostDebugLocObserver &LocObserver) const {
  using namespace TargetOpcode;

  MachineIRBuilder &MIRBuilder = Helper.MIRBuilder;
  MachineRegisterInfo &MRI = *MIRBuilder.getMRI();

  const LLT S32 = LLT::scalar(32);
  const LLT S64 = LLT::scalar(64);
  const LLT P0 = LLT::pointer(0, 32);

  switch (MI.getOpcode()) {
  case G_SEXTLOAD:
  case G_ZEXTLOAD:
  case G_LOAD: {
    // Break an unaligned load into several aligned loads, and combine the
    // results.
    //
    GLoadStore *LdStMI = llvm::cast<GLoadStore>(&MI);
    MachineMemOperand *MMO = *LdStMI->memoperands_begin();
    MachineFunction &MF = MIRBuilder.getMF();

    // Calculate the number of parts which must be loaded.
    // E.g. MemSize = 4, Align = 2 => 2 parts of size 2.
    // There can be only 2 cases: 2 or 4 parts.
    TypeSize MemSize = LdStMI->getMemSize().getValue();
    uint64_t ChunkSize = 1ULL << Log2(MMO->getAlign());

    uint64_t Parts = MemSize / ChunkSize;
    uint64_t Offset = 0;

    Register DstReg = MI.getOperand(0).getReg();
    Register AdrReg = MI.getOperand(1).getReg();

    auto ChunkAmt = MIRBuilder.buildConstant(S32, ChunkSize);
    auto ShiftAmt = MIRBuilder.buildConstant(S32, 8 * ChunkSize);

    // Increments AdrReg by ChunkSize, and loads the value.
    // Alos updates Offset.
    auto IncAndload = [&](Register &AdrReg) -> Register {
      Offset += ChunkSize;
      Register IncAdrReg = MRI.createGenericVirtualRegister(P0);
      MIRBuilder.buildPtrAdd(IncAdrReg, AdrReg, ChunkAmt);
      Register Val = MRI.createGenericVirtualRegister(S32);
      MIRBuilder.buildLoadInstr(
          ChunkSize == 4 ? G_LOAD : G_ZEXTLOAD, Val, IncAdrReg,
          *MF.getMachineMemOperand(MMO, Offset, ChunkSize));
      AdrReg = IncAdrReg;
      return Val;
    };
    auto Combine = [&](Register ValHi, Register ValLo,
                       Register DstReg) -> Register {
      Register TmpReg = MRI.createGenericVirtualRegister(S32);
      MIRBuilder.buildShl(TmpReg, ValHi, ShiftAmt);
      MIRBuilder.buildOr(DstReg, TmpReg, ValLo);
      return DstReg;
    };

    Register ValReg = MRI.createGenericVirtualRegister(S32);
    MIRBuilder.buildLoadInstr(
        ChunkSize == 4
            ? G_LOAD
            : (MI.getOpcode() == G_SEXTLOAD ? G_SEXTLOAD : G_ZEXTLOAD),
        ValReg, AdrReg, *MF.getMachineMemOperand(MMO, Offset, ChunkSize));

    if (Parts > 2) {
      Register NextReg = IncAndload(AdrReg);
      ValReg = Combine(ValReg, NextReg, MRI.createGenericVirtualRegister(S32));

      NextReg = IncAndload(AdrReg);
      ValReg = Combine(ValReg, NextReg, MRI.createGenericVirtualRegister(S32));
    }

    Register LastReg = IncAndload(AdrReg);
    Combine(ValReg, LastReg, DstReg);

    MI.eraseFromParent();
    break;
  }
  case G_STORE: {
    // Break an unaligned store into several aligned stores.
    GStore *StoreMI = llvm::cast<GStore>(&MI);
    MachineMemOperand *MMO = *StoreMI->memoperands_begin();
    MachineFunction &MF = MIRBuilder.getMF();

    // Calculate the number of parts which must be stored.
    // E.g. MemSize = 4, Align = 2 => 2 parts of size 2.
    // There can be only 2 cases: 2 or 4 parts.
    TypeSize MemSize = StoreMI->getMemSize().getValue();
    uint64_t ChunkSize = 1ULL << Log2(MMO->getAlign());

    uint64_t Parts = MemSize / ChunkSize;
    uint64_t Offset = 0;
    uint64_t Part = Parts - 1;

    Register ValReg = StoreMI->getValueReg();
    Register AdrReg = StoreMI->getPointerReg();

    auto ChunkAmt = MIRBuilder.buildConstant(S32, ChunkSize);

    // Stores a part of ValReg.
    auto Store = [&]() {
      Register TmpReg;
      if (Part) {
        TmpReg = MRI.createGenericVirtualRegister(S32);
        MIRBuilder.buildLShr(
            TmpReg, ValReg,
            MIRBuilder.buildConstant(S32, Part * 8 * ChunkSize));
      } else
        TmpReg = ValReg;
      MIRBuilder.buildStore(TmpReg, AdrReg,
                            *MF.getMachineMemOperand(MMO, Offset, ChunkSize));
    };

    // Increments AdrReg by ChunkSize, and store the next part of the value.
    // Alsa updates Offset and Part.
    auto StoreNext = [&]() {
      Offset += ChunkSize;
      Part -= 1;
      Register IncAdrReg = MRI.createGenericVirtualRegister(P0);
      MIRBuilder.buildPtrAdd(IncAdrReg, AdrReg, ChunkAmt);
      AdrReg = IncAdrReg;
      Store();
    };

    Store();
    StoreNext();
    if (Parts > 2) {
      StoreNext();
      StoreNext();
    }

    MI.eraseFromParent();
    break;
  }
  case G_FCONSTANT: {
    LLVMContext &Ctx = MIRBuilder.getMF().getFunction().getContext();
    // Convert to integer constants, while preserving the binary representation.
    auto AsInteger =
        MI.getOperand(1).getFPImm()->getValueAPF().bitcastToAPInt();
    MIRBuilder.buildConstant(MI.getOperand(0),
                             *ConstantInt::get(Ctx, AsInteger));
    MI.eraseFromParent();
    break;
  }
  case G_MUL: {
    // MC88110 only: 32bit multiplication with 64bit result.
    Register DstReg = MI.getOperand(0).getReg();
    MachineInstr *Src1I = getDefIgnoringCopies(MI.getOperand(1).getReg(), MRI);
    MachineInstr *Src2I = getDefIgnoringCopies(MI.getOperand(2).getReg(), MRI);
    unsigned Opc1 = Src1I->getOpcode();
    unsigned Opc2 = Src2I->getOpcode();

    auto Libcall = [&]() -> bool {
      return LegalizerHelper::UnableToLegalize !=
             Helper.libcall(MI, LocObserver);
    };

    // Check if the multiplicants are blown-up 32 bit values. If yes then the
    // multiplication is legal.
    if (Opc1 == G_MERGE_VALUES && Opc2 == G_MERGE_VALUES) {
      auto C1 = getIConstantVRegValWithLookThrough(
          Src1I->getOperand(1).getReg(), MRI);
      auto C2 = getIConstantVRegValWithLookThrough(
          Src1I->getOperand(1).getReg(), MRI);
      if (C1 && C1->Value.isZero() && C2 && C2->Value.isZero())
        return true;
      return Libcall();
    }

    // Try to legalize the instruction.
    if (!((Opc1 == G_ZEXT || Opc1 == G_SEXT) &&
          (Opc2 == G_ZEXT || Opc2 == G_SEXT)))
      return Libcall();
    if (MRI.getType(Src1I->getOperand(1).getReg()) != S32 ||
        MRI.getType(Src2I->getOperand(1).getReg()) != S32)
      return Libcall();
    auto Zero = MIRBuilder.buildConstant(S32, 0);
    auto Mult1 = MIRBuilder.buildMergeLikeInstr(
        S64, {Zero.getReg(0), Src1I->getOperand(1).getReg()});
    auto Mult2 = MIRBuilder.buildMergeLikeInstr(
        S64, {Zero.getReg(0), Src2I->getOperand(1).getReg()});
    MIRBuilder.buildMul(DstReg, Mult1, Mult2, MI.getFlags());
    MI.eraseFromParent();
    break;
  }
  case G_UDIV: {
    // MC88110 only: 64bit division with 32bit divisor.
    Register DstReg = MI.getOperand(0).getReg();
    Register Src1Reg = MI.getOperand(1).getReg();
    MachineInstr *Src2I = getDefIgnoringCopies(MI.getOperand(2).getReg(), MRI);
    unsigned Opc2 = Src2I->getOpcode();

    auto Libcall = [&]() -> bool {
      return LegalizerHelper::UnableToLegalize !=
             Helper.libcall(MI, LocObserver);
    };

    // Check if the divisor is a blown-up 32 bit value. If yes then the division
    // is legal.
    if (Opc2 == G_MERGE_VALUES) {
      auto Cst = getIConstantVRegValWithLookThrough(
          Src2I->getOperand(1).getReg(), MRI);
      if (Cst && Cst->Value.isZero())
        return true;
      return Libcall();
    }

    // Try to legalize the instruction.
    if (Opc2 != G_ZEXT)
      return Libcall();
    if (MRI.getType(Src2I->getOperand(1).getReg()) != S32)
      return Libcall();
    auto Zero = MIRBuilder.buildConstant(S32, 0);
    auto Div = MIRBuilder.buildMergeLikeInstr(
        S64, {Zero.getReg(0), Src2I->getOperand(1).getReg()});
    MIRBuilder.buildInstr(G_UDIV, {DstReg}, {Src1Reg, Div.getReg(0)},
                          MI.getFlags());
    MI.eraseFromParent();
    break;
  }
  case G_CTLZ: {
    // The instruction
    //   %7:_(s32) = G_CTLZ %0(s32)
    // is lowered to:
    //   %1:_(s32) = G_INTRINSIC intrinsic(@llvm.m88k.ff1), %0(s32)
    //   %2:_(s32) = G_CONSTANT i32 31
    //   %3:_(s32) = G_CONSTANT i32 0
    //   %4:_(s32), %3:_(s32) = G_USUBO %2, %1
    //   %5:_(s32) = G_AND %2, %4
    //   %6:_(s32), %3:_(s32) = G_UADDE %5, %3, %4
    Register Dst = MI.getOperand(0).getReg();

    auto FF1 =
        MIRBuilder.buildIntrinsic(Intrinsic::m88k_ff1, {S32}, false, false);
    FF1.addUse(MI.getOperand(1).getReg());
    Register USub = MRI.createGenericVirtualRegister(S32);
    Register Carry = MRI.createGenericVirtualRegister(S32);
    Register Dead = MRI.createGenericVirtualRegister(S32);
    auto Const31 = MIRBuilder.buildConstant(S32, 31);
    auto Const0 = MIRBuilder.buildConstant(S32, 0);
    MIRBuilder.buildUSubo(USub, Carry, Const31, FF1);
    auto And = MIRBuilder.buildAnd(S32, USub, Const31);
    MIRBuilder.buildUAdde(Dst, Dead, And, Const0, Carry);
    MI.eraseFromParent();
    break;
  }
  default:
    return false;
  }

  return true;
}