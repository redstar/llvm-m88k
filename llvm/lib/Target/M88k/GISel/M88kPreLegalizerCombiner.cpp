//=== M88kPreLegalizer.cpp --------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Pre-legalization lowering for instructions.
///
/// This is used to offload pattern matching from the selector.
///
/// For example, this combiner will notice that a G_OR with a shifted mask as
/// argumnet is actually MAKrwo.
///
/// General optimization combines should be handled by either the
/// M88kPostLegalizerCombiner or the M88kPreLegalizerCombiner.
///
//===----------------------------------------------------------------------===//

#include "M88kSubtarget.h"
#include "llvm/CodeGen/GlobalISel/CSEInfo.h"
#include "llvm/CodeGen/GlobalISel/Combiner.h"
#include "llvm/CodeGen/GlobalISel/CombinerHelper.h"
#include "llvm/CodeGen/GlobalISel/CombinerInfo.h"
#include "llvm/CodeGen/GlobalISel/GIMatchTableExecutor.h"
#include "llvm/CodeGen/GlobalISel/GIMatchTableExecutorImpl.h"
#include "llvm/CodeGen/GlobalISel/GISelKnownBits.h"
#include "llvm/CodeGen/GlobalISel/MIPatternMatch.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/CodeGenTypes/LowLevelType.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include <cassert>
#include <cstdint>
#include <functional>

#define GET_GICOMBINER_DEPS
#include "M88kGenPreLegalizeGICombiner.inc"
#undef GET_GICOMBINER_DEPS

#define DEBUG_TYPE "m88k-prelegalizer-combiner"

using namespace llvm;
using namespace MIPatternMatch;

namespace {
#define GET_GICOMBINER_TYPES
#include "M88kGenPreLegalizeGICombiner.inc"
#undef GET_GICOMBINER_TYPES

class M88kPreLegalizerCombinerImpl : public Combiner {
protected:
  mutable CombinerHelper Helper;
  const M88kPreLegalizerCombinerImplRuleConfig &RuleConfig;
  const M88kSubtarget &STI;

public:
  M88kPreLegalizerCombinerImpl(
      MachineFunction &MF, CombinerInfo &CInfo, const TargetPassConfig *TPC,
      GISelKnownBits &KB, GISelCSEInfo *CSEInfo,
      const M88kPreLegalizerCombinerImplRuleConfig &RuleConfig,
      const M88kSubtarget &STI);

  static const char *getName() { return "M88kPostLegalizerCombiner"; }

  bool tryCombineAll(MachineInstr &I) const override;

private:
  bool matchBitfieldExtractFromAndAShr(
      MachineInstr &MI, MachineRegisterInfo &MRI,
      std::function<void(MachineIRBuilder &)> &MatchInfo) const;

#define GET_GICOMBINER_CLASS_MEMBERS
#include "M88kGenPreLegalizeGICombiner.inc"
#undef GET_GICOMBINER_CLASS_MEMBERS
};
} // namespace

/// Form a G_UBFX from "(a sra b) & mask", where b and mask are constants.
/// This is similar to CombinerHelper::matchBitfieldExtractFromAnd(), but
/// matches an arithmetic shift right instructions (instead of locigal shift
/// right). However, it requires more reasoning about the value.
bool M88kPreLegalizerCombinerImpl::matchBitfieldExtractFromAndAShr(
    MachineInstr &MI, MachineRegisterInfo &MRI,
    std::function<void(MachineIRBuilder &)> &MatchInfo) const {
  assert(MI.getOpcode() == TargetOpcode::G_AND);
  Register Dst = MI.getOperand(0).getReg();
  LLT Ty = MRI.getType(Dst);
  LLT ExtractTy = Helper.getTargetLowering().getPreferredShiftAmountTy(Ty);
  LegalizerInfo *LI = nullptr; // TODO
  if (LI && !LI->isLegalOrCustom({TargetOpcode::G_UBFX, {Ty, ExtractTy}}))
    return false;

  int64_t AndImm, ShrAmt;
  Register ShiftSrc;
  const unsigned Size = Ty.getScalarSizeInBits();
  if (!mi_match(MI.getOperand(0).getReg(), MRI,
                m_GAnd(m_OneNonDBGUse(m_GAShr(m_Reg(ShiftSrc), m_ICst(ShrAmt))),
                       m_ICst(AndImm))))
    return false;

  // The mask is a mask of the low bits iff imm & (imm+1) == 0.
  auto MaybeMask = static_cast<uint64_t>(AndImm);
  if (MaybeMask & (MaybeMask + 1))
    return false;

  // ShrAmt must fit within the register.
  if (static_cast<uint64_t>(ShrAmt) >= Size)
    return false;

  uint64_t Width = APInt(Size, AndImm).countTrailingOnes();

  // ShrAmt plus the width of the mask must not be greater than register,
  // because then at most the MSB of ShiftSrc is part of the resulting value.
  if (static_cast<uint64_t>(ShrAmt) + Width >= Size &&
      !Helper.getKnownBits()->signBitIsZero(ShiftSrc))
    return false;

  MatchInfo = [=](MachineIRBuilder &B) {
    auto WidthCst = B.buildConstant(ExtractTy, Width);
    auto LSBCst = B.buildConstant(ExtractTy, ShrAmt);
    B.buildInstr(TargetOpcode::G_UBFX, {Dst}, {ShiftSrc, LSBCst, WidthCst});
  };
  return true;
}

#define GET_GICOMBINER_IMPL
#include "M88kGenPreLegalizeGICombiner.inc"
#undef GET_GICOMBINER_IMPL

namespace {
M88kPreLegalizerCombinerImpl::M88kPreLegalizerCombinerImpl(
    MachineFunction &MF, CombinerInfo &CInfo, const TargetPassConfig *TPC,
    GISelKnownBits &KB, GISelCSEInfo *CSEInfo,
    const M88kPreLegalizerCombinerImplRuleConfig &RuleConfig,
    const M88kSubtarget &STI)
    : Combiner(MF, CInfo, TPC, &KB, CSEInfo),
      Helper(Observer, B, /*IsPreLegalize*/ true, &KB), RuleConfig(RuleConfig),
      STI(STI),
#define GET_GICOMBINER_CONSTRUCTOR_INITS
#include "M88kGenPreLegalizeGICombiner.inc"
#undef GET_GICOMBINER_CONSTRUCTOR_INITS
{
}

// Pass boilerplate
// ================

class M88kPreLegalizerCombiner : public MachineFunctionPass {
  M88kPreLegalizerCombinerImplRuleConfig RuleConfig;

public:
  static char ID;

  M88kPreLegalizerCombiner();

  StringRef getPassName() const override { return "M88kPreLegalizerCombiner"; }

  bool runOnMachineFunction(MachineFunction &MF) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override;
};
} // end anonymous namespace

void M88kPreLegalizerCombiner::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<TargetPassConfig>();
  AU.setPreservesCFG();
  getSelectionDAGFallbackAnalysisUsage(AU);
  AU.addRequired<GISelKnownBitsAnalysis>();
  AU.addPreserved<GISelKnownBitsAnalysis>();
  AU.addRequired<MachineDominatorTreeWrapperPass>();
  AU.addPreserved<MachineDominatorTreeWrapperPass>();
  AU.addRequired<GISelCSEAnalysisWrapperPass>();
  AU.addPreserved<GISelCSEAnalysisWrapperPass>();
  MachineFunctionPass::getAnalysisUsage(AU);
}

M88kPreLegalizerCombiner::M88kPreLegalizerCombiner() : MachineFunctionPass(ID) {
  initializeM88kPreLegalizerCombinerPass(*PassRegistry::getPassRegistry());
}

bool M88kPreLegalizerCombiner::runOnMachineFunction(MachineFunction &MF) {
  if (MF.getProperties().hasProperty(
          MachineFunctionProperties::Property::FailedISel))
    return false;
  auto &TPC = getAnalysis<TargetPassConfig>();

  const Function &F = MF.getFunction();
  GISelKnownBits *KB = &getAnalysis<GISelKnownBitsAnalysis>().get(MF);

  const M88kSubtarget &ST = MF.getSubtarget<M88kSubtarget>();

  CombinerInfo CInfo(/*AllowIllegalOps*/ true, /*ShouldLegalizeIllegal*/ false,
                     /*LegalizerInfo*/ nullptr, /*EnableOpt*/ false,
                     F.hasOptSize(), F.hasMinSize());
  M88kPreLegalizerCombinerImpl Impl(MF, CInfo, &TPC, *KB,
                                    /*CSEInfo*/ nullptr, RuleConfig, ST);
  return Impl.combineMachineInstrs();
}

char M88kPreLegalizerCombiner::ID = 0;
INITIALIZE_PASS_BEGIN(M88kPreLegalizerCombiner, DEBUG_TYPE,
                      "Combine M88k machine instrs before legalization", false,
                      false)
INITIALIZE_PASS_DEPENDENCY(TargetPassConfig)
INITIALIZE_PASS_DEPENDENCY(GISelKnownBitsAnalysis)
INITIALIZE_PASS_DEPENDENCY(GISelCSEAnalysisWrapperPass)
INITIALIZE_PASS_END(M88kPreLegalizerCombiner, DEBUG_TYPE,
                    "Combine M88k machine instrs before legalization", false,
                    false)

namespace llvm {
FunctionPass *createM88kPreLegalizerCombiner() {
  return new M88kPreLegalizerCombiner();
}
} // end namespace llvm
