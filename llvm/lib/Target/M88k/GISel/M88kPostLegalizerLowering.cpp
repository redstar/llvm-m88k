//=== M88kPostLegalizerLowering.cpp -----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Post-legalization lowering for instructions.
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

#include "GISel/M88kLegalizerInfo.h"
#include "M88kTargetMachine.h"
#include "llvm/CodeGen/GlobalISel/CSEInfo.h"
#include "llvm/CodeGen/GlobalISel/Combiner.h"
#include "llvm/CodeGen/GlobalISel/CombinerHelper.h"
#include "llvm/CodeGen/GlobalISel/CombinerInfo.h"
#include "llvm/CodeGen/GlobalISel/GIMatchTableExecutor.h"
#include "llvm/CodeGen/GlobalISel/GIMatchTableExecutorImpl.h"
#include "llvm/CodeGen/GlobalISel/GISelChangeObserver.h"
#include "llvm/CodeGen/GlobalISel/GISelKnownBits.h"
#include "llvm/CodeGen/GlobalISel/GenericMachineInstrs.h"
#include "llvm/CodeGen/GlobalISel/MIPatternMatch.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/Debug.h"

#define GET_GICOMBINER_DEPS
#include "M88kGenPostLegalizeGILowering.inc"
#undef GET_GICOMBINER_DEPS

#define DEBUG_TYPE "M88K-postlegalizer-lowering"

using namespace llvm;
using namespace MIPatternMatch;

namespace {
#define GET_GICOMBINER_TYPES
#include "M88kGenPostLegalizeGILowering.inc"
#undef GET_GICOMBINER_TYPES

// Creates a new MachineBasicBlock. The new block is inserted after/before the
// basic block MBB, depending on flag IsSucc.
MachineBasicBlock *createMBB(MachineBasicBlock *MBB, bool IsSucc = true) {
  // Create the new basic block.
  MachineFunction *MF = MBB->getParent();
  MachineBasicBlock *NewMBB = MF->CreateMachineBasicBlock(MBB->getBasicBlock());

  if (IsSucc) {
    MachineFunction::iterator BBI(MBB);
    MF->insert(++BBI, NewMBB);
    MBB->addSuccessor(NewMBB);
  } else {
    MachineFunction::iterator BBI(MBB);
    MF->insert(BBI, NewMBB);
    NewMBB->addSuccessor(MBB);
  }

  return NewMBB;
}

// The instruction G_SDIV is lowered into G_UDIV. This is done by making both
// operands non-negative, and correcting the sign of the result. All 4 cases
// need to be considered. The code is a bit lengthy, but not complicated.
bool applySDivtoUDiv(GISelChangeObserver &Observer, MachineInstr &MI,
                     MachineRegisterInfo &MRI, MachineIRBuilder &MIB,
                     GISelKnownBits *KB) {
  const LLT S1 = LLT::scalar(1);
  const LLT S32 = LLT::scalar(32);

  Register QuotientReg = MI.getOperand(0).getReg();
  Register NumeratorReg = MI.getOperand(1).getReg();
  Register DenominatorReg = MI.getOperand(2).getReg();

  // This should not happen as the instructions are legalized.
  if (MRI.getType(QuotientReg) != S32 || MRI.getType(NumeratorReg) != S32 ||
      MRI.getType(DenominatorReg) != S32)
    return false;

  MIB.setInstrAndDebugLoc(MI);

  // Analyse numerator and denominator.
  APInt Mask = APInt::getSignMask(32);
  KnownBits NumeratorBits = KB->getKnownBits(NumeratorReg);
  KnownBits DenominatorBits = KB->getKnownBits(DenominatorReg);
  bool NumSignBitIsZero = Mask.isSubsetOf(NumeratorBits.Zero);
  bool NumSignBitIsOne = Mask.isSubsetOf(NumeratorBits.One);
  bool DenomSignBitIsZero = Mask.isSubsetOf(DenominatorBits.Zero);
  bool DenomSignBitIsOne = Mask.isSubsetOf(DenominatorBits.One);

  // First handle the trivial cases that all sign bits are known.
  if (NumSignBitIsZero && DenomSignBitIsZero) {
    MIB.setInstrAndDebugLoc(MI);
    MIB.buildInstr(TargetOpcode::G_UDIV, {QuotientReg},
                   {NumeratorReg, DenominatorReg});
    MI.eraseFromParent();
    return true;
  } else if (NumSignBitIsOne && DenomSignBitIsOne) {
    MIB.setInstrAndDebugLoc(MI);
    auto NegNum = MIB.buildNeg(S32, NumeratorReg);
    auto NegDenom = MIB.buildNeg(S32, DenominatorReg);
    MIB.buildInstr(TargetOpcode::G_UDIV, {QuotientReg}, {NegNum, NegDenom});
    MI.eraseFromParent();
    return true;
  } else if ((NumSignBitIsZero && DenomSignBitIsOne) ||
             (NumSignBitIsOne && DenomSignBitIsZero)) {
    MIB.setInstrAndDebugLoc(MI);
    auto Div = MIB.buildInstr(
        TargetOpcode::G_UDIV, {S32},
        {NumSignBitIsOne ? MIB.buildNeg(S32, NumeratorReg).getReg(0)
                         : NumeratorReg,
         DenomSignBitIsOne ? MIB.buildNeg(S32, DenominatorReg).getReg(0)
                           : DenominatorReg});
    MIB.buildNeg(QuotientReg, Div);
    MI.eraseFromParent();
    return true;
  }

  // Define helper to insert G_UDIV into a machine basic block.
  auto InsertUDiv = [&](MachineBasicBlock *MBB, MachineInstrBuilder &PHI,
                        bool NegNumerator, bool NegDenominator) {
    MachineIRBuilder MIB(*MBB, MBB->end());
    MIB.setChangeObserver(Observer);
    MachineBasicBlock *TargetMBB = PHI.getInstr()->getParent();
    auto Div =
        MIB.buildInstr(TargetOpcode::G_UDIV, {S32},
                       {NegNumerator ? MIB.buildNeg(S32, NumeratorReg).getReg(0)
                                     : NumeratorReg,
                        DenominatorReg});
    MIB.buildBr(*TargetMBB);
    MBB->addSuccessor(TargetMBB);
    PHI.addReg(Div.getReg(0)).addMBB(MBB);
  };
  // Define helper to insert conditional branch at end of machine basic block.
  auto InsertBrCond = [&](MachineBasicBlock *MBB, Register Reg) {
    MachineIRBuilder MIB(*MBB, MBB->end());
    MIB.setChangeObserver(Observer);
    MachineBasicBlock *BBLT0 = createMBB(MBB);
    MachineBasicBlock *BBGE0 = createMBB(MBB);
    auto Zero = MIB.buildConstant(S32, 0);
    MIB.buildBrCond(MIB.buildICmp(CmpInst::ICMP_SLT, S1, Reg, Zero), *BBLT0);
    MIB.buildBr(*BBGE0);
    return std::make_tuple(BBLT0, BBGE0);
  };

  // The sign of at least one instruction is not known. For the end of the
  // computation, there are always 2 cases:
  // - G_UDIV computes the final result
  // - the result of G_UDIV needs to be negated
  // This is handled by to tails: one for the final result, and one for the
  // result which still must be negated.

  // First split the current basic block. Move all instructions after MI into
  // the new block.
  MachineBasicBlock *MBB = MI.getParent();
  MachineBasicBlock *TailBB = MBB->splitAt(MI, false);
  MBB->removeSuccessor(TailBB);

  // Create empty G_PHI instruction in the new tail block.
  MIB.setInsertPt(*TailBB, TailBB->begin());
  MachineInstrBuilder PHI =
      MIB.buildInstr(TargetOpcode::G_PHI, {QuotientReg}, {});

  // Create basic block for negated result.
  MachineBasicBlock *NegTailBB = createMBB(TailBB, false);
  MIB.setInsertPt(*NegTailBB, NegTailBB->end());
  MachineInstrBuilder NegPHI = MIB.buildInstr(TargetOpcode::G_PHI, {S32}, {});
  auto NegResult = MIB.buildNeg(S32, NegPHI);
  MIB.buildBr(*TailBB);
  PHI.addReg(NegResult.getReg(0)).addMBB(NegTailBB);

  // Insert branch if denominator is < 0 and sign bit is unknown.
  MachineBasicBlock *BBDenomLT0 = nullptr;
  MachineBasicBlock *BBDenomGE0 = nullptr;
  if (!DenomSignBitIsZero && !DenomSignBitIsOne)
    std::tie(BBDenomLT0, BBDenomGE0) = InsertBrCond(MBB, DenominatorReg);
  else if (DenomSignBitIsZero)
    BBDenomGE0 = MBB;
  else if (DenomSignBitIsOne)
    BBDenomLT0 = MBB;
  else
    llvm_unreachable("Impossible case reached");

  // Insert branch if numerator is < 0 and sign bit is unknown.
  MachineBasicBlock *BBNumGE0DenomGE0 = nullptr;
  MachineBasicBlock *BBNumLT0DenomGE0 = nullptr;
  if (BBDenomGE0) {
    if (!NumSignBitIsZero && !NumSignBitIsOne)
      std::tie(BBNumLT0DenomGE0, BBNumGE0DenomGE0) =
          InsertBrCond(BBDenomGE0, NumeratorReg);
    else if (NumSignBitIsZero)
      BBNumGE0DenomGE0 = BBDenomGE0;
    else if (NumSignBitIsOne)
      BBNumLT0DenomGE0 = BBDenomGE0;
    else
      llvm_unreachable("Impossible case reached");
  }

  // Compute quotient: numerator >= 0, denominator >= 0.
  if (BBNumGE0DenomGE0)
    InsertUDiv(BBNumGE0DenomGE0, PHI, /*NegNumerator=*/false,
               /*NegDenominator=*/false);

  // Compute quotient: numerator < 0, denominator >= 0.
  if (BBNumLT0DenomGE0)
    InsertUDiv(BBNumLT0DenomGE0, NegPHI, /*NegNumerator=*/true,
               /*NegDenominator=*/false);

  // Negate denominator & branch if numerator is < 0. Denominator is <= 0.
  MachineBasicBlock *BBNumGE0DenomLT0 = nullptr;
  MachineBasicBlock *BBNumLT0DenomLT0 = nullptr;
  if (BBDenomLT0) {
    MIB.setInsertPt(*BBDenomLT0, BBDenomLT0->end());
    auto Neg = MIB.buildNeg(S32, DenominatorReg);
    DenominatorReg = Neg.getReg(0);
    if (!NumSignBitIsZero && !NumSignBitIsOne)
      std::tie(BBNumLT0DenomLT0, BBNumGE0DenomLT0) =
          InsertBrCond(BBDenomLT0, NumeratorReg);
    else if (NumSignBitIsZero)
      BBNumGE0DenomLT0 = BBDenomGE0;
    else if (NumSignBitIsOne)
      BBNumLT0DenomLT0 = BBDenomGE0;
    else
      llvm_unreachable("Impossible case reached");
  }

  // Compute quotient: numerator >= 0, denominator < 0.
  if (BBNumGE0DenomLT0)
    InsertUDiv(BBNumGE0DenomLT0, NegPHI, /*NegNumerator=*/false,
               /*NegDenominator=*/true);

  // Compute quotient: numerator < 0, denominator < 0.
  if (BBNumLT0DenomLT0)
    InsertUDiv(BBNumLT0DenomLT0, PHI, /*NegNumerator=*/true,
               /*NegDenominator=*/true);

  // Remove the G_SDIV instruction.
  MI.eraseFromParent();
  return true;
}

bool matchInsertDivByZeroTrap(MachineInstr &MI, MachineRegisterInfo &MRI,
                              GISelKnownBits *KB) {
  Register DenominatorReg = MI.getOperand(2).getReg();

  // If at least 1 bit is known to be 1, then it is not a division by zero.
  APInt KnownOnes = KB->getKnownOnes(DenominatorReg);
  if (!KnownOnes.isZero())
    return false;

  // If this div instruction has already a division by zero check, then there
  // must be a terminating trap in this block using the register.
  MachineBasicBlock *MBB = MI.getParent();
  for (MachineInstr &I : MBB->terminators()) {
    if (I.getOpcode() == M88k::TRAP503 &&
        I.getOperand(0).getReg() == DenominatorReg)
      return false;
  }

  // A trap needs to be added.
  return true;
}

bool applyInsertDivByZeroTrap(GISelChangeObserver &Observer, MachineInstr &MI,
                              MachineRegisterInfo &MRI, MachineIRBuilder &MIB) {
  const LLT S1 = LLT::scalar(1);
  const LLT S32 = LLT::scalar(32);

  MachineBasicBlock *MBB = MI.getParent();
  MachineBasicBlock *TailMBB = MBB->splitAt(MI);
  MIB.setInsertPt(*MBB, MBB->end());
  MIB.setDebugLoc(MI.getDebugLoc());
  Register DenominatorReg = MI.getOperand(2).getReg();
  auto Zero = MIB.buildConstant(S32, 0);
  MIB.buildBrCond(MIB.buildICmp(CmpInst::ICMP_NE, S1, DenominatorReg, Zero),
                  *TailMBB);
  auto Trap = MIB.buildInstr(M88k::TRAP503, {}, {DenominatorReg});

  // The trap instruction needs to be constrained.
  MachineFunction &MF = MIB.getMF();
  const M88kSubtarget &Subtarget = MF.getSubtarget<M88kSubtarget>();
  const auto *TRI = Subtarget.getRegisterInfo();
  const auto *TII = Subtarget.getInstrInfo();
  const auto *RBI = Subtarget.getRegBankInfo();
  constrainSelectedInstRegOperands(*Trap, *TII, *TRI, *RBI);

  return true;
}

} // namespace

#define M88KPOSTLEGALIZERLOWERINGHELPER_GENCOMBINERHELPER_DEPS
#include "M88kGenPostLegalizeGILowering.inc"
#undef M88KPOSTLEGALIZERLOWERINGHELPER_GENCOMBINERHELPER_DEPS

namespace {
class M88kPostLegalizerLoweringImpl : public Combiner {
protected:
  mutable CombinerHelper Helper;
  const M88kPostLegalizerLoweringImplRuleConfig &RuleConfig;
  const M88kSubtarget &STI;

  const bool ReplaceSignedDiv;
  const bool AddZeroDivCheck;

public:
  M88kPostLegalizerLoweringImpl(
      MachineFunction &MF, CombinerInfo &CInfo, const TargetPassConfig *TPC,
      GISelKnownBits &KB, GISelCSEInfo *CSEInfo,
      const M88kPostLegalizerLoweringImplRuleConfig &RuleConfig,
      const M88kSubtarget &STI, MachineDominatorTree *MDT,
      const LegalizerInfo *LI, bool ReplaceSignedDiv, bool AddZeroDivCheck);

  static const char *getName() { return "M88kPostLegalizerCombiner"; }

  bool tryCombineAll(MachineInstr &I) const override;

  bool tryCombineAllImpl(MachineInstr &I) const;

private:
#define GET_GICOMBINER_CLASS_MEMBERS
#include "M88kGenPostLegalizeGILowering.inc"
#undef GET_GICOMBINER_CLASS_MEMBERS
};

#define GET_GICOMBINER_IMPL
#include "M88kGenPostLegalizeGILowering.inc"
#undef GET_GICOMBINER_IMPL

M88kPostLegalizerLoweringImpl::M88kPostLegalizerLoweringImpl(
    MachineFunction &MF, CombinerInfo &CInfo, const TargetPassConfig *TPC,
    GISelKnownBits &KB, GISelCSEInfo *CSEInfo,
    const M88kPostLegalizerLoweringImplRuleConfig &RuleConfig,
    const M88kSubtarget &STI, MachineDominatorTree *MDT,
    const LegalizerInfo *LI, bool ReplaceSignedDiv, bool AddZeroDivCheck)
    : Combiner(MF, CInfo, TPC, &KB, CSEInfo),
      Helper(Observer, B, /*IsPreLegalize*/ false, &KB, MDT, LI),
      RuleConfig(RuleConfig), STI(STI), ReplaceSignedDiv(ReplaceSignedDiv),
      AddZeroDivCheck(AddZeroDivCheck),
#define GET_GICOMBINER_CONSTRUCTOR_INITS
#include "M88kGenPostLegalizeGILowering.inc"
#undef GET_GICOMBINER_CONSTRUCTOR_INITS
{
}

bool M88kPostLegalizerLoweringImpl::tryCombineAll(MachineInstr &MI) const {
  // If the instruction is commutable and the first operand is a constant, then
  // swap the operands. The matcher generated from the SDAG patterns expects the
  // constant always as the second operand, otherwise operand is not matched as
  // immediate.
  if (MI.isCommutable() && isPreISelGenericOpcode(MI.getOpcode())) {
    assert(MI.getNumExplicitOperands() >= 3 && "Not a binary operation");
    unsigned Opc = MI.getOpcode();
    bool HasCarry =
        Opc == TargetOpcode::G_UADDO || Opc == TargetOpcode::G_USUBO ||
        Opc == TargetOpcode::G_UADDE || Opc == TargetOpcode::G_USUBE;
    unsigned SrcIdx = HasCarry ? 2 : 1;
    unsigned SrcOpc =
        getDefIgnoringCopies(MI.getOperand(SrcIdx).getReg(), *B.getMRI())
            ->getOpcode();
    if (SrcOpc == TargetOpcode::G_CONSTANT ||
        SrcOpc == TargetOpcode::G_FCONSTANT) {
      Observer.changingInstr(MI);
      B.getTII().commuteInstruction(MI, false, SrcIdx, SrcIdx + 1);
      Observer.changedInstr(MI);
    }
  }

  return tryCombineAllImpl(MI);
}

class M88kPostLegalizerLowering : public MachineFunctionPass {
  bool IsOptNone;
  M88kPostLegalizerLoweringImplRuleConfig RuleConfig;

public:
  static char ID;

  M88kPostLegalizerLowering(bool IsOptNone = false);

  StringRef getPassName() const override { return "M88kPostLegalizerLowering"; }

  bool runOnMachineFunction(MachineFunction &MF) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
};
} // end anonymous namespace

void M88kPostLegalizerLowering::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<TargetPassConfig>();
  AU.setPreservesCFG();
  getSelectionDAGFallbackAnalysisUsage(AU);
  AU.addRequired<GISelKnownBitsAnalysis>();
  AU.addPreserved<GISelKnownBitsAnalysis>();
  if (!IsOptNone) {
    AU.addRequired<MachineDominatorTree>();
    AU.addPreserved<MachineDominatorTree>();
    AU.addRequired<GISelCSEAnalysisWrapperPass>();
    AU.addPreserved<GISelCSEAnalysisWrapperPass>();
  }
  MachineFunctionPass::getAnalysisUsage(AU);
}

M88kPostLegalizerLowering::M88kPostLegalizerLowering(bool IsOptNone)
    : MachineFunctionPass(ID), IsOptNone(IsOptNone) {
  initializeM88kPostLegalizerLoweringPass(*PassRegistry::getPassRegistry());
}

bool M88kPostLegalizerLowering::runOnMachineFunction(MachineFunction &MF) {
  if (MF.getProperties().hasProperty(
          MachineFunctionProperties::Property::FailedISel))
    return false;
  assert(MF.getProperties().hasProperty(
             MachineFunctionProperties::Property::Legalized) &&
         "Expected a legalized function?");
  auto *TPC = &getAnalysis<TargetPassConfig>();
  const Function &F = MF.getFunction();
  const M88kTargetMachine &TM = TPC->getTM<M88kTargetMachine>();
  bool ReplaceSignedDiv =
      !TM.useDivInstr() && !MF.getSubtarget<M88kSubtarget>().isMC88110();
  bool AddZeroDivCheck =
      !TM.noZeroDivCheck() && !MF.getSubtarget<M88kSubtarget>().isMC88110();
  bool EnableOpt =
      MF.getTarget().getOptLevel() != CodeGenOptLevel::None && !skipFunction(F);

  const M88kSubtarget &ST = MF.getSubtarget<M88kSubtarget>();
  const auto *LI = ST.getLegalizerInfo();

  GISelKnownBits *KB = &getAnalysis<GISelKnownBitsAnalysis>().get(MF);
  MachineDominatorTree *MDT =
      IsOptNone ? nullptr : &getAnalysis<MachineDominatorTree>();
  GISelCSEAnalysisWrapper &Wrapper =
      getAnalysis<GISelCSEAnalysisWrapperPass>().getCSEWrapper();
  auto *CSEInfo = &Wrapper.get(TPC->getCSEConfig());

  CombinerInfo CInfo(/*AllowIllegalOps*/ true, /*ShouldLegalizeIllegal*/ false,
                     /*LegalizerInfo*/ nullptr, EnableOpt, F.hasOptSize(),
                     F.hasMinSize());
  M88kPostLegalizerLoweringImpl Impl(MF, CInfo, TPC, *KB, CSEInfo, RuleConfig,
                                     ST, MDT, LI, ReplaceSignedDiv,
                                     AddZeroDivCheck);
  return Impl.combineMachineInstrs();
}

char M88kPostLegalizerLowering::ID = 0;
INITIALIZE_PASS_BEGIN(M88kPostLegalizerLowering, DEBUG_TYPE,
                      "Lower M88k MachineInstrs after legalization", false,
                      false)
INITIALIZE_PASS_DEPENDENCY(TargetPassConfig)
INITIALIZE_PASS_DEPENDENCY(GISelKnownBitsAnalysis)
INITIALIZE_PASS_END(M88kPostLegalizerLowering, DEBUG_TYPE,
                    "Lower M88k MachineInstrs after legalization", false, false)

namespace llvm {
FunctionPass *createM88kPostLegalizerLowering(bool IsOptNone) {
  return new M88kPostLegalizerLowering(IsOptNone);
}
} // end namespace llvm
