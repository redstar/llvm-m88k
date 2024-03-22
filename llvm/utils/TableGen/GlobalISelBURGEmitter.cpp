
//===- GlobalISelBURGEmitter.cpp - Generate a BURS instruction selector ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This tablegen backend emits code for use by the GlobalISel instruction
/// selector. See include/llvm/Target/GlobalISel/Target.td.
///
/// This file analyzes the patterns recognized by the SelectionDAGISel tablegen
/// backend, filters out the ones that are unsupported, maps
/// SelectionDAG-specific constructs to their GlobalISel counterpart
/// (when applicable: MVT to LLT;  SDNode to generic Instruction).
///
/// Not all patterns are supported: pass the tablegen invocation
/// "-warn-on-skipped-patterns" to emit a warning when a pattern is skipped,
/// as well as why.
///
/// The generator emits a BURS-style instruction selector.
///
/// For the algorithm to construct the tables and how to use them, see:
/// Proebsting 1992, BURS Automata Generation
/// (https://dl.acm.org/doi/pdf/10.1145/203095.203098)
///
/// For the integration of constraints, see:
/// Thier, Ertl, Krall 2018; Fast and Flexible Instruction Selection with
/// Constraints
/// (https://publik.tuwien.ac.at/files/publik_277344.pdf)
///
/// For the hard-coded output values, see:
/// Fraser, Henry 1991; Hard-coding Bottom-up Code Generation Tables to Save
/// Time and Space
/// (http://tfeng.me/papers/fh91hard.pdf)
///
//===----------------------------------------------------------------------===//

#include "CodeGenDAGPatterns.h"
#include "CodeGenInstruction.h"
#include "CodeGenIntrinsics.h"
#include "CodeGenRegisters.h"
#include "CodeGenTarget.h"
#include "InfoByHwMode.h"
#include "SubtargetFeatureInfo.h"
#include "llvm/ADT/PointerUnion.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGenTypes/LowLevelType.h"
#include "llvm/CodeGenTypes/MachineValueType.h"
#include "llvm/Support/CodeGenCoverage.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/SaveAndRestore.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include "llvm/TableGen/TableGenBackend.h"
#include <numeric>
#include <string>

/*
def : Pat<(shl (and GPROpnd:$rs1, mask32:$imm), bfoffset:$ofs),
          (MAKrwo GPROpnd:$rs1, (CPOP $imm), bfoffset:$ofs)>;
def : Pat<(or GPROpnd:$rs1, shmask32:$imm),
          (SETrwo GPROpnd:$rs1, (CPOP $imm), (CTZ $imm))>;
def : Pat<(and GPROpnd:$rs1, invshmask32:$imm),
          (CLRrwo GPROpnd:$rs1, (CPOPINV $imm), (CTZINV $imm))>;

shl -> G_SHL
and -> G_AND

$mak -> G_SHL($and, $bfoffset) : 1
$and -> G_AND($gpr, $mask)
$gpr -> GPROpnd
$mask -> mask32

--------------
Pattern:
(add gr:$r1, (i32 1))

Rules:
$add -> G_ADD($reg, $const)
$const -> G_CONSTANT($one)
$reg -> GR
$one -> 1

-> Operator = instr + operamds
            | register class
            | integer constant
            | constraint

Loops:
 - for all leafs
 - for all operators with arity k
 - for all chain rules
 - for all nonterminals
 - for all operators

Rule = mapping nonterminal -> operator | nonterminal
*/

using namespace llvm;

#define DEBUG_TYPE "gisel-burg-emitter"

STATISTIC(NumPatternTotal, "Total number of patterns");

namespace {

static std::string explainPredicates(const TreePatternNode &N) {
  std::string Explanation;
  StringRef Separator = "";
  for (const TreePredicateCall &Call : N.getPredicateCalls()) {
    const TreePredicateFn &P = Call.Fn;
    Explanation +=
        (Separator + P.getOrigPatFragRecord()->getRecord()->getName()).str();
    Separator = ", ";

    if (P.isAlwaysTrue())
      Explanation += " always-true";
    if (P.isImmediatePattern())
      Explanation += " immediate";

    if (P.isUnindexed())
      Explanation += " unindexed";

    if (P.isNonExtLoad())
      Explanation += " non-extload";
    if (P.isAnyExtLoad())
      Explanation += " extload";
    if (P.isSignExtLoad())
      Explanation += " sextload";
    if (P.isZeroExtLoad())
      Explanation += " zextload";

    if (P.isNonTruncStore())
      Explanation += " non-truncstore";
    if (P.isTruncStore())
      Explanation += " truncstore";

    if (Record *VT = P.getMemoryVT())
      Explanation += (" MemVT=" + VT->getName()).str();
    if (Record *VT = P.getScalarMemoryVT())
      Explanation += (" ScalarVT(MemVT)=" + VT->getName()).str();

    if (ListInit *AddrSpaces = P.getAddressSpaces()) {
      raw_string_ostream OS(Explanation);
      OS << " AddressSpaces=[";

      StringRef AddrSpaceSeparator;
      for (Init *Val : AddrSpaces->getValues()) {
        IntInit *IntVal = dyn_cast<IntInit>(Val);
        if (!IntVal)
          continue;

        OS << AddrSpaceSeparator << IntVal->getValue();
        AddrSpaceSeparator = ", ";
      }

      OS << ']';
    }

    int64_t MinAlign = P.getMinAlignment();
    if (MinAlign > 0)
      Explanation += " MinAlign=" + utostr(MinAlign);

    if (P.isAtomicOrderingMonotonic())
      Explanation += " monotonic";
    if (P.isAtomicOrderingAcquire())
      Explanation += " acquire";
    if (P.isAtomicOrderingRelease())
      Explanation += " release";
    if (P.isAtomicOrderingAcquireRelease())
      Explanation += " acq_rel";
    if (P.isAtomicOrderingSequentiallyConsistent())
      Explanation += " seq_cst";
    if (P.isAtomicOrderingAcquireOrStronger())
      Explanation += " >=acquire";
    if (P.isAtomicOrderingWeakerThanAcquire())
      Explanation += " <acquire";
    if (P.isAtomicOrderingReleaseOrStronger())
      Explanation += " >=release";
    if (P.isAtomicOrderingWeakerThanRelease())
      Explanation += " <release";
  }
  return Explanation;
}

std::string explainOperator(Record *Operator) {
  if (Operator->isSubClassOf("SDNode"))
    return (" (" + Operator->getValueAsString("Opcode") + ")").str();

  if (Operator->isSubClassOf("Intrinsic"))
    return (" (Operator is an Intrinsic, " + Operator->getName() + ")").str();

  if (Operator->isSubClassOf("ComplexPattern"))
    return (" (Operator is an unmapped ComplexPattern, " + Operator->getName() +
            ")")
        .str();

  if (Operator->isSubClassOf("SDNodeXForm"))
    return (" (Operator is an unmapped SDNodeXForm, " + Operator->getName() +
            ")")
        .str();

  return (" (Operator " + Operator->getName() + " not understood)").str();
}

/// Helper function to let the emitter report skip reason error messages.
static Error failedImport(const Twine &Reason) {
  return make_error<StringError>(Reason, inconvertibleErrorCode());
}

static Error isTrivialOperatorNode(const TreePatternNode &N) {
  std::string Explanation;
  std::string Separator;

  bool HasUnsupportedPredicate = false;
  for (const TreePredicateCall &Call : N.getPredicateCalls()) {
    const TreePredicateFn &Predicate = Call.Fn;

    if (Predicate.isAlwaysTrue())
      continue;

    if (Predicate.isImmediatePattern())
      continue;

    if (Predicate.hasNoUse())
      continue;

    if (Predicate.isNonExtLoad() || Predicate.isAnyExtLoad() ||
        Predicate.isSignExtLoad() || Predicate.isZeroExtLoad())
      continue;

    if (Predicate.isNonTruncStore() || Predicate.isTruncStore())
      continue;

    if (Predicate.isLoad() && Predicate.getMemoryVT())
      continue;

    if (Predicate.isLoad() || Predicate.isStore()) {
      if (Predicate.isUnindexed())
        continue;
    }

    if (Predicate.isLoad() || Predicate.isStore() || Predicate.isAtomic()) {
      const ListInit *AddrSpaces = Predicate.getAddressSpaces();
      if (AddrSpaces && !AddrSpaces->empty())
        continue;

      if (Predicate.getMinAlignment() > 0)
        continue;
    }

    if (Predicate.isAtomic() && Predicate.getMemoryVT())
      continue;

    if (Predicate.isAtomic() &&
        (Predicate.isAtomicOrderingMonotonic() ||
         Predicate.isAtomicOrderingAcquire() ||
         Predicate.isAtomicOrderingRelease() ||
         Predicate.isAtomicOrderingAcquireRelease() ||
         Predicate.isAtomicOrderingSequentiallyConsistent() ||
         Predicate.isAtomicOrderingAcquireOrStronger() ||
         Predicate.isAtomicOrderingWeakerThanAcquire() ||
         Predicate.isAtomicOrderingReleaseOrStronger() ||
         Predicate.isAtomicOrderingWeakerThanRelease()))
      continue;

    if (Predicate.hasGISelPredicateCode())
      continue;

    HasUnsupportedPredicate = true;
    Explanation = Separator + "Has a predicate (" + explainPredicates(N) + ")";
    Separator = ", ";
    Explanation += (Separator + "first-failing:" +
                    Predicate.getOrigPatFragRecord()->getRecord()->getName())
                       .str();
    break;
  }

  if (!HasUnsupportedPredicate)
    return Error::success();

  return failedImport(Explanation);
}

//===- BURS table generator -----------------------------------------------===//

constexpr unsigned CostInfinity = ~1U;

class alignas(8) Nonterminal {
public:
};

using OperandList = SmallVector<Nonterminal *, 2>;

// A operator can be either an instruction, a register class, or an immediate
// value.
class alignas(8) Operator {
public:
  enum Type { Op_Inst, Op_RegClass, Op_Value };

protected:
  Type Kind;

private:
  unsigned Num;
  unsigned Opcode;
  OperandList Operands;
  Record *RegClass;
  int IntValue;

  // Open:
  // map, reps

public:
  Operator(unsigned Num, unsigned Opcode, OperandList &&Operands)
      : Kind(Op_Inst), Num(Num), Opcode(Opcode), Operands(std::move(Operands)),
        RegClass(nullptr), IntValue(0) {}
  Operator(unsigned Num, Record *RegClass)
      : Kind(Op_RegClass), Num(Num), Opcode(0), Operands(), RegClass(RegClass),
        IntValue(0) {}
  Operator(unsigned Num, int IntValue)
      : Kind(Op_RegClass), Num(Num), Opcode(0), Operands(), RegClass(nullptr),
        IntValue(IntValue) {}

  unsigned getNum() const { return Num; }

  unsigned getOpcode() const {
    assert(isInst());
    return Opcode;
  }
  Record *getRegClass() const {
    assert(isRegClass());
    return RegClass;
  }
  int getIntValue() const {
    assert(isValue());
    return IntValue;
  }

  unsigned arity() const {
    if (isInst())
      return Operands.size();
    return 0;
  }

  Type getKind() const { return Kind; }
  bool isInst() const { return Kind == Op_Inst; }
  bool isRegClass() const { return Kind == Op_RegClass; }
  bool isValue() const { return Kind == Op_Value; }
};

class Rule {
  // The DAG pattern this rule is derived from. Only valid for the root element.
  const PatternToMatch *Pat;

  // The left hand side of the rule.
  Nonterminal *LHS;

  // The right hand side of the rule.
  // In normal form, we can have either a chain rule or an operator as right
  // hand side.
  PointerUnion<Nonterminal *, Operator *> RHS;

  // The cost of the rule.
  unsigned Cost;

  // The rule number.
  unsigned Num;

public:
  Rule(unsigned Num, const PatternToMatch *Pat)
      : Pat(Pat), LHS(nullptr), RHS(nullptr), Cost(CostInfinity), Num(Num) {}

  const PatternToMatch *getPattern() const { return Pat; }
  Nonterminal *getLHS() const { return LHS; }

  bool isChainRule() const { return RHS.is<Nonterminal *>(); }

  Nonterminal *getDerivedNonterminal() const {
    assert(isChainRule() && "Rule is not a chain rule");
    return RHS.get<Nonterminal *>();
  }

  bool derivesLeaf() {
    if (RHS.is<Operator *>())
      return RHS.get<Operator *>()->arity() == 0;
    return false;
  }

  Operator *getOperator() const { return RHS.get<Operator *>(); }

  unsigned getCost() const { return Cost; }
  unsigned getNum() const { return Num; }
};

struct Item {
  Rule *R;
  unsigned Cost;
};

class State {
  DenseMap<Nonterminal *, Item> ItemSet;
  unsigned Num;

public:
  unsigned getNum() const { return Num; }

  // Function NormalizeCosts(), Fig. 7
  void normalizeCost() {
    unsigned Delta = CostInfinity;
    for (auto &[NT, Item] : ItemSet)
      Delta = std::min(Delta, Item.Cost);
    for (auto &[NT, Item] : ItemSet)
      Item.Cost = Delta;
  }

  unsigned getCost(Nonterminal *NT) {
    auto It = ItemSet.find_as(NT);
    if (It != ItemSet.end())
      return It->second.Cost;
    return CostInfinity;
  }

  void update(Nonterminal *NT, Rule *R, unsigned Cost) {
    ItemSet[NT] = {R, Cost};
  }
};

class BURSTableGenerator {
  // List of all operators.
  SmallVector<Operator *, 0> Operators;

  // List of all rules.
  SmallVector<Rule *, 0> Rules;

  // Work list containing the discovered stated.
  SmallVector<State *, 8> WorkList;

public:
  void closure(State *S);
  void computeLeafStates();
  State *project(Operator *Op, unsigned Idx, State *S);
  void triangle(unsigned I, unsigned J);
  void computeTransitions(Operator *Op, State *S);
  void run();
};

// Function Closure(), Fig. 8
void BURSTableGenerator::closure(State *S) {
  bool Changed;
  do {
    Changed = false;
    for (Rule *R : Rules) {
      if (!R->isChainRule())
        continue;
      Nonterminal *N = R->getLHS();
      Nonterminal *M = R->getDerivedNonterminal();

      unsigned Cost = R->getCost() + S->getCost(M);
      if (Cost < S->getCost(N)) {
        S->update(N, R, Cost);
        Changed = true;
      }
    }
  } while (Changed);
}

// Function ComputeLeafStates(), Fig. 9
void BURSTableGenerator::computeLeafStates() {
  for (Operator *Op : Operators) {
    if (Op->arity() != 0)
      continue;
    State *S = new State();
    for (Rule *R : Rules) {
      if (!R->derivesLeaf())
        continue;
      if (R->getOperator() != Op)
        continue;
      Nonterminal *N = R->getLHS();
      if (R->getCost() < S->getCost(N))
        S->update(N, R, R->getCost());
    }
    S->normalizeCost();
    closure(S);
    WorkList.push_back(S);
    // States.push_back(S);
    // Op->setState(S);
  }
}

// Function Project(), Fig. 11
State *BURSTableGenerator::project(Operator *Op, unsigned Idx, State *S) {
  State *P = new State();
  // For all nonterminal:
  //    If nonterminal N is used in the ith dimension of op, then add the cost
  //    to the state.
  P->normalizeCost();
  return P;
}

// Function Triangle(), Fig. 16
void BURSTableGenerator::triangle(unsigned I, unsigned J) {}

// Function ComputeTransitions(), Fig. 12
void BURSTableGenerator::computeTransitions(Operator *Op, State *S) {
  for (unsigned I = 0, E = Op->arity(); I < E; ++I) {
    State *P = project(Op, I, S);
    // Op->map[I][S] = P;
    // If P is not a representer set in Op->reps[I]
    //    ... lot of computations ...
  }
}

// Function Main(), Fig. 5
void BURSTableGenerator::run() {
  computeLeafStates();
  while (!WorkList.empty()) {
    State *S = WorkList.pop_back_val();
    for (Operator *Op : Operators)
      computeTransitions(Op, S);
  }
}

//===- GlobalISelBURGEmitter class ----------------------------------------===//

class GlobalISelBURGEmitter {
public:
  explicit GlobalISelBURGEmitter(RecordKeeper &RK);

  const CodeGenTarget &getTarget() const { return Target; }
  StringRef getClassName() const { return ClassName; }

  void gatherOpcodeValues();
  void gatherNodeEquivs();

  Record *findNodeEquiv(Record *N) const;
  const CodeGenInstruction *getEquivNode(Record &Equiv,
                                         const TreePatternNode &N) const;

  Error importPatternToMatch(BURSTableGenerator &BURS,
                             const PatternToMatch &Pat);

  void run(raw_ostream &OS);

private:
  std::string ClassName;

  const RecordKeeper &RK;
  const CodeGenDAGPatterns CGP;
  const CodeGenTarget &Target;
  CodeGenRegBank &CGRegs;

  std::vector<Record *> AllPatFrags;

  DenseMap<const CodeGenInstruction *, unsigned> OpcodeValues;

  /// Keep track of the equivalence between SDNodes and Instruction by mapping
  /// SDNodes to the GINodeEquiv mapping. We need to map to the GINodeEquiv to
  /// check for attributes on the relation such as CheckMMOIsNonAtomic.
  /// This is defined using 'GINodeEquiv' in the target description.
  DenseMap<Record *, Record *> NodeEquivs;

  /// Keep track of the equivalence between ComplexPattern's and
  /// GIComplexOperandMatcher. Map entries are specified by subclassing
  /// GIComplexPatternEquiv.
  DenseMap<const Record *, const Record *> ComplexPatternEquivs;

  /// Keep track of the equivalence between SDNodeXForm's and
  /// GICustomOperandRenderer. Map entries are specified by subclassing
  /// GISDNodeXFormEquiv.
  DenseMap<const Record *, const Record *> SDNodeXFormEquivs;

  /// Keep track of Scores of PatternsToMatch similar to how the DAG does.
  /// This adds compatibility for RuleMatchers to use this for ordering rules.
  DenseMap<uint64_t, int> RuleMatcherScores;
};

GlobalISelBURGEmitter::GlobalISelBURGEmitter(RecordKeeper &RK)
    : RK(RK), CGP(RK), Target(CGP.getTargetInfo()),
      CGRegs(Target.getRegBank()) {
  ClassName = Target.getName().str() + "BURGInstructionSelector";
}

void GlobalISelBURGEmitter::gatherOpcodeValues() {
  for (const CodeGenInstruction *I : Target.getInstructionsByEnumValue())
    OpcodeValues[I] = Target.getInstrIntValue(I->TheDef);
}

void GlobalISelBURGEmitter::gatherNodeEquivs() {
  assert(NodeEquivs.empty());
  for (Record *Equiv : RK.getAllDerivedDefinitions("GINodeEquiv"))
    NodeEquivs[Equiv->getValueAsDef("Node")] = Equiv;

  assert(ComplexPatternEquivs.empty());
  for (Record *Equiv : RK.getAllDerivedDefinitions("GIComplexPatternEquiv")) {
    Record *SelDAGEquiv = Equiv->getValueAsDef("SelDAGEquivalent");
    if (!SelDAGEquiv)
      continue;
    ComplexPatternEquivs[SelDAGEquiv] = Equiv;
  }

  assert(SDNodeXFormEquivs.empty());
  for (Record *Equiv : RK.getAllDerivedDefinitions("GISDNodeXFormEquiv")) {
    Record *SelDAGEquiv = Equiv->getValueAsDef("SelDAGEquivalent");
    if (!SelDAGEquiv)
      continue;
    SDNodeXFormEquivs[SelDAGEquiv] = Equiv;
  }
}

Record *GlobalISelBURGEmitter::findNodeEquiv(Record *N) const {
  return NodeEquivs.lookup(N);
}

const CodeGenInstruction *
GlobalISelBURGEmitter::getEquivNode(Record &Equiv,
                                    const TreePatternNode &N) const {
  if (N.getNumChildren() >= 1) {
    // setcc operation maps to two different G_* instructions based on the type.
    if (!Equiv.isValueUnset("IfFloatingPoint") &&
        MVT(N.getChild(0).getSimpleType(0)).isFloatingPoint())
      return &Target.getInstruction(Equiv.getValueAsDef("IfFloatingPoint"));
  }

  if (!Equiv.isValueUnset("IfConvergent") &&
      N.getIntrinsicInfo(CGP)->isConvergent)
    return &Target.getInstruction(Equiv.getValueAsDef("IfConvergent"));

  for (const TreePredicateCall &Call : N.getPredicateCalls()) {
    const TreePredicateFn &Predicate = Call.Fn;
    if (!Equiv.isValueUnset("IfSignExtend") &&
        (Predicate.isLoad() || Predicate.isAtomic()) &&
        Predicate.isSignExtLoad())
      return &Target.getInstruction(Equiv.getValueAsDef("IfSignExtend"));
    if (!Equiv.isValueUnset("IfZeroExtend") &&
        (Predicate.isLoad() || Predicate.isAtomic()) &&
        Predicate.isZeroExtLoad())
      return &Target.getInstruction(Equiv.getValueAsDef("IfZeroExtend"));
  }

  return &Target.getInstruction(Equiv.getValueAsDef("I"));
}

Error GlobalISelBURGEmitter::importPatternToMatch(BURSTableGenerator &BURS,
                                                  const PatternToMatch &Pat) {
  // Translate pattern to grammar.

  TreePatternNode &Src = Pat.getSrcPattern();
  TreePatternNode &Dst = Pat.getDstPattern();

  // If the root of either pattern isn't a simple operator, ignore it.
  if (auto Err = isTrivialOperatorNode(Dst))
    return failedImport("Dst pattern root isn't a trivial operator (" +
                        toString(std::move(Err)) + ")");
  if (auto Err = isTrivialOperatorNode(Src))
    return failedImport("Src pattern root isn't a trivial operator (" +
                        toString(std::move(Err)) + ")");

  Record *SrcGIEquivOrNull = nullptr;
  const CodeGenInstruction *SrcGIOrNull = nullptr;

  // Start with the defined operands (i.e., the results of the root operator).
  if (Src.isLeaf()) {
    Init *SrcInit = Src.getLeafValue();
    if (isa<IntInit>(SrcInit)) {
      // InsnMatcher.addPredicate<InstructionOpcodeMatcher>(
      //     &Target.getInstruction(RK.getDef("G_CONSTANT")));
    } else
      return failedImport(
          "Unable to deduce gMIR opcode to handle Src (which is a leaf)");
  } else {
    SrcGIEquivOrNull = findNodeEquiv(Src.getOperator());
    if (!SrcGIEquivOrNull)
      return failedImport("Pattern operator lacks an equivalent Instruction" +
                          explainOperator(Src.getOperator()));
    SrcGIOrNull = getEquivNode(*SrcGIEquivOrNull, Src);

    // The operators look good: match the opcode
    // InsnMatcher.addPredicate<InstructionOpcodeMatcher>(SrcGIOrNull);
  }

  return Error::success();
}

void GlobalISelBURGEmitter::run(raw_ostream &OS) {
  // Gather all opcode values.
  gatherOpcodeValues();

  // Track the GINodeEquiv definitions.
  gatherNodeEquivs();

  AllPatFrags = RK.getAllDerivedDefinitions("PatFrags");

  BURSTableGenerator BURS;
  for (const PatternToMatch &Pat : CGP.ptms()) {
    ++NumPatternTotal;
    if (auto Err = importPatternToMatch(BURS, Pat)) {
      dbgs() << llvm::to_string(Pat.getSrcPattern()) << "  =>  "
             << llvm::to_string(Pat.getDstPattern()) << "\n";
      dbgs() << toString(std::move(Err)) << "\n";
    }
  }
  BURS.run();
}

} // end anonymous namespace

//===----------------------------------------------------------------------===//

static TableGen::Emitter::OptClass<GlobalISelBURGEmitter>
    X("gen-global-isel-burg", "Generate GlobalISel BURG selector");
