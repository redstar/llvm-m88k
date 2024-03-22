
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
#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/PointerUnion.h"
#include "llvm/ADT/STLExtras.h"
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
#include <map>
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

Constraints/predicates are handled by the generated labeler.

Loops:
 - for all leafs
 - for all operators with arity k
 - for all chain rules
 - for all nonterminals
 - for all operators

Rule = mapping nonterminal -> operator | nonterminal
*/

//===----------------------------------------------------------------------===//
//
// Design notes
//
// Cost vs Complexity
// Cost and Complexity are a dual concept. The LLVM complexity can be turn into
// a cost by inverting all bits.
//
// Predicates
// A predicate in the DAG pattern can be evaluated in the labeler or the
// matcher, depending on the nature of the predicate. For example, a register
// operand is constraint to have a register class. The check for the register
// class can be encoded in the grammar, and thus is encoded in the matcher
// table. The same approach does not workfor integer values, because there can
// be overlapping subranges. For example, patterns for constant materialization
// can have patterns for specific values, e.g. (i32 1), and also subranges which
// include these specific values, and also each other, e.g. (i8 $imm), (i16
// $imm), and (i32 $imm). If the subject tree contains G_CONSTANT 1, then it is
// unclear which operator to choose, because the value can be used in several
// ways. E.g., a pattern like (add $gpr, (i32 1)) could be covered by a more
// complex pattern for address computation, which uses a i8. The solution is to
// simply use an integer type in the grammar, and run the predications in the
// matcher. When a predicate fails, then there is either another (less complex)
// match if the patterns fully cover the tree, or the fallback select() routine
// can be called.
//
// Grammar construction
// The DAG patterns do not use all the possibilities the grammar approach offers
//  - A register operand GPR is translated to
//    gpr: GPR
//  - An integer constant is translated to
//    int: Int
//    There can be lot of subranges of integer, e.g. (i32 0) or predicates like
//    imm8 or uimm16. These all are handled as integers in the grammar.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
//
// Lessons learned about SDAG patterns:
//  - The root of a pattern is either a constant value or an operator
//  - Immediates seemed to be handled differently
//
//
//
//===----------------------------------------------------------------------===//

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

static Record *getInitValueAsRegClass(Init *V) {
  if (DefInit *VDefInit = dyn_cast<DefInit>(V)) {
    if (VDefInit->getDef()->isSubClassOf("RegisterOperand"))
      return VDefInit->getDef()->getValueAsDef("RegClass");
    if (VDefInit->getDef()->isSubClassOf("RegisterClass"))
      return VDefInit->getDef();
  }
  return nullptr;
}

//===- BURS table generator -----------------------------------------------===//

// Use descriptive type names for the various numbers.
using NonterminalNum = unsigned;
using OperatorNum = unsigned;
using RuleNum = unsigned;
using StateNum = unsigned;

// Simple abstraction of the cost of a rule.
class CostValue {
  unsigned Cost;

public:
  CostValue() : Cost(0) {}

  static CostValue fromComplexity(int Score) {
    CostValue C;
    C.Cost = unsigned(~Score);
    return C;
  }

  static CostValue infinity() {
    CostValue C;
    C.Cost = unsigned(~0U);
    return C;
  }

  bool operator<(CostValue Other) const { return Cost < Other.Cost; }

  friend CostValue operator+(CostValue LHS, const CostValue RHS) {
    CostValue C;
    C.Cost = LHS.Cost + RHS.Cost;
    // Check for overflow.
    if (C.Cost < std::min(LHS.Cost, RHS.Cost))
      return infinity();
    return C;
  }

  CostValue min(CostValue Other) const {
    return Cost < Other.Cost ? *this : Other;
  }

  void normalize(CostValue Delta) {
    assert(Delta.Cost <= Cost && "Normalize cost would be negative");
    Cost -= Delta.Cost;
  }

  unsigned getValue() const { return Cost; }
};

class alignas(8) Nonterminal {
  NonterminalNum Num;

public:
  Nonterminal(NonterminalNum Num) : Num(Num) {}
  NonterminalNum getNum() const { return Num; }
};

using OperandList = SmallVector<Nonterminal *, 2>;

class State;

// A operator can be either an instruction, a register class, or an integer
// tyoe. The mapping to representer states and the representer states are part
// of the operator data. Note that this actual values for the operands are part
// of the rules which use this operator.
class alignas(8) Operator : public FoldingSetNode {
public:
  // Kind of operators.
  // TODO Add predicate(s)?
  enum Type { Op_Inst, Op_RegClass, Op_Value };

protected:
  Type Kind;

private:
  OperatorNum Num;
  unsigned Opcode;
  Record *RegClass;
  unsigned Arity;
  int IntValue;

  // The mapping from state to representer state for each dimension.
  SmallVector<DenseMap<unsigned, unsigned>, 0> Map;

  // The mapping from a representer state to a unique number.
  SmallVector<DenseMap<unsigned, unsigned>, 0> Reps;

  // State of operator if leaf.
  State *LeafState = nullptr;

  // TODO Transition table.
public:
  Operator(OperatorNum Num, unsigned Opcode, unsigned Arity)
      : Kind(Op_Inst), Num(Num), Opcode(Opcode), RegClass(nullptr),
        Arity(Arity), IntValue(0) {
    Map.resize(Arity);
    Reps.resize(Arity);
  }
  Operator(OperatorNum Num, Record *RegClass)
      : Kind(Op_RegClass), Num(Num), Opcode(0), RegClass(RegClass), Arity(0),
        IntValue(0) {}
  Operator(OperatorNum Num, int IntValue)
      : Kind(Op_RegClass), Num(Num), Opcode(0), RegClass(nullptr), Arity(0),
        IntValue(IntValue) {}

  void Profile(FoldingSetNodeID &ID) const {
    ID.AddInteger(unsigned(Kind));
    switch (Kind) {
    case Op_Inst:
      ID.AddInteger(Opcode);
      ID.AddInteger(Arity);
      break;
    case Op_RegClass:
      ID.AddPointer(RegClass);
      break;
    case Op_Value:
      ID.AddInteger(IntValue);
      break;
    }
  }

  OperatorNum getNum() const { return Num; }

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

  void setLeafState(State *S) { LeafState = S; }
  State *getLeadState() const { return LeafState; }

  unsigned arity() const { return Arity; }

  SmallVectorImpl<DenseMap<unsigned, unsigned>> &getMap() { return Map; };
  SmallVectorImpl<DenseMap<unsigned, unsigned>> &getReps() { return Reps; };

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

  // The operands in case the right hand side is an operator.
  OperandList Operands;

  // The cost of the rule.
  CostValue Cost;

  // The rule number.
  RuleNum Num;

public:
  Rule(RuleNum Num, Nonterminal *LHS, Operator *RHS, OperandList &&Operands,
       CostValue Cost, const PatternToMatch *Pat)
      : Pat(Pat), LHS(LHS), RHS(RHS), Operands(std::move(Operands)), Cost(Cost),
        Num(Num) {}
  Rule(RuleNum Num, Nonterminal *LHS, Nonterminal *RHS, CostValue Cost,
       const PatternToMatch *Pat)
      : Pat(Pat), LHS(LHS), RHS(RHS), Cost(Cost), Num(Num) {}

  const PatternToMatch *getPattern() const { return Pat; }
  Nonterminal *getLHS() const { return LHS; }

  bool isChainRule() const { return RHS.is<Nonterminal *>(); }

  // Predicates which can be used with make_filter_range().
  static bool isChainRule(const Rule *R) { return R->isChainRule(); }
  static bool isOperatorRule(const Rule *R) { return !R->isChainRule(); }

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
  const OperandList &getOperands() const { return Operands; }

  CostValue getCost() const { return Cost; }
  RuleNum getNum() const { return Num; }
};

struct Item {
  RuleNum Num;
  CostValue Cost;
};

class State : public FoldingSetNode {
  // Mapping from nonterminal to item.
  // The only reason for an ordered map is the ordered enumeration required for
  // the lookup in the FoldingSet.
  std::map<NonterminalNum, Item> ItemSet;
  StateNum Num;

public:
  State() : Num(~1U) {}

  void Profile(FoldingSetNodeID &ID) const {
    for (auto &[No, Item] : ItemSet) {
      ID.AddInteger(No);
      ID.AddInteger(Item.Num);
      ID.AddInteger(Item.Cost.getValue());
    }
  }

  void setNum(StateNum N) { Num = N; }
  StateNum getNum() const { return Num; }

  // Function NormalizeCosts(), Fig. 7
  void normalizeCost() {
    CostValue Delta = CostValue::infinity();
    for (auto &[No, Item] : ItemSet)
      Delta = Delta.min(Item.Cost);
    for (auto &[No, Item] : ItemSet)
      Item.Cost.normalize(Delta);
  }

  CostValue getCost(Nonterminal *NT) {
    auto It = ItemSet.find(NT->getNum());
    if (It != ItemSet.end())
      return It->second.Cost;
    return CostValue::infinity();
  }

  void update(Nonterminal *NT, Rule *R, CostValue Cost) {
    ItemSet[NT->getNum()] = {R->getNum(), Cost};
  }
};

class ProjectedState : public FoldingSetNode {
  std::map<NonterminalNum, CostValue> ItemSet;
  StateNum Num;

public:
  ProjectedState() : Num(~1U) {}

  void Profile(FoldingSetNodeID &ID) const {
    for (auto &[No, Cost] : ItemSet) {
      ID.AddInteger(No);
      ID.AddInteger(Cost.getValue());
    }
  }

  void setNum(StateNum N) { Num = N; }
  StateNum getNum() const { return Num; }

  // Function NormalizeCosts(), Fig. 7
  void normalizeCost() {
    CostValue Delta = CostValue::infinity();
    for (auto &[No, Cost] : ItemSet)
      Delta = Delta.min(Cost);
    for (auto &[No, Cost] : ItemSet)
      Cost.normalize(Delta);
  }

  CostValue getCost(Nonterminal *NT) {
    auto It = ItemSet.find(NT->getNum());
    if (It != ItemSet.end())
      return It->second;
    return CostValue::infinity();
  }

  void update(Nonterminal *NT, CostValue Cost) { ItemSet[NT->getNum()] = Cost; }
};

class BURSTableGenerator {
  // Set of all operators.
  FoldingSet<Operator> Operators;

  // List of all nonterminals.
  SmallVector<Nonterminal *, 0> Nonterminals;
  DenseMap<unsigned, Nonterminal *> OperatorToNonterminal;

  // Set of all states.
  FoldingSet<State> States;

  // Set of all projected states.
  FoldingSet<ProjectedState> ProjectedStates;

  // List of all rules.
  SmallVector<Rule *, 0> Rules;

  // Work list containing the discovered stated.
  SmallVector<State *, 8> WorkList;

  Rule *createRule(Operator *Op, OperandList &&Operands, CostValue Cost);

public:
  Rule *createValueRule(int Value, CostValue Cost = CostValue());
  Rule *createInstRule(unsigned Opcode, OperandList &&Opnds,
                       CostValue Cost = CostValue());
  Rule *createRegClassRule(Record *RC, CostValue Cost = CostValue());

  void closure(State *S);
  void computeLeafStates();
  ProjectedState *project(Operator *Op, unsigned Idx, State *S);
  void triangle(unsigned I, unsigned J);
  void computeTransitions(Operator *Op, State *S);
  void run();
};

Rule *BURSTableGenerator::createRule(Operator *Op, OperandList &&Operands,
                                     CostValue Cost) {
  Nonterminal *NT = OperatorToNonterminal[Op->getNum()];
  if (!NT) {
    NT = new Nonterminal(Nonterminals.size());
    Nonterminals.push_back(NT);
    OperatorToNonterminal[Op->getNum()] = NT;
  }

  Rule *R = new Rule(Rules.size(), NT, Op, std::move(Operands), Cost, nullptr);
  Rules.push_back(R);
  return R;
}

Rule *BURSTableGenerator::createValueRule(int Value, CostValue Cost) {
  FoldingSetNodeID ID;
  ID.AddInteger(unsigned(Operator::Op_Value));
  ID.AddInteger(Value);
  void *InsertPoint;
  Operator *Op = Operators.FindNodeOrInsertPos(ID, InsertPoint);
  if (!Op) {
    unsigned Num = Operators.size();
    Op = new Operator(Num, Value);
    Operators.InsertNode(Op, InsertPoint);
  }

  return createRule(Op, {}, Cost);
}

Rule *BURSTableGenerator::createInstRule(unsigned Opcode, OperandList &&Opnds,
                                         CostValue Cost) {
  const unsigned Arity = Opnds.size();
  FoldingSetNodeID ID;
  ID.AddInteger(unsigned(Operator::Op_Inst));
  ID.AddInteger(Opcode);
  ID.AddInteger(Arity);
  void *InsertPoint;
  Operator *Op = Operators.FindNodeOrInsertPos(ID, InsertPoint);
  if (!Op) {
    unsigned Num = Operators.size();
    Op = new Operator(Num, Opcode, Arity);
    Operators.InsertNode(Op, InsertPoint);
  }

  return createRule(Op, std::move(Opnds), Cost);
}

Rule *BURSTableGenerator::createRegClassRule(Record *RC, CostValue Cost) {
  FoldingSetNodeID ID;
  ID.AddInteger(unsigned(Operator::Op_RegClass));
  ID.AddPointer(RC);
  void *InsertPoint;
  Operator *Op = Operators.FindNodeOrInsertPos(ID, InsertPoint);
  if (!Op) {
    unsigned Num = Operators.size();
    Op = new Operator(Num, RC);
    Operators.InsertNode(Op, InsertPoint);
  }

  return createRule(Op, {}, Cost);
}

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

      CostValue Cost = R->getCost() + S->getCost(M);
      if (Cost < S->getCost(N)) {
        S->update(N, R, Cost);
        Changed = true;
      }
    }
  } while (Changed);
}

// Function ComputeLeafStates(), Fig. 9
void BURSTableGenerator::computeLeafStates() {
  for (Operator &Op : Operators) {
    if (Op.arity() != 0)
      continue;
    State *S = new State();
    for (Rule *R : make_filter_range(Rules, Rule::isOperatorRule)) {
      if (R->getOperator() != &Op)
        continue;
      Nonterminal *N = R->getLHS();
      if (R->getCost() < S->getCost(N))
        S->update(N, R, R->getCost());
    }
    S->normalizeCost();
    closure(S);

    // Record the state if not yet known.
    FoldingSetNodeID ID;
    S->Profile(ID);
    void *InsertPoint;
    if (State *Tmp = States.FindNodeOrInsertPos(ID, InsertPoint)) {
      delete S;
      S = Tmp;
    } else {
      S->setNum(States.size());
      States.InsertNode(S, InsertPoint);
      WorkList.push_back(S);
    }
    Op.setLeafState(S);
  }
}

// Function Project(), Fig. 11
ProjectedState *BURSTableGenerator::project(Operator *Op, unsigned Idx,
                                            State *S) {
  ProjectedState *P = new ProjectedState();
  for (auto *R : make_filter_range(Rules, Rule::isOperatorRule)) {
    if (R->getOperator() != Op)
      continue;
    // Nonterminal NT is used in dimenson Idx.
    Nonterminal *NT = R->getOperands()[Idx];
    P->update(NT, S->getCost(NT));
  }
  P->normalizeCost();

  // Record the state if not yet known.
  FoldingSetNodeID ID;
  P->Profile(ID);
  void *InsertPoint;
  if (ProjectedState *Tmp =
          ProjectedStates.FindNodeOrInsertPos(ID, InsertPoint)) {
    delete P;
    P = Tmp;
  } else {
    P->setNum(ProjectedStates.size());
    ProjectedStates.InsertNode(P, InsertPoint);
  }

  return P;
}

// Function Triangle(), Fig. 16
void BURSTableGenerator::triangle(unsigned I, unsigned J) {}

namespace {
// Enumerate all dimensions except Idx.
class Enumerator {
  SmallVector<DenseMap<unsigned, unsigned>::iterator, 0> Iterators;
  SmallVectorImpl<DenseMap<unsigned, unsigned>> &Reps;
  unsigned Idx;
  unsigned State;

  void fill(SmallVectorImpl<unsigned> &Sets) {
    for (size_t I = 0, E = Reps.size(); I < E; ++I)
      if (I == Idx)
        Sets[I] = State;
      else
        Sets[I] = Iterators[I]->first;
  }

public:
  Enumerator(SmallVectorImpl<DenseMap<unsigned, unsigned>> &Reps, unsigned Idx,
             unsigned State)
      : Reps(Reps), Idx(Idx), State(State) {
    Iterators.resize(Reps.size());
  }

  bool first(SmallVectorImpl<unsigned> &Sets) {
    for (size_t I = 0, E = Reps.size(); I < E; ++I)
      if (I != Idx) {
        Iterators[I] = Reps[I].begin();
        if (Iterators[I] == Reps[I].end())
          return false;
      }
    fill(Sets);
    return true;
  }

  bool next(SmallVectorImpl<unsigned> &Sets) {
    for (size_t I = 0, E = Reps.size(); I < E; ++I) {
      if (I == Idx)
        continue;
      ++Iterators[I];
      if (Iterators[I] != Reps[I].end())
        break;
      if (I + 1 == E)
        return false;
      Iterators[I] = Reps[I].begin();
    }
    fill(Sets);
    return true;
  }
};
} // namespace

// Function ComputeTransitions(), Fig. 12
void BURSTableGenerator::computeTransitions(Operator *Op, State *S) {
  for (unsigned I = 0, E = Op->arity(); I < E; ++I) {
    ProjectedState *P = project(Op, I, S);
    Op->getMap()[I][S->getNum()] = P->getNum();
    auto It = Op->getReps()[I].find(P->getNum());
    if (It == Op->getReps()[I].end()) {
      unsigned RepNum = Op->getReps()[I].size();
      Op->getReps()[I][P->getNum()] = RepNum;
      SmallVector<StateNum, 0> EnumStates;
      EnumStates.resize(Op->arity());
      Enumerator Enum(Op->getReps(), I, P->getNum());
      if (Enum.first(EnumStates)) {
        do {
          State *Result = new State();
          //  Enumerate all rules with Op.
          Result->normalizeCost();
          // If Result not in States ....

        } while (Enum.next(EnumStates));
      }
    }
  }
}

// Function Main(), Fig. 5
void BURSTableGenerator::run() {
  computeLeafStates();
  while (!WorkList.empty()) {
    State *S = WorkList.pop_back_val();
    for (Operator &Op : Operators)
      computeTransitions(&Op, S);
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

  Expected<Rule *> patternToRule(BURSTableGenerator &BURS,
                                 const TreePatternNode &Src,
                                 CostValue Cost = CostValue());
  Expected<Rule *> importPatternToMatch(BURSTableGenerator &BURS,
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

Expected<Rule *> GlobalISelBURGEmitter::patternToRule(
    BURSTableGenerator &BURS, const TreePatternNode &Src, CostValue Cost) {
  if (!Src.isLeaf()) {
    // Look up the operator.
    Record *SrcGIEquivOrNull = nullptr;
    const CodeGenInstruction *SrcGIOrNull = nullptr;
    SrcGIEquivOrNull = findNodeEquiv(Src.getOperator());
    if (!SrcGIEquivOrNull)
      return failedImport("Pattern operator lacks an equivalent Instruction" +
                          explainOperator(Src.getOperator()));
    SrcGIOrNull = getEquivNode(*SrcGIEquivOrNull, Src);

    // Create rules for the children.
    // TODO Do we need to handle immediates and pointer types differently?
    unsigned NumChildren = Src.getNumChildren();
    SmallVector<Rule *, 0> Children(NumChildren);
    for (unsigned I = 0; I != NumChildren; ++I) {
      const TreePatternNode &SrcChild = Src.getChild(I);
      auto RuleOrError = patternToRule(BURS, SrcChild, CostValue());
      if (auto Error = RuleOrError.takeError())
        return Error;
      Children[I] = *RuleOrError;
    }

    // The operators look good: match the opcode
    // InsnMatcher.addPredicate<InstructionOpcodeMatcher>(SrcGIOrNull);
    dbgs() << "  ---> Found operator " << SrcGIOrNull->TheDef->getName()
           << "\n";
    dbgs() << "       " << llvm::to_string(Src) << "\n";
    dbgs() << "       Children: " << NumChildren << "\n";

    OperandList Opnds;
    Opnds.reserve(NumChildren);
    for (auto *R : Children) {
      Opnds.push_back(R->getLHS());
    }
    return BURS.createInstRule(OpcodeValues[SrcGIOrNull], std::move(Opnds),
                               Cost);
  }

  // Handle leafs, like int and register classes, etc.
  if (auto *ChildInt = dyn_cast<IntInit>(Src.getLeafValue())) {
    // TODO Do we need to distinguish between immediate and materialized
    // constants?
    return BURS.createValueRule(ChildInt->getValue(), Cost);
  }

  if (auto *ChildDefInit = dyn_cast<DefInit>(Src.getLeafValue())) {
    auto *ChildRec = ChildDefInit->getDef();

    // Check for register classes.
    if (ChildRec->isSubClassOf("RegisterClass") ||
        ChildRec->isSubClassOf("RegisterOperand"))
      return BURS.createRegClassRule(getInitValueAsRegClass(ChildDefInit),
                                     Cost);

    if (ChildRec->isSubClassOf("Register")) {
      return failedImport("Not yet implemented: register operands " +
                          explainOperator(Src.getOperator()));
    }
  }

  return failedImport("Case not yet handled");
}

Expected<Rule *>
GlobalISelBURGEmitter::importPatternToMatch(BURSTableGenerator &BURS,
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

  int Score = Pat.getPatternComplexity(CGP);

  // Handle the leaf case first.
  if (Src.isLeaf()) {
    Init *SrcInit = Src.getLeafValue();
    if (isa<IntInit>(SrcInit)) {
      dbgs() << "  ---> Leaf is INT value\n";
      dbgs() << "       " << llvm::to_string(Src) << "\n";
      return BURS.createValueRule(cast<IntInit>(SrcInit)->getValue(),
                                  CostValue::fromComplexity(Score));
    }
    return failedImport(
        "Unable to deduce gMIR opcode to handle Src (which is a leaf)");
  }

  return patternToRule(BURS, Src, CostValue::fromComplexity(Score));
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
    if (auto Err = importPatternToMatch(BURS, Pat).takeError()) {
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
