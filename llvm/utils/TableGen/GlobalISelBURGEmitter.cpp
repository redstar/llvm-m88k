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
/// Proebsting 1995, BURS Automata Generation
/// (https://dl.acm.org/doi/pdf/10.1145/203095.203098)
///
/// For the extension of tree parsing to DAGs, see
/// Ertl 1999; Optimal Code Selection in DAGs
/// (https://dl.acm.org/doi/pdf/10.1145/292540.292562)
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

#include "Basic/CodeGenIntrinsics.h"
#include "Common/CodeGenInstruction.h"
#include "Common/CodeGenRegisters.h"
#include "Common/CodeGenTarget.h"
#include "Common/GlobalISel/CXXPredicates.h"
#include "Common/GlobalISel/CodeExpander.h"
#include "Common/GlobalISel/CodeExpansions.h"
#include "Common/GlobalISel/CombinerUtils.h"
#include "Common/GlobalISel/GlobalISelMatchTable.h"
#include "Common/GlobalISel/GlobalISelMatchTableExecutorEmitter.h"
#include "Common/GlobalISel/PatternParser.h"
#include "Common/GlobalISel/Patterns.h"
#include "Common/SubtargetFeatureInfo.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/PointerUnion.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGenTypes/LowLevelType.h"
#include "llvm/CodeGenTypes/MachineValueType.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CodeGenCoverage.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/SaveAndRestore.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include "llvm/TableGen/TableGenBackend.h"
#include <map>
#include <numeric>
#include <queue>
#include <string>

//===----------------------------------------------------------------------===//
//
// Design notes
//
// Predicates
// A predicate in the DAG pattern can be evaluated in the labeler or the
// matcher, depending on the nature of the predicate. For example, a register
// operand is constraint to have a register class. The check for the register
// class can be encoded in the grammar, and thus is encoded in the matcher
// table. The same approach does not work for integer values, because there can
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

//===- Copied parts BEGIN -------------------------------------------------===//

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

//===- Copied parts END ---------------------------------------------------===//

//===- Code generation ----------------------------------------------------===//

class CGLowLevelType {
  LLT Ty;
  unsigned ID;

  static DenseMap<LLT, CGLowLevelType *> UsedLLTs;

protected:
  CGLowLevelType(LLT Ty, unsigned ID) : Ty(Ty), ID(ID) {}

public:
  static CGLowLevelType *get(LLT Ty) {
    if (auto It = UsedLLTs.find(Ty); It != UsedLLTs.end()) {
      return It->second;
    }
    return UsedLLTs[Ty] = new CGLowLevelType(Ty, UsedLLTs.size());
  }

  void Profile(FoldingSetNodeID &ID) { ID.AddInteger(this->ID); }

  void emit(raw_ostream &OS) const { emit(OS, Ty); }

  LLT type() const { return Ty; }

private:
  static void emit(raw_ostream &OS, LLT Ty) {
    OS << "LLT::";
    if (Ty.isVector()) {
      OS << "vector(" << Ty.getElementCount() << ", ";
      emit(OS, Ty.getElementType());
      OS << ")";
    } else if (Ty.isPointer()) {
      OS << "pointer(" << Ty.getAddressSpace() << ", "
         << Ty.getScalarSizeInBits() << ")";
    } else {
      assert(Ty.isScalar() && "Unexpected LL type");
      OS << "scalar(" << Ty.getScalarSizeInBits() << ")";
    }
  }
};

DenseMap<LLT, CGLowLevelType *> CGLowLevelType::UsedLLTs;

//===- BURS table generator -----------------------------------------------===//

// Use descriptive type names for the various numbers.
using NonterminalNum = unsigned;
using OperatorNum = unsigned;
using RuleNum = unsigned;
using StateNum = unsigned;

// The set of all matching rules is modelled as a bit vector.
using RuleSet = BitVector;

class alignas(8) Nonterminal {
  NonterminalNum Num;

public:
  Nonterminal(NonterminalNum Num) : Num(Num) {}
  NonterminalNum getNum() const { return Num; }
};

using OperandList = SmallVector<Nonterminal *, 2>;

class State;

// A multi-dimensional table.
// The class mimicks a multi-dimensional array in C, which means access is
// row-major. The underlying data can be used to initialize a C array.
template <class T> class Table {
  // The payload as a 1-dimensional array.
  OwningArrayRef<T> Data;

  // The high bound of each dimension.
  OwningArrayRef<unsigned> Dim;

  static size_t memsize(ArrayRef<unsigned> Dimensions) {
    size_t MemSize = Dimensions[0];
    for (unsigned I = 1, E = Dimensions.size(); I < E; ++I)
      MemSize *= Dimensions[I];
    return MemSize;
  }

  static size_t element(ArrayRef<unsigned> AccessVec, ArrayRef<unsigned> Dim) {
    assert(AccessVec.size() == Dim.size() &&
           "Table dimension and access vector does not match");
    size_t Idx = AccessVec[0];
    for (unsigned I = 1, E = Dim.size(); I < E; ++I) {
      Idx *= Dim[I];
      Idx += AccessVec[I];
    }
    return Idx;
  }

  static void dump(ArrayRef<unsigned> A) {
    llvm::dbgs() << "[";
    for (unsigned I = 0, E = A.size(); I < E; ++I) {
      if (I)
        llvm::dbgs() << ", ";
      llvm::dbgs() << A[I];
    }
    llvm::dbgs() << "]";
  }

public:
  Table(unsigned Arity) : Dim(Arity) {
    assert(Arity > 0 && "Table requires arity greater than 0");
    std::fill(Dim.begin(), Dim.end(), 0);
    // llvm::dbgs() << "Table " << this << " has " << Arity << " dimensions\n";
  }

  ArrayRef<T> getData() const { return Data; }
  ArrayRef<unsigned> getDim() const { return Dim; }

  T &getCell(ArrayRef<unsigned> AccessVec) { return getCell(AccessVec, Dim); }

private:
  T &getCell(ArrayRef<unsigned> AccessVec, ArrayRef<unsigned> Dim) {
    assert(AccessVec.size() > 0 && "Access vector must have size > 0");
    // llvm::dbgs() << "Table " << this << ": getCell(";
    // dump(AccessVec);
    // llvm::dbgs() << ") with current bounds ";
    // dump(Dim);
    // llvm::dbgs() << "\n";
    size_t Idx = element(AccessVec, Dim);
    // llvm::dbgs() << "   Calculated index is " << Idx << " with memory size "
    //             << Data.size() << "\n";
    return Data[Idx];
  }

public:
  void extend(ArrayRef<unsigned> NewDim) {
    // llvm::dbgs() << "Table " << this << ": extend(";
    // dump(NewDim);
    // llvm::dbgs() << ") from current bounds ";
    // dump(Dim);
    // llvm::dbgs() << "\n";
    // Assumption: Dimensions only become larger.
    assert(NewDim.size() == Dim.size() && "Cannot change number of dimensions");
    size_t OldSize = memsize(Dim);
    size_t NewSize = memsize(NewDim);
    // No change of size implies no change (under given assumptions).
    if (OldSize == NewSize)
      return;
    // If the old size is zero, then just allocate the memory and update the
    // high bounds of the dimensions.
    if (OldSize == 0) {
      Data = OwningArrayRef<T>(NewSize);
      std::fill(Data.begin(), Data.end(), ~0);
      std::copy(NewDim.begin(), NewDim.end(), Dim.begin());
      return;
    }
    // Extend the array and copy over the data.
    OwningArrayRef<T> OldData = std::move(Data);
    Data = OwningArrayRef<T>(NewSize);
    std::fill(Data.begin(), Data.end(), ~0);
    SmallVector<unsigned, 3> Vec(0);
    Vec.resize(Dim.size());
    for (size_t I = 0; I < OldSize; ++I) {
      getCell(Vec, NewDim) = OldData[I];
      // llvm::dbgs() << "   Assigned value is " << OldData[I] << "\n";
      unsigned D = Vec.size();
      while (D > 0) {
        --D;
        if (++Vec[D] < Dim[D])
          break;
        Vec[D] = 0;
      }
    }
    std::copy(NewDim.begin(), NewDim.end(), Dim.begin());
  }
};

// A operator can be either an instruction, a register class, or an integer
// type. The mapping to representer states and the representer states are part
// of the operator data. Note that the actual values for the operands are part
// of the rules which use this operator.
class alignas(8) Operator : public FoldingSetNode {
public:
  // Kind of operators.
  // TODO Add predicate(s)?
  enum TypeKind { Op_Inst, Op_RegClass, Op_Value };

protected:
  TypeKind Kind;

private:
  OperatorNum Num;

  // If Kind == Op_Inst: pointer to instruction.
  const CodeGenInstruction *Inst;

  // If Kind == Op_RegClass: pointer to register class.
  Record *RegClass;

  // If Kind == Op_RegClass or Kind == Op_Value: the associated type.
  CGLowLevelType *Type;

  // If Kind == Op_Value: the constant value.
  int IntValue;

  // Arity of this operator.
  unsigned Arity;

  // The mapping from state to representer state for each dimension.
  SmallVector<DenseMap<State *, State *>, 0> Map;

  // The mapping from a representer state to a unique number.
  SmallVector<DenseMap<State *, unsigned>, 0> Reps;

  // State of operator if leaf.
  State *LeafState = nullptr;

  // The transition table.
  Table<unsigned> *Transitions = nullptr;

public:
  Operator(OperatorNum Num, const CodeGenInstruction *Inst, unsigned Arity)
      : Kind(Op_Inst), Num(Num), Inst(Inst), RegClass(nullptr), Type(nullptr),
        IntValue(0), Arity(Arity) {
    Map.resize(Arity);
    Reps.resize(Arity);
    if (Arity > 0)
      Transitions = new Table<unsigned>(Arity);
  }
  Operator(OperatorNum Num, Record *RegClass, CGLowLevelType *Type)
      : Kind(Op_RegClass), Num(Num), Inst(nullptr), RegClass(RegClass),
        Type(Type), IntValue(0), Arity(0) {}
  Operator(OperatorNum Num, int IntValue, CGLowLevelType *Type)
      : Kind(Op_Value), Num(Num), Inst(nullptr), RegClass(nullptr), Type(Type),
        IntValue(IntValue), Arity(0) {}

  void Profile(FoldingSetNodeID &ID) const {
    ID.AddInteger(unsigned(Kind));
    switch (Kind) {
    case Op_Inst:
      ID.AddPointer(Inst->TheDef);
      ID.AddInteger(Arity);
      break;
    case Op_RegClass:
      ID.AddPointer(RegClass);
      ID.Add(Type);
      break;
    case Op_Value:
      ID.AddInteger(IntValue);
      ID.Add(Type);
      break;
    }
  }

  OperatorNum getNum() const { return Num; }

  const CodeGenInstruction *getInst() const {
    assert(isInst() && "Expecting a valid instruction for an Operator!");
    return Inst;
  };
  Record *getRegClass() const {
    assert(isRegClass() && "Expecting a valid register class for an Operator!");
    return RegClass;
  }
  CGLowLevelType *getType() const {
    assert((isRegClass() || isValue()) &&
           "Must be a register class or a value when getting the type for an "
           "Operator!");
    return Type;
  }
  int getIntValue() const {
    assert(isValue() && "Expecting Operator to be a value!");
    return IntValue;
  }

  void setLeafState(State *S) { LeafState = S; }
  State *getLeafState() const { return LeafState; }

  unsigned arity() const { return Arity; }

  SmallVectorImpl<DenseMap<State *, State *>> &getMap() { return Map; };
  SmallVectorImpl<DenseMap<State *, unsigned>> &getReps() { return Reps; };
  Table<unsigned> &getTransitions() {
    assert(Transitions && "Transition table requires arity > 0");
    return *Transitions;
  }

  TypeKind getKind() const { return Kind; }
  bool isInst() const { return Kind == Op_Inst; }
  bool isRegClass() const { return Kind == Op_RegClass; }
  bool isValue() const { return Kind == Op_Value; }

  void dump(raw_ostream &OS);
};

class Rule {
  // The DAG pattern this rule is derived from. Only valid for the root element.
  const PatternToMatch *Pat;

  // The left hand side of the rule.
  Nonterminal *LHS;

  // The right hand side of the rule.
  // In normal form, we can have either a chain rule or an operator as the right
  // hand side.
  PointerUnion<Nonterminal *, Operator *> RHS;

  // The operands in case the right hand side is an operator.
  OperandList Operands;

  // The rule number.
  RuleNum Num;

public:
  Rule(RuleNum Num, Nonterminal *LHS, Operator *RHS, OperandList &&Operands,
       const PatternToMatch *Pat)
      : Pat(Pat), LHS(LHS), RHS(RHS), Operands(std::move(Operands)), Num(Num) {}
  Rule(RuleNum Num, Nonterminal *LHS, Nonterminal *RHS,
       const PatternToMatch *Pat)
      : Pat(Pat), LHS(LHS), RHS(RHS), Num(Num) {}

  const PatternToMatch *getPattern() const { return Pat; }
  void setPattern(const PatternToMatch *Pattern) { Pat = Pattern; }
  Nonterminal *getLHS() const { return LHS; }

  // Predicates which can be used with make_filter_range().
  static bool isChainRule(const Rule *R) { return R->RHS.is<Nonterminal *>(); }
  static bool isOperatorRule(const Rule *R) { return !isChainRule(R); }

  Nonterminal *getDerivedNonterminal() const {
    assert(isChainRule(this) && "Rule is not a chain rule");
    return RHS.get<Nonterminal *>();
  }

  bool derivesLeaf() {
    if (RHS.is<Operator *>())
      return RHS.get<Operator *>()->arity() == 0;
    return false;
  }

  Operator *getOperator() const { return RHS.get<Operator *>(); }
  bool hasOperator(const Operator *Op) const {
    return !isChainRule(this) && getOperator() == Op;
  }
  const OperandList &getOperands() const { return Operands; }

  RuleNum getNum() const { return Num; }
};

class State : public FoldingSetNode {

  // An ItemSet is a mapping from a nonterminal to the set of matching rules.
  // The only reason for an ordered map is the ordered enumeration required for
  // the lookup in the FoldingSet.
  using ItemSet = std::map<NonterminalNum, RuleSet>;

  // The items of this state.
  ItemSet Items;

  // The state number.
  StateNum Num;

  // The size of a rule set.
  size_t RuleSetSize;

public:
  explicit State(StateNum Num, size_t RuleSetSize)
      : Num(Num), RuleSetSize(RuleSetSize) {}
  State(State &&Other) = default;

  void Profile(FoldingSetNodeID &ID) const {
    for (auto &[NT, Rules] : Items) {
      ID.AddInteger(NT);
      for (auto BitPart : Rules.getData())
        ID.AddInteger(BitPart);
    }
  }

  StateNum getNum() const { return Num; }

  bool contains(const Nonterminal *NT) const {
    auto It = Items.find(NT->getNum());
    return It != Items.end();
  }

  RuleSet getRules(const Nonterminal *NT) const {
    auto It = Items.find(NT->getNum());
    if (It != Items.end())
      return It->second;
    return RuleSet(RuleSetSize);
  }

  // Add rule R to the items of nonterminal NT.
  // Returns true if the set was updated.
  bool update(const Nonterminal *NT, const Rule *R) {
    RuleSet &RS = Items[NT->getNum()];
    RS.resize(RuleSetSize);
    if (RS.test(R->getNum()))
      return false;
    RS.set(R->getNum());
    return true;
  }

  void dump(raw_ostream &OS, bool IsYAML = false) {
    if (IsYAML) {
      OS << "State:\n";
      OS << "  Num: " << Num << "\n";
      OS << "  ItemSets:\n";
      for (const auto &[NT, Rules] : Items) {
        OS << "    " << NT << ": [ ";
        bool IsFirst = true;
        for (unsigned B : Rules.set_bits()) {
          OS << (IsFirst ? "" : ", ") << B;
          IsFirst = false;
        }
        OS << " ]\n";
      }
    } else {
      OS << "State " << Num << ":";
      for (const auto &[NT, Rules] : Items) {
        OS << " [ nt " << NT << ": [ ";
        bool IsFirst = true;
        for (unsigned B : Rules.set_bits()) {
          OS << (IsFirst ? "" : ", ") << B;
          IsFirst = false;
        }
        OS << " ]]";
      }
    }
  }
};

class BURSTableGenerator {
  // Set of all operators.
  FoldingSetVector<Operator> Operators;

  // List of all nonterminals.
  SmallVector<Nonterminal *, 0> Nonterminals;

  // Caching of leaf operators.
  DenseMap<Operator *, Rule *> OperatorToRule;

  // Set of all states.
  FoldingSetVector<State> States;

  // Set of all projected states.
  FoldingSetVector<State> ProjectedStates;

  // List of all rules.
  SmallVector<Rule *, 0> Rules;

  // Subsets of all rules.
  SmallVector<Rule *, 0> OperatorRules;
  SmallVector<Rule *, 0> ChainRules;

  // The goal symbol of the grammar.
  Nonterminal *Goal;

  // Work list containing the discovered stated.
  std::queue<State *> WorkList;

  // Insert element Elem into set Set, and return a pointer to the element.
  // If the element is not in the set, then the element will be inserted, and
  // the element and the flag true are returned. Otherwise, the found element
  // and the flag false are returned, and the element will not be inserted.
  template <typename T>
  std::pair<T *, bool> insert(FoldingSetVector<T> &Set, T &&Elem) {
    FoldingSetNodeID ID;
    ID.Add(Elem);
    void *InsertPoint;
    if (T *Tmp = Set.FindNodeOrInsertPos(ID, InsertPoint))
      return std ::pair<T *, bool>(Tmp, false);
    T *NewElem = new T(std::move(Elem));
    Set.InsertNode(NewElem, InsertPoint);
    return std ::pair<T *, bool>(NewElem, true);
  }

  Rule *createRule(Operator *Op, OperandList &&Operands);

public:
  BURSTableGenerator();
  Rule *createValueRule(int Value, CGLowLevelType *Type);
  Rule *createInstRule(const CodeGenInstruction *Inst, OperandList &&Opnds);
  Rule *createRegClassRule(Record *RC, CGLowLevelType *Type);
  Rule *createChainRule(Nonterminal *A, Nonterminal *B,
                        const PatternToMatch *Pat = nullptr);

  Nonterminal *getGoal();
  void closure(State &S);
  void computeLeafStates();
  State *project(Operator *Op, unsigned Idx, State *S);
  void computeTransitions(Operator *Op, State *S);
  void run();

  void dump(raw_ostream &OS);

  // TODO Move the emit functionality to new class.
  void emit(raw_ostream &OS, StringRef ClassName, const CodeGenTarget &Target);
private:
  void emitLabel(raw_ostream &OS, StringRef ClassName, const CodeGenTarget &Target);
  void emitReduce(raw_ostream &OS, StringRef ClassName, const CodeGenTarget &Target);
};

BURSTableGenerator::BURSTableGenerator() {
  // Initialize the goal symbol.
  Goal = new Nonterminal(0);
  Nonterminals.push_back(Goal);
}

Rule *BURSTableGenerator::createRule(Operator *Op, OperandList &&Operands) {
  // TODO Use a better data structure.
  for (Rule *R : OperatorRules) {
    if (R->getOperator() == Op && R->getOperands() == Operands)
      return R;
  }

  Nonterminal *NT = new Nonterminal(Nonterminals.size());
  Nonterminals.push_back(NT);
  Rule *R = new Rule(Rules.size(), NT, Op, std::move(Operands), nullptr);
  Rules.push_back(R);
  if (Rule::isOperatorRule(R))
    OperatorRules.push_back(R);
  else
    ChainRules.push_back(R);
  return R;
}

Rule *BURSTableGenerator::createValueRule(int Value, CGLowLevelType *Type) {
  FoldingSetNodeID ID;
  ID.AddInteger(unsigned(Operator::Op_Value));
  ID.AddInteger(Value);
  ID.Add(Type);
  void *InsertPoint;
  Operator *Op = Operators.FindNodeOrInsertPos(ID, InsertPoint);
  if (!Op) {
    unsigned Num = Operators.size();
    Op = new Operator(Num, Value, Type);
    Operators.InsertNode(Op, InsertPoint);
  }

  return createRule(Op, {});
}

Rule *BURSTableGenerator::createInstRule(const CodeGenInstruction *Inst,
                                         OperandList &&Opnds) {
  const unsigned Arity = Opnds.size();
  FoldingSetNodeID ID;
  ID.AddInteger(unsigned(Operator::Op_Inst));
  ID.AddPointer(Inst->TheDef);
  ID.AddInteger(Arity);
  void *InsertPoint;
  Operator *Op = Operators.FindNodeOrInsertPos(ID, InsertPoint);
  if (!Op) {
    unsigned Num = Operators.size();
    Op = new Operator(Num, Inst, Arity);
    Operators.InsertNode(Op, InsertPoint);
  }

  return createRule(Op, std::move(Opnds));
}

Rule *BURSTableGenerator::createRegClassRule(Record *RC, CGLowLevelType *Type) {
  FoldingSetNodeID ID;
  ID.AddInteger(unsigned(Operator::Op_RegClass));
  ID.AddPointer(RC);
  ID.Add(Type);
  void *InsertPoint;
  Operator *Op = Operators.FindNodeOrInsertPos(ID, InsertPoint);
  if (!Op) {
    unsigned Num = Operators.size();
    Op = new Operator(Num, RC, Type);
    Operators.InsertNode(Op, InsertPoint);
  }

  return createRule(Op, {});
}

Rule *BURSTableGenerator::createChainRule(Nonterminal *A, Nonterminal *B,
                                          const PatternToMatch *Pat) {
  Rule *R = new Rule(Rules.size(), A, B, Pat);
  Rules.push_back(R);
  ChainRules.push_back(R);
  llvm::dbgs() << "Added new chain rule " << A->getNum() << " -> "
               << B->getNum() << "\n";
  return R;
}

Nonterminal *BURSTableGenerator::getGoal() { return Goal; }

// Function Closure(), Fig. 8
void BURSTableGenerator::closure(State &S) {
  bool Changed;
  do {
    Changed = false;
    for (const Rule *R : ChainRules) {
      Nonterminal *N = R->getLHS();
      Nonterminal *M = R->getDerivedNonterminal();

      // If nonterminal M is in state S, then add
      // rule R as a match for nonterminal N.
      if (S.contains(M))
        if (S.update(N, R))
          Changed = true;
    }
  } while (Changed);
}

// Function ComputeLeafStates(), Fig. 9
void BURSTableGenerator::computeLeafStates() {
  // Loop over all leaf operators.
  auto LeafOp = [](const Operator &Op) { return Op.arity() == 0; };
  for (Operator &Op : make_filter_range(Operators, LeafOp)) {
    State S(States.size(), Rules.size());

    // Loop over all rules which derives the current leaf operator.
    auto SameOp = [&Op](const Rule *R) { return R->getOperator() == &Op; };
    for (const Rule *R : make_filter_range(OperatorRules, SameOp)) {
      Nonterminal *N = R->getLHS();
      S.update(N, R);
    }
    closure(S);

    // Record the state if not yet known.
    auto [SPtr, Inserted] = insert(States, std::move(S));
    if (Inserted)
      WorkList.push(SPtr);
    Op.setLeafState(SPtr);
  }
}

// Function Project(), Fig. 11
State *BURSTableGenerator::project(Operator *Op, unsigned Idx, State *S) {
  State P(ProjectedStates.size(), Rules.size());
  auto SameOp = [&Op](const Rule *R) { return R->getOperator() == Op; };
  for (const auto *R : make_filter_range(OperatorRules, SameOp)) {
    // Nonterminal NT is used in dimension Idx.
    Nonterminal *NT = R->getOperands()[Idx];
    if (S->contains(NT))
      P.update(NT, R);
  }

  // Record the state if not yet known.
  return insert(ProjectedStates, std::move(P)).first;
}

namespace {
// Enumerate all dimensions except Idx.
// TODO Turn into range.
class Enumerator {
  SmallVector<DenseMap<State *, unsigned>::iterator, 0> Iterators;
  SmallVectorImpl<DenseMap<State *, unsigned>> &Reps;
  unsigned Idx;
  State *S;

  void fill(SmallVectorImpl<State *> &Sets) {
    for (size_t I = 0, E = Reps.size(); I < E; ++I)
      if (I == Idx)
        Sets[I] = S;
      else
        Sets[I] = Iterators[I]->first;
  }

public:
  Enumerator(SmallVectorImpl<DenseMap<State *, unsigned>> &Reps, unsigned Idx,
             State *State)
      : Reps(Reps), Idx(Idx), S(State) {
    Iterators.resize(Reps.size());
  }

  bool first(SmallVectorImpl<State *> &Sets) {
    for (size_t I = 0, E = Reps.size(); I < E; ++I)
      if (I != Idx) {
        Iterators[I] = Reps[I].begin();
        if (Iterators[I] == Reps[I].end())
          return false;
      }
    fill(Sets);
    return true;
  }

  bool next(SmallVectorImpl<State *> &Sets) {
    for (size_t I = 0, E = Reps.size(); I < E; ++I) {
      if (I != Idx) {
        ++Iterators[I];
        if (Iterators[I] != Reps[I].end())
          break;
      }
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
  unsigned OpArity = Op->arity();
  llvm::dbgs() << "computeTransitions for op " << Op->getNum() << " (arity "
               << OpArity << ") and state " << S->getNum() << "\n";
  for (unsigned I = 0, E = OpArity; I < E; ++I) {
    llvm::dbgs() << "Operand " << I << "\n";
    State *P = project(Op, I, S);
    Op->getMap()[I][S] = P;
    auto It = Op->getReps()[I].find(P);
    if (It == Op->getReps()[I].end()) {
      llvm::dbgs() << "  --> representer set not found\n";

      // Add new representer set.
      unsigned RepNum = Op->getReps()[I].size();
      Op->getReps()[I][P] = RepNum;
      llvm::dbgs() << "  --> New representer set " << RepNum << "\n";

      // Extend the transition map.
      SmallVector<unsigned, 3> NewShape;
      NewShape.resize_for_overwrite(OpArity);
      for (unsigned A = 0; A < OpArity; ++A)
        NewShape[A] = Op->getReps()[A].size();
      Op->getTransitions().extend(NewShape);

      // Enumerate all representer set combinations.
      SmallVector<State *, 0> EnumStates;
      EnumStates.resize(OpArity);
      SmallVector<unsigned> TransitionVec;
      TransitionVec.resize(OpArity);
      Enumerator Enum(Op->getReps(), I, P);
      if (Enum.first(EnumStates)) {
        llvm::dbgs() << "  --> Enum states\n";
        do {
          llvm::dbgs() << "  --> Loop over states\n";
          for (unsigned X = 0; X < EnumStates.size(); ++X) {
            llvm::dbgs() << "      -> " << X << ": ";
            EnumStates[X]->dump(llvm::dbgs());
            llvm::dbgs() << "\n";
          }
          State Result(States.size(), Rules.size());
          //  Enumerate all rules with Op.
          auto SameOp = [&Op](const Rule *R) { return R->getOperator() == Op; };
          for (const auto *R : make_filter_range(OperatorRules, SameOp)) {
            // Calculate cost. There is no check if m_i is in op.reps[i],
            // because in this case the cost is infinity, and as conseqeunce the
            // final comparison cost < result[n].cost is false.
            bool Match = true;
            for (unsigned Mi = 0, Me = OpArity; Mi < Me; ++Mi)
              Match &= EnumStates[Mi]->contains(R->getOperands()[Mi]);
            Nonterminal *RuleLHS = R->getLHS();
            if (Match)
              Result.update(RuleLHS, R);
          }

          // TODO Mark core items, and only run closure() on new states after
          // insertion.
          closure(Result);

          // Record the state if not yet known.
          auto [ResultPtr, Inserted] = insert(States, std::move(Result));
          if (Inserted)
            WorkList.push(ResultPtr);

          // Record transition.
          for (unsigned Mi = 0, Me = OpArity; Mi < Me; ++Mi)
            TransitionVec[Mi] = Op->getReps()[Mi][EnumStates[Mi]];
          Op->getTransitions().getCell(TransitionVec) = ResultPtr->getNum();

          llvm::dbgs() << "  --> Transition ";
          llvm::dbgs() << "[";
          for (unsigned Mi = 0, Me = OpArity; Mi < Me; ++Mi) {
            if (Mi)
              llvm::dbgs() << ", ";
            llvm::dbgs() << TransitionVec[Mi];
          }
          llvm::dbgs() << "] = " << ResultPtr->getNum() << "\n";

        } while (Enum.next(EnumStates));
      } else
        llvm::dbgs() << "  --> No state enumeration\n";
    }
  }
}

// Function Main(), Fig. 5
void BURSTableGenerator::run() {
  llvm::dbgs() << "Generate BURS tables\n";
  // State 0 is the error state. This state would be added anyway during the
  // computation of the transitions. Adding it now makes sure it has the number
  // 0, which makes it easy to test for.
  WorkList.push(insert(States, State(0, Rules.size())).first);
  computeLeafStates();
  while (!WorkList.empty()) {
    State *S = WorkList.front();
    WorkList.pop();
    for (Operator &Op : Operators)
      computeTransitions(&Op, S);
  }
}

// Emit label(MachineInstr &).
void BURSTableGenerator::emitLabel(raw_ostream &OS, StringRef ClassName,
                                   const CodeGenTarget &Target) {
  OS << "void " << ClassName << "::label(MachineInstr &MI) {\n";
  OS << "  MachineBasicBlock &MBB = *MI.getParent();\n";
  OS << "  MachineFunction &MF = *MBB.getParent();\n";
  OS << "  MachineRegisterInfo &MRI = MF.getRegInfo();\n";
  OS << "  (void)MRI;\n";
  OS << "  (void)preISelLower(MI);\n";
  OS << "  uint32_t State = 0;\n";
  OS << "  switch (MI.getOpcode()) {\n";
  for (Operator &Op : Operators) {
    if (Op.arity() == 0 && !Op.isInst())
      continue;
    OS << "    case ";
    if (!Op.getInst()->Namespace.empty())
      OS << Op.getInst()->Namespace << "::";
    OS << Op.getInst()->TheDef->getName() << ": {\n";
    if (Op.arity() > 0) {
      OS << "      static const uint16_t Map[" << Op.arity() << "]["
         << States.size() << "] = {\n";
      for (unsigned I = 0, E = Op.arity(); I < E; ++I) {
        unsigned Cnt = 0;
        OS << "        { ";
        for (State &S : States) {
          if ((Cnt % 16) == 0) {
            if (Cnt > 0)
              OS << "\n          ";
            OS << format("/* %4d */ ", Cnt);
          }
          ++Cnt;
          State *P = Op.getMap()[I][&S];
          OS << Op.getReps()[I][P] << ", ";
        }
        OS << "},\n";
      }
      OS << "      };\n";
      OS << "      static const uint16_t Transition";
      auto &Trans = Op.getTransitions();
      for (unsigned I = 0, E = Trans.getDim().size(); I < E; ++I)
        OS << "[" << Trans.getDim()[I] << "]";
      OS << " = {";

      unsigned Cnt = 0;
      for (unsigned I = 0, E = Trans.getData().size(); I < E; ++I) {
        if ((Cnt % 16) == 0) {
          OS << "\n        ";
          OS << format("/* %4d */ ", Cnt);
        }
        ++Cnt;
        if (Trans.getData()[I] == ~0U)
          OS << "~0U, ";
        else
          OS << Trans.getData()[I] << ", ";
      }

      OS << "\n      };\n";
      for (unsigned I = 0, E = Op.arity(); I < E; ++I)
        OS << "      uint16_t Op" << I << " = Map[" << I
           << "][label(MRI, TRI, RBI, MI.getOperand(" << (I + 1) << "))];\n";
      OS << "      State = Transition";
      for (unsigned I = 0, E = Op.arity(); I < E; ++I)
        OS << "[Op" << I << "]";
      OS << ";\n";
    } else {
      OS << "      // Instruction with no operands.\n";
    }
    OS << "      break;\n";
    OS << "    }\n";
  }
  OS << "    StateMap[&MI] = State;\n";
  OS << "  }\n";
  OS << "}\n";
}

// Emit reduce(MachineInstr &).
void BURSTableGenerator::emitReduce(raw_ostream &OS, StringRef ClassName,
                                    const CodeGenTarget &Target) {
  OS << "bool " << ClassName << "::reduce(MachineInstr &I) {\n";
  OS << "  if (earlySelect(MI))\n";
  OS << "    return true;\n";
  OS << "  uint32_t State = StateMap[&MI];\n";
  OS << "  switch (State) {\n";
  for (auto &S : States) {
    OS << "    // ";
    S.dump(OS);
    OS << "\n";
    RuleSet RSet = S.getRules(getGoal());
    if (RSet.any()) {
      for (int RNo = RSet.find_first(); RNo != -1; RNo = RSet.find_next(RNo)) {
        Rule *R = Rules[RNo];
        if (R->getPattern()) {
          OS << "    case " << S.getNum() << ":\n";
          OS << "    // Match: "
             << llvm::to_string(R->getPattern()->getSrcPattern()) << "\n";
        }
      }
    }
  }
  OS << "  \n";
  OS << "  }\n";
  OS << "  return select(MI);\n";
  OS << "}\n";
}

void BURSTableGenerator::emit(raw_ostream &OS, StringRef ClassName,
                              const CodeGenTarget &Target) {
  OS << "#ifdef GET_GLOBALISEL_DECL\n";
  OS << "void label(MachineInstr &I) override;\n";
  OS << "void reduce(MachineInstr &I) override;\n";
  OS << "#endif\n";
  OS << "#ifdef GET_GLOBALISEL_IMPL\n";

  OS << "namespace {\n";
  // Emit label(MachineRegisterInfo &, TargetRegisterInfo &, RegisterBankInfo &,
  // Register).
  OS << "uint32_t label(MachineRegisterInfo &MRI, const TargetRegisterInfo "
        "&TRI,\n";
  OS << "               const RegisterBankInfo &RBI, Register Reg) {\n";
  OS << "  LLT Ty = MRI.getType(Reg);\n";
  OS << "  const RegisterBank *RegBank = RBI.getRegBank(Reg, MRI, TRI);\n";
  OS << "  // TODO Calculate RegisterBank at TableGen-time.\n";
  for (auto Op : Operators) {
    State *Leaf = Op.getLeafState();
    if (Leaf == nullptr || !Op.isRegClass())
      continue;
    OS << "  if (Ty == ";
    Op.getType()->emit(OS);
    OS << " && RegBank == &RBI.getRegBankFromRegClass("
       << Target.getRegisterClass(Op.getRegClass()).getQualifiedName()
       << ", Ty))\n";
    OS << "    return " << Leaf->getNum() << ";\n";
  }
  OS << "  return 0;\n";
  OS << "}\n";

  // Emit label(MachineRegisterInfo &, TargetRegisterInfo &, RegisterBankInfo &,
  // MachineOperand &).
  OS << "uint32_t label(MachineRegisterInfo &MRI, const TargetRegisterInfo "
        "&TRI,\n";
  OS << "               const RegisterBankInfo &RBI, MachineOperand &MO) {\n";
  OS << "  if (MO.isReg()) {\n";
  OS << "    MachineInstr *DefMI = getDefIgnoringCopies(MO.getReg(), MRI);\n";
  OS << "    if (auto It = StateMap.find(DefMI); It != StateMap.end())\n";
  OS << "      return It->second;\n";
  OS << "    return label(MRI, TRI, RBI, MO.getReg());\n";
  OS << "  }\n";
  OS << "  if (MO.isImm()) {\n";
  OS << "    uint64_t Val = MO.getCImm()->getZExtValue();\n";
  OS << "    (void)Val;\n";
  for (auto Op : Operators) {
    State *Leaf = Op.getLeafState();
    if (Leaf == nullptr || !Op.isValue())
      continue;
    OS << "    if (Ty == ";
    Op.getType()->emit(OS);
    OS << " && Val == "
       << Op.getIntValue()
       << ")\n";
    OS << "      return " << Leaf->getNum() << ";\n";
  }
  OS << "  }\n";
  OS << "  // TODO Handle other cases.\n";
  OS << "  return 0;\n";
  OS << "}\n";
  OS << "} // End of anonymous namespace.\n";

  emitLabel(OS, ClassName, Target);
  emitReduce(OS, ClassName, Target);

  OS << "#endif\n";
}

void Operator::dump(raw_ostream &OS) {
  unsigned MaxStateNo = 0;
  for (const auto &Dim : Map)
    for (const auto &[S, P] : Dim)
      MaxStateNo = std::max(MaxStateNo, S->getNum());
  ++MaxStateNo;
  SmallVector<unsigned, 0> TmpMap;
  TmpMap.resize(MaxStateNo);
  OS << "Operator:\n";
  OS << "  Num: " << Num << "\n";
  if (isInst()) {
    OS << "  Name: \"";
    if (!Inst->Namespace.empty())
      OS << Inst->Namespace << "::";
    OS << Inst->TheDef->getName() << "\"\n";
    OS << "  Arity: " << Arity << "\n";
  }
  if (Arity) {
    OS << "  Map:\n";
    for (unsigned Dim = 0; Dim < Arity; ++Dim) {
      OS << "      - Dim" << Dim << ": [ ";
      for (unsigned I = 0, E = MaxStateNo; I < E; ++I)
        TmpMap[I] = 0;
      for (auto &[S, P] : Map[Dim])
        TmpMap[S->getNum()] = Reps[Dim][P];
      for (unsigned I = 0, E = MaxStateNo; I < E; ++I) {
        if (I)
          OS << ", ";
        OS << TmpMap[I];
      }
      OS << " ]\n";
    }

    OS << "  Transition:\n";
    OS << "    Dimension: [ ";
    for (unsigned I = 0, E = Transitions->getDim().size(); I < E; ++I) {
      if (I)
        OS << ", ";
      OS << Transitions->getDim()[I];
    }
    OS << " ]\n";
    OS << "    Data: [ ";
    for (unsigned I = 0, E = Transitions->getData().size(); I < E; ++I) {
      if (I)
        OS << ", ";
      if (Transitions->getData()[I] == ~0U)
        OS << "~0U";
      else if (Transitions->getData()[I] == static_cast<unsigned>(-1))
        OS << "-1";
      else
        OS << Transitions->getData()[I];
    }
    OS << " ]\n";
  } else {
    if (isRegClass())
      OS << "  RegisterClass: \"" << RegClass->getName() << "\"\n";
    if (isValue())
      OS << "  IntValue: " << IntValue << "\n";
    if (isRegClass() || isValue()) {
      OS << "  Type: ";
      getType()->type().print(OS);
      OS << "\n";
    }
    OS << "  State: " << LeafState->getNum() << "\n";
  }
}

void BURSTableGenerator::dump(raw_ostream &OS) {
  OS << "//"
        "===-------------------------------------------------------------------"
        "---===//\n";
  OS << "Operators: " << Operators.size() << "\n";
  OS << "Nonterminals: " << Nonterminals.size() << "\n";
  OS << "Rules: " << Rules.size() << "\n";
  OS << "States: " << States.size() << "\n";
  OS << "Projected states: " << ProjectedStates.size() << "\n";
  for (Operator &Op : Operators) {
    Op.dump(OS);
  }
  for (State &S : States) {
    S.dump(OS, true);
  }
  OS << "//"
        "===-------------------------------------------------------------------"
        "---===//\n";
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

  Expected<CGLowLevelType *> getLLT(const TypeSetByHwMode &VTy,
                                    bool OperandIsAPointer);

  Expected<Rule *> patternToRule(BURSTableGenerator &BURS,
                                 const TreePatternNode &Src);
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

//===- Copied parts BEGIN -------------------------------------------------===//

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

//===- Copied parts END ---------------------------------------------------===//

Expected<CGLowLevelType *>
GlobalISelBURGEmitter::getLLT(const TypeSetByHwMode &VTy,
                              bool OperandIsAPointer) {
  if (!VTy.isMachineValueType())
    return failedImport("unsupported typeset");

  // TODO It is currently unclear how to support iPTR.
  if (VTy.getMachineValueType() == MVT::iPTR && OperandIsAPointer) {
    return failedImport("iPTR not supported");
  }

  LLT Ty = LLT(VTy.getMachineValueType().SimpleTy);

  if (OperandIsAPointer)
    return CGLowLevelType::get(LLT::pointer(0, Ty.getSizeInBits()));
  if (VTy.isPointer())
    return CGLowLevelType::get(
        LLT::pointer(VTy.getPtrAddrSpace(), Ty.getSizeInBits()));
  return CGLowLevelType::get(Ty);
}

Expected<Rule *>
GlobalISelBURGEmitter::patternToRule(BURSTableGenerator &BURS,
                                     const TreePatternNode &Src) {
  if (!Src.isLeaf()) {
    // Look up the operator.
    Record *SrcGIEquivOrNull = nullptr;
    const CodeGenInstruction *SrcGIOrNull = nullptr;
    SrcGIEquivOrNull = findNodeEquiv(Src.getOperator());
    if (!SrcGIEquivOrNull)
      return failedImport("Pattern operator lacks an equivalent Instruction" +
                          explainOperator(Src.getOperator()));
    SrcGIOrNull = getEquivNode(*SrcGIEquivOrNull, Src);

//    unsigned OpIdx = 0;
    for (const TypeSetByHwMode &VTy : Src.getExtTypes()) {
//      const bool OperandIsAPointer =
//          SrcGIOrNull && SrcGIOrNull->isOutOperandAPointer(OpIdx);
      llvm::dbgs() << "TypeSetByHwMode: ";
      if (VTy.getMachineValueType().SimpleTy == MVT::i8)
        llvm::dbgs() << "i8";
      if (VTy.getMachineValueType().SimpleTy == MVT::i32)
        llvm::dbgs() << "i32";
      if (VTy.getMachineValueType().SimpleTy == MVT::i64)
        llvm::dbgs() << "i64";
      if (VTy.getMachineValueType().SimpleTy == MVT::f32)
        llvm::dbgs() << "f32";
      if (VTy.getMachineValueType().SimpleTy == MVT::f64)
        llvm::dbgs() << "f64";
      llvm::dbgs() << "\n";
    }

    // Create rules for the children.
    // TODO Do we need to handle immediates and pointer types differently?
    unsigned NumChildren = Src.getNumChildren();
    SmallVector<Rule *, 0> Children(NumChildren);
    for (unsigned I = 0; I != NumChildren; ++I) {
      const TreePatternNode &SrcChild = Src.getChild(I);
      auto RuleOrError = patternToRule(BURS, SrcChild);
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
    return BURS.createInstRule(SrcGIOrNull, std::move(Opnds));
  }

  ArrayRef<TypeSetByHwMode> ChildTypes = Src.getExtTypes();
  if (ChildTypes.size() != 1)
    return failedImport("Src pattern child has multiple results");
  Expected<CGLowLevelType *> ChildType =
      getLLT(ChildTypes.front(), /*OperandIsAPointer=*/false);
  if (!ChildType)
    return ChildType.takeError();

  // Handle leafs, like int and register classes, etc.
  Init *SrcLeaf = Src.getLeafValue();
  if (auto *ChildInt = dyn_cast<IntInit>(SrcLeaf)) {
    // TODO What about the RegisterBank?
    return BURS.createInstRule(
        &Target.getInstruction(RK.getDef("G_CONSTANT")),
        {BURS.createValueRule(ChildInt->getValue(), *ChildType)->getLHS()});
  }

  if (auto *ChildDefInit = dyn_cast<DefInit>(SrcLeaf)) {
    auto *ChildRec = ChildDefInit->getDef();

    // Check for register classes.
    if (ChildRec->isSubClassOf("RegisterClass") ||
        ChildRec->isSubClassOf("RegisterOperand"))
      return BURS.createRegClassRule(getInitValueAsRegClass(ChildDefInit),
                                     *ChildType);

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

  // TODO Add score to rule.
  // int Score = Pat.getPatternComplexity(CGP);

  Rule *R;
  // Handle the leaf case first.
  if (Src.isLeaf()) {
    Init *SrcInit = Src.getLeafValue();
    if (isa<IntInit>(SrcInit)) {
      dbgs() << "  ---> Leaf is INT value\n";
      dbgs() << "       " << llvm::to_string(Src) << "\n";
      // TODO What about the RegisterBank? Where to find the correct type?
      R = BURS.createInstRule(
          &Target.getInstruction(RK.getDef("G_CONSTANT")),
          {BURS.createValueRule(cast<IntInit>(SrcInit)->getValue(),
                                CGLowLevelType::get(LLT::scalar(32)))
               ->getLHS()});
    } else
      return failedImport(
          "Unable to deduce gMIR opcode to handle Src (which is a leaf)");
  } else {
    Expected<Rule *> ChildRule = patternToRule(BURS, Src);
    if (!ChildRule)
      return ChildRule;
    R = *ChildRule;
  }
  R->setPattern(&Pat);
  return BURS.createChainRule(BURS.getGoal(), R->getLHS(), &Pat);
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
  llvm::dbgs() << "Computing tables...\n";
  BURS.run();
  BURS.dump(dbgs());

  emitSourceFileHeader(
      ("Global Instruction Selector for the " + Target.getName() + " target")
          .str(),
      OS);

  BURS.emit(OS, getClassName(), getTarget());
}
} // end anonymous namespace

//===----------------------------------------------------------------------===//

static TableGen::Emitter::OptClass<GlobalISelBURGEmitter>
    X("gen-global-isel-burg", "Generate GlobalISel BURG selector");
