//===- GIMatchTree.cpp - A decision tree to match GIMatchDag's ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Generate a bottom-up tree matcher as described by Chase (1987).
///
/// The basic idea of a bottom-up matcher is to associate with each instruction
/// the set of matching patterns, called the match set. For an instruction
/// without use operands (a leaf) the match set is easily determined. For any
/// other instruction, the match set is retrieved with a table lookup, using the
/// use operands as table indices. As a result, all matching patterns can be
/// found in linear time.
///
/// All patterns to match are known at compile. From these patterns, the match
/// sets and the table lookups are constructed. The algorithm was first
/// described by Hoffmann and O'Donnel.
///  - First enumerate the pattern forest (the set of all subpatterns), and
///    assign a number to each pattern
///  - Then calculate the match sets. First, the match sets of patterns with
///    height 0 are calculated. Based on the result, patterns of height 1 can be
///    calculated, and so on.
///  - Finally, the lookup tables con be constructed.
///
/// The main disadvantage of this algorithm is that the tables can get very
/// large. This affects the preprocessing time and space requirements in the
/// resulting matcher. Chase modified the algorithm to include compression of
/// the tables. The basic idea is to define an equivalence relation on the set
/// of of patterns, which can appear as subpatterns of a pattern. Using these
/// representer sets, the calculation is speed up, and the tables are much
/// smaller.
///
/// The modification to the algorithm includes:
///  - The representer sets are calculated along the match sets, and the
///    calculation of the match sets uses the representer sets.
///  - The lookup tables are only computed for the representer sets.
///  - An additional mapping from the match sets to the representer sets is
///    required.
///
/// Implementation notes
/// The nodes of the pattern tree are labled with the instruction name. These
/// lables are singletons, and implemented using a FoldingVector.
/// Each pattern is given a numeric encoding. The set of all subpatterns,
/// called the pattern forest, is also implemented using a FoldingSet.
/// A set of patterns is implemented as a BitVector, and also given a numeric
/// encoding. The match sets, which are sets of sets of patterns, are stored in
/// a DenseMap, using the set of patterns as key, and its numerical encoding as
/// value.
/// The implementation assumes that the placeholder * (v in paper of Chase) is
/// always a member of the pattern forest. It further assumes that the
/// placeholder * and the set only containing the placeholder have the encoding
/// 0.
///
/// References:
/// Hoffmann, O'Donnel: Pattern Matching in Trees (1982)
/// https://dl.acm.org/doi/10.1145/322290.322295
///
/// Chase: An Improvement to Bottom-up Tree Pattern Matching (1987)
/// https://dl.acm.org/doi/10.1145/41625.41640
//===----------------------------------------------------------------------===//

#include "GIMatchTreeAutomaton.h"
#include "GIMatchDagPredicate.h"

#include "../CodeGenInstruction.h"

#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"

#include <map>

#define DEBUG_TYPE "gimatchtreeautomaton"

using namespace llvm;

/*
  Some remarks about performance and memory usage

  (a)
  If a dimension of the lookup table is 1 then that dimenion, the corresponding
  row of the compression table, and the corresponding operand can be omitted.

  (b)
  The Label and the Pattern class have 1 or 2 OwningArrayRef members. The size
  of the array is known when the objects are allocated. These additional memory
  allocations can be avoided by managing that memory together with the object.
  E.g.
      static Label *create(const CodeGenInstruction *Inst) {
      unsigned NumOpnds = Inst->Operands.size() - Inst->Operands.NumDefs;
      size_t Ofs = alignTo(sizeof(Label), alignof(BitVector));
      void *Mem = operator new[](Ofs + NumOpnds * sizeof(BitVector));
      BitVector *PAj = reinterpret_cast<BitVector *>(
          reinterpret_cast<unsigned char *>(Mem) + Ofs);
      for (unsigned I = 0, E = NumOpnds; I < E; ++I)
        new (&PAj[I]) BitVector();
      return new (Mem) Label(Inst, MutableArrayRef<BitVector>(PAj, NumOpnds));
    }
  The objects could also be made smaller by exploting the facts that the size of
  the array only need to be stored once, and that the pointer(s) to the array(s)
  are at known offsets from the this pointer.

  (c)
  The implementation does not care about memory management. A context object
  holding a bump allocator could be introduced to free most of the memory after
  the matcher is created.
*/

namespace llvm {

namespace {
// The algorithm requires to enumerate all elements of an n-dimensional set
// product. That is, given sets R_1, ..., R_n, all tuples (r_1, ..., r_n) of
// R_1 x ... x R_n are enumerated.
// For convenience and easy understanding, that enumeration is implemented as a
// C++ range. The template implementation needs to know that type of the set
// (SetT), and the type of the set elements (ElemT). The only other requirement
// is that the set type provides a const_iterator.
// Two specialized version are provided. One uses a BitVector as set type and
// unsigned as element type. This is mainly provided for performance reasons, as
// this range is used in the innermost loop, and the implementeation requires
// less temporary memory. The other version enumerates a set product [0..N_0] x
// ... X [0..N_n] of integer intervals. The rightmost element changes the
// fastest, which is compatible with multi-dimensional C++ arrays.

// This version uses iterators to loop over elements of the sets R_i.
// TODO The implementation is not completely generic - it assumes that the set
// contains key-value pairs as DenseMap does.
template <typename SetT, typename ElemT> class EnumSetRangeImpl {
  const ArrayRef<SetT> &Dimension;
  SmallVector<typename SetT::const_iterator, 3>
      Iter;                   // The iterator for each dimension.
  SmallVector<ElemT, 3> Elem; // The current element for each dimension.
  bool AtEnd;

public:
  EnumSetRangeImpl(const ArrayRef<SetT> &Dimension, bool IsAtEnd = false)
      : Dimension(Dimension), AtEnd(IsAtEnd || !Dimension.size()) {
    if (AtEnd)
      return;

    const size_t Dim = Dimension.size();

    // Make room for the iterators and element data.
    Iter.resize_for_overwrite(Dim);
    Elem.resize_for_overwrite(Dim);

    // Initialize first element. Return if one of the sets is empty.
    for (int I = 0, E = Dim; I < E; ++I) {
      Iter[I] = Dimension[I].begin();
      if (Iter[I] == Dimension[I].end()) {
        AtEnd = true;
        break;
      }
      Elem[I] = Iter[I]->first;
    }
  }

  EnumSetRangeImpl &operator++() {
    assert(!AtEnd && "Incrementing iterator over end");
    for (unsigned I = 0, E = Dimension.size(); I < E; ++I) {
      unsigned Idx = E - I - 1;
      if (++Iter[Idx] != Dimension[Idx].end()) {
        Elem[Idx] = Iter[Idx]->first;
        break;
      }

      // Overflow in the left most position indicates all elements are
      // enumerated.
      if (Idx == 0) {
        AtEnd = true;
        return *this;
      }
      Iter[Idx] = Dimension[Idx].begin();
      Elem[Idx] = Iter[Idx]->first;
    }
    return *this;
  }
  ArrayRef<ElemT> operator*() const { return Elem; }
  bool operator!=(const EnumSetRangeImpl &Other) const {
    assert(Dimension == Other.Dimension && "Comparing different enumerations");
    if (AtEnd != Other.AtEnd)
      return true;
    if (AtEnd && Other.AtEnd)
      return false;
    return Elem != Other.Elem;
  }
};

// Specialization for sets represented as BitVector.
template <> class EnumSetRangeImpl<BitVector, unsigned> {
  const ArrayRef<BitVector> &Dimension;
  SmallVector<unsigned, 3> Elem;
  int AtEnd;

public:
  EnumSetRangeImpl(const ArrayRef<BitVector> &Dimension, bool IsAtEnd = false)
      : Dimension(Dimension), AtEnd(IsAtEnd || !Dimension.size()) {
    if (AtEnd)
      return;

    const size_t Dim = Dimension.size();

    // Make room for the element data.
    Elem.resize_for_overwrite(Dim);

    // Initialize first element. Return if one of the sets is empty.
    for (int I = 0, E = Dim; I < E; ++I) {
      int N = Dimension[I].find_first();
      if (N == -1) {
        AtEnd = true;
        break;
      }
      Elem[I] = N;
    }
  }

  EnumSetRangeImpl &operator++() {
    assert(!AtEnd && "Incrementing iterator over end");
    for (unsigned I = 0, E = Dimension.size(); I < E; ++I) {
      unsigned Idx = E - I - 1;
      int N = Dimension[Idx].find_next(Elem[Idx]);
      if (N != -1) {
        Elem[Idx] = N;
        break;
      }

      // Overflow in the left most position indicates all elements are
      // enumerated.
      if (Idx == 0) {
        AtEnd = true;
        return *this;
      }
      Elem[Idx] = Dimension[Idx].find_first();
    }
    return *this;
  }
  ArrayRef<unsigned> operator*() const { return Elem; }
  bool operator!=(const EnumSetRangeImpl &Other) const {
    assert(Dimension == Other.Dimension && "Comparing different enumerations");
    if (AtEnd != Other.AtEnd)
      return true;
    if (AtEnd && Other.AtEnd)
      return false;
    return Elem != Other.Elem;
  }
};

// Specialization for set product of integer intervals.
template <> class EnumSetRangeImpl<unsigned, unsigned> {
  const ArrayRef<unsigned> &Dimension;
  SmallVector<unsigned, 3> Elem;
  int AtEnd;

public:
  EnumSetRangeImpl(const ArrayRef<unsigned> &Dimension, bool IsAtEnd = false)
      : Dimension(Dimension), AtEnd(IsAtEnd || !Dimension.size()) {
    if (AtEnd)
      return;

    const size_t Dim = Dimension.size();

    // Make room for the element data.
    Elem.resize_for_overwrite(Dim);

    // Initialize first element. Return if one of the sets is empty.
    for (int I = 0, E = Dim; I < E; ++I)
      Elem[I] = 0;
  }

  EnumSetRangeImpl &operator++() {
    assert(!AtEnd && "Incrementing iterator over end");
    for (unsigned I = 0, E = Dimension.size(); I < E; ++I) {
      unsigned Idx = E - I - 1;
      unsigned N = Elem[Idx] + 1;
      if (N < Dimension[Idx]) {
        Elem[Idx] = N;
        break;
      }

      // Overflow in the left most position indicates all elements are
      // enumerated.
      if (Idx == 0) {
        AtEnd = true;
        return *this;
      }
      Elem[Idx] = 0;
    }
    return *this;
  }
  ArrayRef<unsigned> operator*() const { return Elem; }
  bool operator!=(const EnumSetRangeImpl &Other) const {
    assert(Dimension == Other.Dimension && "Comparing different enumerations");
    if (AtEnd != Other.AtEnd)
      return true;
    if (AtEnd && Other.AtEnd)
      return false;
    return Elem != Other.Elem;
  }
};

template <typename SetT, typename ElemT> class EnumSet {

  using iterator = EnumSetRangeImpl<SetT, ElemT>;

  const ArrayRef<SetT> Dimension;

public:
  EnumSet(ArrayRef<SetT> Dimension) : Dimension(Dimension) {}
  iterator begin() { return std::move(iterator(Dimension)); }
  iterator end() { return std::move(iterator(Dimension, true)); }
};

// Emit a multi-dimensional array. The dimenions are given in array Dim, and the
// data is in array Data. The symbols used for opening and closing parenthesis
// must be provided in Paren.
void emitMultiDimTable(raw_ostream &OS, unsigned Indent,
                       const ArrayRef<unsigned> Dim,
                       const ArrayRef<unsigned> Data, StringRef Paren) {
  assert(Dim.size() > 0 && "Expected at least one dimension");
  assert(Paren.size() == 2 && "Expected pair of parenthesis");
  const char PO = Paren[0];
  const char PC = Paren[1];
  const unsigned LastDim = Dim[Dim.size() - 1];

  for (unsigned Idx = 0, End = Data.size(); Idx < End; ++Idx) {
    // Emit prefix: either chain of opening parenthesis, or a comma.
    if (Idx % LastDim)
      OS << ",";
    else {
      if (Idx)
        OS.indent(Indent);
      OS << PO;
      for (unsigned PrevFac = LastDim, I = 0, E = Dim.size() - 1; I < E; ++I) {
        unsigned Fac = PrevFac * Dim[Dim.size() - I - 2];
        if ((Idx % Fac) != 0)
          break;
        Indent += 2;
        OS << "\n";
        OS.indent(Indent) << PO;
        PrevFac = Fac;
      }
    }

    // Emit the data element.
    OS << format(" %u", Data[Idx]);

    // Emit chain of closing parenthesis if required.
    if ((Idx + 1) % LastDim == 0) {
      OS << " " << PC;
      for (unsigned PrevFac = LastDim, I = 0, E = Dim.size() - 1; I < E; ++I) {
        unsigned Fac = PrevFac * Dim[Dim.size() - I - 2];
        if (((Idx + 1) % Fac) != 0) {
          OS << ",\n";
          break;
        }
        Indent -= 2;
        OS << "\n";
        OS.indent(Indent) << PC;
        PrevFac = Fac;
      }
    }
  }
}

// Ouput a BitVector as a sequence of the set bit's number.
raw_ostream &operator<<(raw_ostream &OS, const BitVector &BV) {
  int B = BV.find_first();
  if (B != -1) {
    OS << B;
    while ((B = BV.find_next(B)) != -1)
      OS << ", " << B;
  }
  return OS;
}
} // namespace

class PatternForestBuilder {
  // Each bit vector represents a match set (aka a set of patterns). The value
  // of the map is the encoding of the match set.
  using SetOfSetOfPatterns = DenseMap<BitVector, unsigned>;

  // Data structure to represent the label and the patterns that appear as the
  // j-th child of that label. In Chase's description, a pattern is described as
  // A[p_0, ..., p_n]. This structure store A (the instruction), the set of
  // patterns appearing as children P_A (for every operand j), and the
  // representer set S_A.
  struct Label : public FoldingSetNode {
    const CodeGenInstruction *Inst;

    // P_A_j is the set of patterns which appears as the j-th child of patterns
    // with label A in PF.
    OwningArrayRef<llvm::BitVector> PA;

    // S_A_j is the set of representer set, basically the intersection of the
    // match sets R with P_A_j.
    OwningArrayRef<SetOfSetOfPatterns> SA;

  private:
    Label(const CodeGenInstruction *Inst)
        : Inst(Inst), PA(Inst->Operands.size() - Inst->Operands.NumDefs),
          SA(PA.size()) {}

  public:
    static Label *create(const CodeGenInstruction *Inst) {
      assert(Inst && "Expected instruction");
      return new Label(Inst);
    }

    void Profile(FoldingSetNodeID &ID) const { ID.AddPointer(Inst->TheDef); }

    bool isCommutable() { return Inst->isCommutable; }

    bool isLeaf() { return getNumUseOpnds() == 0; }

    unsigned getNumDefOpnds() const { return Inst->Operands.NumDefs; }
    unsigned getNumUseOpnds() const {
      return Inst->Operands.size() - Inst->Operands.NumDefs;
    }
    unsigned getNumOpnds() const { return Inst->Operands.size(); }

    // Update the P_A sets.
    void updatePA(ArrayRef<unsigned> Opnds) {
      assert(getNumUseOpnds() == Opnds.size() &&
             "Unexpected number of operands");
      for (unsigned J = 0, E = getNumUseOpnds(); J != E; ++J) {
        if (PA[J].size() <= Opnds[J])
          PA[J].resize(Opnds[J] + 1);
        PA[J].set(Opnds[J]);
      }
    }

    // Make sure that the P_A sets all have the same size.
    void normalizePA(unsigned NumOfPatterns) {
      for (unsigned J = 0, E = PA.size(); J < E; ++J) {
        if (PA[J].size() != NumOfPatterns) {
          assert(PA[J].size() <= NumOfPatterns &&
                 "P_A_j larger than number of patterns");
          PA[J].resize(NumOfPatterns);
        }
      }
    }

    // Update the representer sets S_A.
    // Given a match set MS, calculate MS /\ P_A_j for each operand j, and
    // insert the result into S_A_j. Return true if a new element was inserted
    // into S_A_j.
    bool updateSA(const BitVector &MS) {
      bool Changes = false;
      for (unsigned J = 0, E = getNumUseOpnds(); J < E; ++J) {
        BitVector B(MS); // R
        B &= PA[J];      // R /\ P_A_j
        if (B.any()) {
          if (SA[J].insert(std::pair(B, SA[J].size())).second)
            Changes = true;
        }
      }
      return Changes;
    }
  };

  // A pattern, consisting of the label and the children (which are also
  // patterns). In Chase's paper it is A[p_0, ..., p_n]. Each pattern is encoded
  // as an integer. The placeholder * (or v in the paper) is modelled as having
  // no label and no children.
  struct Pattern : public FoldingSetNode {
    const Label *A;
    const OwningArrayRef<unsigned> Opnds;
    const unsigned Enc; // Numeric encoding of the pattern.

  private:
    Pattern(const Label *A, unsigned Enc, ArrayRef<unsigned> Opnds)
        : A(A), Opnds(Opnds), Enc(Enc) {}

  public:
    static Pattern *create(const Label *A, unsigned Enc,
                           ArrayRef<unsigned> Opnds) {
      return new Pattern(A, Enc, Opnds);
    }

    void Profile(FoldingSetNodeID &ID) const {
      ID.AddPointer(A);
      for (unsigned I = 0, E = Opnds.size(); I < E; ++I)
        ID.AddInteger(Opnds[I]);
    }

    void dump();
    void writeYAML(raw_ostream &OS, unsigned Indent) const;
  };

  // The labels are singletons.
  FoldingSet<Label> Labels;

  // Set of all patterns, ordered by encoding. The first slot is the placeholder
  // *.
  FoldingSet<Pattern> Patterns;

  // Number of patterns. Should always be same as Patterns.size().
  unsigned NumOfPatterns;

  // The set of the calculated match sets R.
  SetOfSetOfPatterns MatchSets;

  // Returns the label instance used for the instruction. It ensures that there
  // is exactly one label for it.
  Label *getLabel(const CodeGenInstruction *Inst);

  // Binding information for matching rules.
  SmallVector<GIMatchPatternInfo, 0> MatchingRuleInfos;

  // Mapping between pattern encoding and matching rule info.
  MapVector<unsigned, SmallVector<unsigned, 0>> MatchingRules;

  // Look up a pattern using its label and the subpatterns.
  Pattern *lookup(Label *A, ArrayRef<unsigned> Opnds);

  // Add the pattern A [ Opnds ] to the pattern forest.
  unsigned addPatternToForest(Label *A, ArrayRef<unsigned> Opnds);

  // Update the match set MS with the pattern L [ child patterns ].
  // Returns true if the pattern was found.
  bool updateMatchSetWithPattern(BitVector &MS, Label &L,
                                 ArrayRef<unsigned> ChildPatterns);

#ifndef NDEBUG
  // Dump a match set.
  template <typename T> void dumpMS(T Sets, StringRef Name, unsigned No) const;
#endif

public:
  PatternForestBuilder();
  ~PatternForestBuilder();
  void addPattern(StringRef Name, unsigned RootIdx, const GIMatchDag &MatchDag,
                  void *Data);
  void createMatchSets();
  GIMatchTreeAutomaton *createAutomaton();
  void dump() const;
  void writeYAML(raw_ostream &OS) const;
};

PatternForestBuilder::PatternForestBuilder() : NumOfPatterns(1) {
  Patterns.InsertNode(Pattern::create(nullptr, 0, ArrayRef<unsigned>()));
}

PatternForestBuilder::~PatternForestBuilder() = default;

PatternForestBuilder::Label *
PatternForestBuilder::getLabel(const CodeGenInstruction *Inst) {
  assert(Inst && "Need instruction to create a label");
  FoldingSetNodeID ID;
  ID.AddPointer(Inst->TheDef);
  void *InsertPoint;
  Label *L = Labels.FindNodeOrInsertPos(ID, InsertPoint);
  if (L == nullptr) {
    L = Label::create(Inst);
    Labels.InsertNode(L, InsertPoint);
  }
  return L;
}

void PatternForestBuilder::Pattern::dump() { writeYAML(llvm::dbgs(), 0); }

void PatternForestBuilder::Pattern::writeYAML(raw_ostream &OS,
                                              unsigned Indent) const {
  OS.indent(Indent) << "- " << Enc << ": ";
  if (A) {
    OS << A->Inst->TheDef->getName() << " [";
    for (unsigned I = 0, E = Opnds.size(); I < E; ++I) {
      OS << (I ? ", " : " ") << Opnds[I];
    }
    OS << " ]";
  } else {
    OS << "*";
  }
  OS << "\n";
}

PatternForestBuilder::Pattern *
PatternForestBuilder::lookup(Label *A, ArrayRef<unsigned> Opnds) {
  FoldingSetNodeID ID;
  ID.AddPointer(A);
  for (unsigned I = 0, E = Opnds.size(); I < E; ++I)
    ID.AddInteger(Opnds[I]);
  void *InsertPoint;
  return Patterns.FindNodeOrInsertPos(ID, InsertPoint);
}

unsigned PatternForestBuilder::addPatternToForest(Label *A,
                                                  ArrayRef<unsigned> Opnds) {
  FoldingSetNodeID ID;
  ID.AddPointer(A);
  for (unsigned I = 0, E = Opnds.size(); I < E; ++I)
    ID.AddInteger(Opnds[I]);
  void *InsertPoint;
  Pattern *P = Patterns.FindNodeOrInsertPos(ID, InsertPoint);
  if (P)
    return P->Enc;
  P = Pattern::create(A, NumOfPatterns, Opnds);
  // Udate P_A_j.
  A->updatePA(Opnds);
  Patterns.InsertNode(P, InsertPoint);
  ++NumOfPatterns;
  assert(NumOfPatterns == Patterns.size() && "Counters out of sync");
  return P->Enc;
}

void PatternForestBuilder::addPattern(StringRef Name, unsigned RootIdx,
                                      const GIMatchDag &MatchDag, void *Data) {
  // Mapping from GIMatchDagInstr to outgoing GIMatchDagEdges.
  DenseMap<const GIMatchDagInstr *, std::vector<const GIMatchDagEdge *>> Edges;

  // Mapping from GIMatchDagInstr to associated
  // GIMatchDagPredicateDependencyEdge.
  DenseMap<const GIMatchDagInstr *,
           std::vector<const GIMatchDagPredicateDependencyEdge *>>
      PredEdges;

  // Initializes maps.
  for (auto *Edge : MatchDag.edges()) {
    Edges[Edge->getFromMI()].push_back(Edge);
  }
  for (auto *PredEdge : MatchDag.predicate_edges()) {
    PredEdges[PredEdge->getRequiredMI()].push_back(PredEdge);
  }

  // Lambda to find root element.
  auto getRoot = [&RootIdx, &MatchDag]() -> const GIMatchDagInstr * {
    for (const auto &Root : enumerate(MatchDag.roots())) {
      if (Root.index() == RootIdx)
        return Root.value();
    }
    return nullptr;
  };

  // Lambda to retrieve the opcode predicate for an instruction.
  auto getOpcodePredicate =
      [&](const GIMatchDagInstr *Instr) -> const GIMatchDagOpcodePredicate * {
    for (auto &PredEgde : PredEdges[Instr]) {
      if (auto *P =
              dyn_cast<GIMatchDagOpcodePredicate>(PredEgde->getPredicate())) {
        assert(PredEgde->getRequiredMO() == nullptr && "Unexpected operand");
        return P;
      }
    }
    return nullptr;
  };

  // Recursive lambda to add all edges of tree. It combines 2 traversals:
  //  - It adds instruction/variable bindings in pre-order.
  //  - it adds edges in post-order.
  std::function<unsigned(const GIMatchDagInstr *, GIMatchPatternInfo &,
                         unsigned, unsigned, unsigned, unsigned &)>
      addEdge;
  addEdge = [&](const GIMatchDagInstr *T, GIMatchPatternInfo &Info,
                unsigned BaseInstrID, unsigned FromMoIdx, unsigned Mask,
                unsigned &Count) -> unsigned {
    auto &EdgeList = Edges[T];
    const CodeGenInstruction *Inst = getOpcodePredicate(T)->getInstr();
    Label *A = getLabel(Inst);
    const unsigned MaxOpnds = A->getNumOpnds();
    const unsigned DefOpnds = A->getNumDefOpnds();
    BitVector OperandsWithEdge(MaxOpnds);
    SmallVector<unsigned, 0> Encoding;
    Encoding.resize(MaxOpnds);

    BaseInstrID = Info.add(T, BaseInstrID, FromMoIdx);

    bool SwapOpnds = false;
    if (A->isCommutable()) {
      SwapOpnds = (Mask & (1 << Count)) != 0;
      ++Count;
    }

    for (auto &E : EdgeList) {
      assert(E->getFromMI() == T && "Wrong edge?");

      unsigned Idx = E->getFromMO()->getIdx();
      if (SwapOpnds) {
        if (Idx == DefOpnds)
          Idx = DefOpnds + 1;
        else if (Idx == DefOpnds + 1)
          Idx = DefOpnds;
      }
      unsigned Enc = addEdge(E->getToMI(), Info, BaseInstrID, Idx, Mask, Count);
      Encoding[Idx] = Enc;
      OperandsWithEdge.set(Idx);
    }

    SmallVector<unsigned, 3> Opnds;
    // Add accepting Opnd nodes for all other operands.
    for (auto &Opnd : T->getOperandInfo()) {
      if (Opnd.isDef())
        continue;
      if (OperandsWithEdge[Opnd.getIdx()])
        Opnds.push_back(Encoding[Opnd.getIdx()]);
      else
        Opnds.push_back(0);
    }
    assert(A->getNumUseOpnds() == Opnds.size() && "Wrong number of operands");
    return addPatternToForest(A, Opnds);
  };

  const GIMatchDagInstr *DAGRoot = getRoot();
  assert(DAGRoot != nullptr && "Missing root element of DAG");

  // If DAAGRoot is an instruction, then traverse all edges originating there.
  if (getOpcodePredicate(DAGRoot)) {
    GIMatchPatternInfo Info(Name, Data);
    unsigned Mask = 0;
    unsigned Count = 0;
    unsigned Enc = addEdge(DAGRoot, Info, 0, 0, Mask, Count);
    unsigned BaseInfoId = MatchingRuleInfos.size();
    MatchingRuleInfos.push_back(Info);
    MatchingRules[Enc].push_back(BaseInfoId);
    for (unsigned I = 1, E = 1 << Count; I < E; ++I) {
      GIMatchPatternInfo Info(Name, Data, true);
      Count = 0;
      Enc = addEdge(DAGRoot, Info, 0, 0, I, Count);
      if (MatchingRules.find(Enc) == MatchingRules.end()) {
        unsigned InfoId = MatchingRuleInfos.size();
        MatchingRuleInfos.push_back(Info);
        MatchingRules[Enc].push_back(InfoId);
        MatchingRuleInfos[BaseInfoId].addVariant(InfoId);
      }
    }
  }

  // Process one-of-opcode predicates.
  std::optional<unsigned> InfoId;
  SmallVector<unsigned, 3> Opnds;
  for (auto *PredEdge : PredEdges[DAGRoot]) {
    if (auto *P = dyn_cast<GIMatchDagOneOfOpcodesPredicate>(
            PredEdge->getPredicate())) {
      for (auto *Inst : P->getInstrs()) {
        if (!InfoId) {
          // All matches share the same (empty) variable bindings.
          GIMatchPatternInfo Info(Name, Data);
          Info.add(DAGRoot, 0, 0);
          InfoId = MatchingRuleInfos.size();
          MatchingRuleInfos.push_back(Info);
        }
        Label *A = getLabel(Inst);
        Opnds.resize(A->getNumUseOpnds());
        unsigned Enc = addPatternToForest(A, Opnds);
        MatchingRules[Enc].push_back(*InfoId);
      }
    }
  }
}

bool PatternForestBuilder::updateMatchSetWithPattern(
    BitVector &MS, Label &L, ArrayRef<unsigned> ChildPatterns) {
  if (Pattern *P = lookup(&L, ChildPatterns)) {
    MS.set(P->Enc);
    return true;
  }
  return false;
}

#ifndef NDEBUG
template <typename T>
void PatternForestBuilder::dumpMS(T Sets, StringRef Name, unsigned No) const {
  llvm::dbgs() << Name << "_" << No << " =\n";
  for (auto &MS : Sets) {
    llvm::dbgs() << llvm::format("%6d", MS.second) << " = { " << MS.first
                 << " }\n";
  }
  llvm::dbgs() << "\n";
}
#endif

void PatternForestBuilder::createMatchSets() {
  // Normalize P_A_j, the set of patterns that appear as the j-th child of A.
  for (auto &L : Labels)
    L.normalizePA(NumOfPatterns);

  // Initialize match set for placeholder *.
  const BitVector SetOfStar = BitVector(NumOfPatterns).set(0);
  MatchSets[SetOfStar] = 0;
  LLVM_DEBUG(dumpMS(MatchSets, "R", 0));

  // Add the match sets for height 0.
  for (auto &L : Labels) {
    if (L.isLeaf()) {
      if (Pattern *P = lookup(&L, ArrayRef<unsigned>())) {
        BitVector MS(SetOfStar);
        MS.set(P->Enc);
        MatchSets.insert(std::pair(MS, MatchSets.size()));
      }
    }
  }
  LLVM_DEBUG(dumpMS(MatchSets, "R", 1));

  // Calculate S_A_j_0.
  for (auto &L : Labels) {
    for (auto &MS : MatchSets) {
      L.updateSA(MS.first);
    }
    LLVM_DEBUG(for (unsigned I = 0, E = L.getNumUseOpnds(); I < E; ++I)
                   dumpMS(L.SA[I], Twine("S_A_j_").concat(Twine(I)).str(), 1));
  }

  unsigned H = 2;
  // Compute all match sets.
  for (bool Changes = true; Changes; ++H) {
    Changes = false;

    // Calculation next match set.
    for (auto &L : Labels) {
      assert(L.SA.size() == L.getNumUseOpnds() && "Size missmatch");
      for (auto PatternSet : EnumSet<SetOfSetOfPatterns, BitVector>(L.SA)) {
        BitVector MS(NumOfPatterns);
        for (auto P : EnumSet<BitVector, unsigned>(PatternSet)) {
          updateMatchSetWithPattern(MS, L, P);
        }
        if (MS.any())
          MatchSets.insert(std::pair(MS.set(0), MatchSets.size()));
      }
    }
    LLVM_DEBUG(dumpMS(MatchSets, "R", H));

    // Calculate S_A_j_i.
    for (auto &L : Labels) {
      for (auto &MS : MatchSets) {
        if (L.updateSA(MS.first))
          Changes = true;
      }
      LLVM_DEBUG(
          for (unsigned I = 0, E = L.getNumUseOpnds(); I < E; ++I)
              dumpMS(L.SA[I], Twine("S_A_j_").concat(Twine(I)).str(), H));
    }
  }
}

GIMatchTreeAutomaton *PatternForestBuilder::createAutomaton() {
  const BitVector SetOfStar = BitVector(NumOfPatterns).set(0);

  const unsigned DimMatchSets = MatchSets.size();
  GIMatchTreeAutomaton *Automaton = new GIMatchTreeAutomaton(DimMatchSets);
  for (auto &L : Labels) {
    // Handle leafs aka instructions with zero operands.
    if (L.isLeaf()) {
      // Look up encoding for match set { *, L }.
      BitVector MS(SetOfStar);
      updateMatchSetWithPattern(MS, L, ArrayRef<unsigned>());
      Automaton->LeafTables.emplace_back(L.Inst, MatchSets[MS]);
      continue;
    }

    // Handle all other patterns.
    auto &SA = L.SA;
    SmallVector<unsigned, 3> DimT;
    SmallVector<SmallVector<BitVector, 32>, 3>
        ChaseToHOD; // Mapping from the Chase set encoding to a HOD match set.
    GIMatchTreeAutomaton::Table T;
    T.Inst = L.Inst;
    T.DimC = L.getNumUseOpnds();

    // Initialize the compression tables.
    T.C = OwningArrayRef<unsigned>(T.DimC * DimMatchSets);
    for (unsigned I = 0, E = T.C.size(); I < E; ++I)
      T.C[I] = 0;

    // This loops performs several tasks:
    // (a) It calculates the size one each dimension of the lookup table.
    // (b) It calculates the size of the flat lookup table.
    // (c) It creates the mapping from a Chase set encoding to a HOD set.
    unsigned Size = 1;
    for (unsigned Op = 0; Op < T.DimC; ++Op) {
      // The assign encoding needs some small tweaking, because
      // the set containing the placeholder * must have 0 as encoding.
      bool ContainsSetOfStar;
      unsigned Swap;
      if (auto It = SA[Op].find(SetOfStar); It != SA[Op].end()) {
        ContainsSetOfStar = true;
        Swap = It->second;
      } else {
        ContainsSetOfStar = false;
        Swap = 0;
      }

      unsigned Sz = SA[Op].size() + !ContainsSetOfStar;
      SmallVector<BitVector, 32> M;
      M.resize_for_overwrite(Sz);
      if (!ContainsSetOfStar)
        M[0] = SetOfStar;
      auto &PAj = L.PA[Op];
      for (auto &[MS, HODSetEnc] : MatchSets) {
        BitVector B(MS);
        B &= PAj;
        auto It = SA[Op].find(B);
        if (It != SA[Op].end()) {
          unsigned ChaseSetEnc = It->second;
          if (ContainsSetOfStar) {
            if (ChaseSetEnc == Swap)
              ChaseSetEnc = 0;
            else if (ChaseSetEnc == 0)
              ChaseSetEnc = Swap;
          } else
            ++ChaseSetEnc;
          T.C[Op * DimMatchSets + HODSetEnc] = ChaseSetEnc;
          M[ChaseSetEnc] = MS;
        }
      }
      ChaseToHOD.push_back(std::move(M));

      // Calculate size of flat array and save size of this dimension.
      Size *= Sz;
      DimT.push_back(Sz);
    }

    // Initialize the lookup table.
    T.T = OwningArrayRef<unsigned>(Size);
    unsigned TOffset = 0; // Offset into T array.
    for (auto OpndsChase : EnumSet<unsigned, unsigned>(DimT)) {
      // OpndsChase[] is Chase set encoding.
      // Opnds[] is the Hoffmann/O'Donnel match set.
      SmallVector<BitVector, 3> Opnds;
      Opnds.resize_for_overwrite(T.DimC);
      for (unsigned I = 0; I < T.DimC; ++I)
        Opnds[I] = ChaseToHOD[I][OpndsChase[I]];

      BitVector MS(SetOfStar);
      for (auto P : EnumSet<BitVector, unsigned>(Opnds))
        updateMatchSetWithPattern(MS, L, P);
      auto It = MatchSets.find(MS);
      if (It != MatchSets.end())
        T.T[TOffset] = It->second;
      else
        T.T[TOffset] = 0;
      ++TOffset;
    }
    // Check for special case size equals 1. It means that the state transition
    // table contains exactly one element. This happens when the only use of a
    // non-leaf label has only * appearing as child patterns. E.g. G_AND [*, *].
    // We can treat this similar to a leaf.
    if (Size == 1) {
      Automaton->LeafTables.emplace_back(L.Inst, T.T[0]);
      continue;
    }
    T.DimT = OwningArrayRef<unsigned>(DimT);
    Automaton->Tables.push_back(std::move(T));
  }

  // Add the matching rules.
  for (auto &[MS, MSEnc] : MatchSets) {
    for (auto R : MatchingRules) {
      if (MS[R.first]) {
        Automaton->MatchingRules[MSEnc].append(R.second);
      }
    }
  }
  Automaton->MatchingRuleInfos = MatchingRuleInfos;

  return Automaton;
}

void PatternForestBuilder::dump() const { writeYAML(llvm::dbgs()); }

void PatternForestBuilder::writeYAML(raw_ostream &OS) const {
  auto WriteSet = [&OS](BitVector Set) {
    OS << "[ " << Set << (Set.any() ? " " : "") << "]";
  };
  auto WriteSetOfSets = [&OS, &WriteSet](SetOfSetOfPatterns Sets,
                                         unsigned Indent, bool EmitIdx) {
    SmallVector<BitVector, 0> Tmp;
    Tmp.resize_for_overwrite(Sets.size());
    for (auto &MS : Sets)
      Tmp[MS.second] = MS.first;
    for (auto [Index, MS] : enumerate(Tmp)) {
      OS.indent(Indent) << "- ";
      if (EmitIdx)
        OS << Index << ": ";
      WriteSet(MS);
      OS << "\n";
    }
  };

  // Sort the labels by name. Printing in sorted order helps with testing.
  // This can be removed when FileCheck supports CHECK-DAG-NEXT.
  std::vector<const Label *> SortedLabels;
  SortedLabels.reserve(Labels.size());
  for (const Label &L : Labels)
    SortedLabels.push_back(&L);
  std::sort(SortedLabels.begin(), SortedLabels.end(),
            [](const Label *L, const Label *R) {
                return L->Inst->TheDef->getName() < R->Inst->TheDef->getName();
            });

  OS << "PatternForest: # PF\n";
  for (const Pattern &P : Patterns) {
    P.writeYAML(OS, 2);
  }
  OS << "MatchSets: # R\n";
  WriteSetOfSets(MatchSets, 2, true);
  OS << "ChildPatternSets: # P_A\n";
  for (auto *L : SortedLabels) {
    OS.indent(2) << L->Inst->TheDef->getName() << ":\n";
    for (unsigned I = 0, E = L->getNumUseOpnds(); I < E; ++I) {
      OS.indent(4) << "- " << I << ": ";
      WriteSet(L->PA[I]);
      OS << "\n";
    }
  }
  OS << "RepresenterSets: # S_A\n";
  for (auto *L : SortedLabels) {
    OS.indent(2) << L->Inst->TheDef->getName() << ":\n";
    for (unsigned I = 0, E = L->getNumUseOpnds(); I < E; ++I) {
      OS.indent(4) << "- " << I << ": \n";
      WriteSetOfSets(L->SA[I], 6, false);
    }
  }
}

GIMatchTreeAutomaton::GIMatchTreeAutomaton(unsigned DimMatchSets)
    : DimMatchSets(DimMatchSets) {}

void GIMatchTreeAutomaton::emitTable(raw_ostream &OS, const Table &T,
                                     unsigned Indent) const {
  // Emit compression array.
  OS.indent(Indent) << "static unsigned C[" << T.DimC << "][" << DimMatchSets
                    << "] = ";
  emitMultiDimTable(OS, Indent, {T.DimC, DimMatchSets}, T.C, "{}");
  OS << ";\n\n";

  // Emit transition table.
  OS.indent(Indent) << "static unsigned T";
  for (unsigned I = 0, E = T.DimT.size(); I < E; ++I)
    OS << "[" << T.DimT[I] << "]";
  OS << " = ";
  emitMultiDimTable(OS, Indent, T.DimT, T.T, "{}");
  OS << ";\n\n";
}

void GIMatchTreeAutomaton::emitTransitions(raw_ostream &OS,
                                           unsigned Indent) const {
  // Avoid emitting an empty switch statement.
  if (LeafTables.empty() && Tables.empty())
    return;
  // Emit code to calculate the match set.
  OS.indent(Indent) << "switch (MI.getOpcode()) {\n";
  // First emit the leaf transitions.
  for (auto &[Inst, MS] : LeafTables) {
    OS.indent(Indent) << "case " << Inst->Namespace
                      << "::" << Inst->TheDef->getName() << ":\n";
    OS.indent(Indent + 2) << "MS = " << MS << ";\n";
    OS.indent(Indent + 2) << "break;\n";
  }
  // Then emit all other transitions.
  for (auto &T : Tables) {
    OS.indent(Indent) << "case " << T.Inst->Namespace
                      << "::" << T.Inst->TheDef->getName() << ": {\n";
    for (unsigned I = 0, E = T.DimT.size(); I < E; ++I) {
      unsigned OpNo = T.Inst->Operands.NumDefs + I;
      OS.indent(Indent + 2) << "unsigned Idx" << I << " = MI.getOperand("
                            << OpNo << ").isReg()\n";
      OS.indent(Indent + 2)
          << "                    ? MatchSets[MRI.getVRegDef(MI.getOperand("
          << OpNo << ").getReg())]\n";
      OS.indent(Indent + 2) << "                    : 0;\n";
    }
    OS << "\n";
    emitTable(OS, T, 4);
    OS.indent(Indent + 2) << "MS = T";
    for (unsigned I = 0, E = T.DimT.size(); I < E; ++I)
      OS << "[C[" << I << "][Idx" << I << "]]";
    OS << ";\n";
    OS.indent(Indent + 2) << "break;\n  }\n";
  }
  OS.indent(Indent) << "}\n";
}

void GIMatchTreeAutomaton::emitRuleMapping(raw_ostream &OS,
                                           unsigned Indent) const {
  OwningArrayRef<unsigned> MSToRule(DimMatchSets);
  for (auto &I : MSToRule)
    I = 0;
  SmallVector<SmallVector<unsigned, 0>, 0> Rules;
  unsigned SizeOfAllRules = 0;
  for (auto [Idx, MR] : enumerate(getMatchingRules())) {
    MSToRule[MR.first] = Idx + 1;
    SmallVector<unsigned, 0> RulesToExecute;
    BitVector Filter(getMatchingRuleInfos().size() + 1, true);
    for (auto PatternRuleID : MR.second) {
      if (Filter[PatternRuleID]) {
        RulesToExecute.push_back(PatternRuleID);
        Filter[PatternRuleID] = false;
      }
    }
    SizeOfAllRules += RulesToExecute.size();
    Rules.push_back(RulesToExecute);
  }
  // Do not output the tables in case there are no rules to execute.
  if (Rules.empty())
    return ;
  OS.indent(Indent) << "static const unsigned MSToRule[" << DimMatchSets
                    << "] = ";
  emitMultiDimTable(OS, Indent, {DimMatchSets}, MSToRule, "{}");
  OS << ";\n";
  OS.indent(Indent) << "static const unsigned AllRules[" << SizeOfAllRules
                    << "] = {\n";
  for (auto [Idx, R] : enumerate(Rules)) {
    OS.indent(Indent + 2) << "/* " << Idx << " */ ";
    for (unsigned Val : R)
      OS << Val << ", ";
    OS << "\n";
  }
  OS.indent(Indent) << "};\n";

  OS.indent(Indent) << "static const ArrayRef<unsigned> Rules["
                    << static_cast<unsigned>(Rules.size() + 1) << "] = {\n";
  OS.indent(Indent + 2) << "/* 0 */ ArrayRef<unsigned>(),\n";
  unsigned Ofs = 0;
  for (auto [Idx, R] : enumerate(Rules)) {
    OS.indent(Indent + 2) << "/* " << (Idx + 1)
                          << " */ ArrayRef<unsigned>(&AllRules[" << Ofs << "], "
                          << R.size() << "),\n";
    Ofs += R.size();
  }
  OS.indent(Indent) << "};\n";
}

void GIMatchTreeAutomaton::dump() const { writeYAML(llvm::dbgs(), true); }

void GIMatchTreeAutomaton::writeYAML(raw_ostream &OS, bool Compact) const {
  // Sort the tables using an index.
  SmallVector<unsigned, 0> IdxTables;
  IdxTables.resize_for_overwrite(Tables.size());
  for (unsigned I = 0, E = Tables.size(); I < E; ++I)
    IdxTables[I] = I;
  std::sort(IdxTables.begin(), IdxTables.end(),
            [&](const unsigned L, const unsigned R) {
              return Tables[L].Inst->TheDef->getName() <
                     Tables[R].Inst->TheDef->getName();
            });

  OS << "LeafTables:\n";
  for (auto &[Inst, MS] : LeafTables) {
    OS << "  " << Inst->TheDef->getName() << ": " << MS << "\n";
  }

  OS << "Tables:\n";
  if (Compact) {
    for (auto I : IdxTables) {
      auto &T = Tables[I];
      OS << "  " << T.Inst->TheDef->getName() << ":\n";
      OS << "    C: ";
      emitMultiDimTable(OS, 8, {T.DimC, DimMatchSets}, T.C, "[]");
      OS << "\n    T: ";
      emitMultiDimTable(OS, 8, T.DimT, T.T, "[]");
      OS << "\n";
    }
  } else {
    for (auto I : IdxTables) {
      auto &T = Tables[I];
      OS << "  " << T.Inst->TheDef->getName() << ":\n";
      OS << "    C:\n";
      for (unsigned I = 0; I < T.DimC; ++I) {
        for (unsigned J = 0; J < DimMatchSets; ++J) {
          OS << "      - [ " << I << ", " << J << ", "
             << T.C[I * DimMatchSets + J] << " ]\n";
        }
      }
      OS << "    T:\n";
      unsigned TOffset = 0; // Offset into T array.
      for (auto Elem : EnumSet<unsigned, unsigned>(T.DimT)) {
        OS << "      - [ ";
        for (unsigned I = 0, E = T.DimT.size(); I < E; ++I) {
          if (I)
            OS << ", ";
          OS << Elem[I];
        }
        OS << ", " << T.T[TOffset] << " ]\n";
        ++TOffset;
      }
    }
  }
}

GIMatchTreeAutomatonBuilder::GIMatchTreeAutomatonBuilder(RecordKeeper &Records)
    : Target(Records) {
  PFBuilder = std::make_unique<PatternForestBuilder>();
}

void GIMatchTreeAutomatonBuilder::addLeaf(StringRef Name, uint64_t ID,
                                          unsigned RootIdx,
                                          const GIMatchDag &MatchDag,
                                          void *Data) {
  PFBuilder->addPattern(Name, RootIdx, MatchDag, Data);
}

GIMatchTreeAutomatonBuilder::~GIMatchTreeAutomatonBuilder() = default;

std::unique_ptr<GIMatchTreeAutomaton> GIMatchTreeAutomatonBuilder::run() {
  PFBuilder->createMatchSets();
  return std::unique_ptr<GIMatchTreeAutomaton>(PFBuilder->createAutomaton());
}

void GIMatchTreeAutomatonBuilder::dump() const { writeYAML(llvm::dbgs()); }

void GIMatchTreeAutomatonBuilder::writeYAML(raw_ostream &OS) const {
  PFBuilder->writeYAML(OS);
}
} // namespace llvm
