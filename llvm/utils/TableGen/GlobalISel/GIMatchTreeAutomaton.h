//===- GIMatchTree.h - A decision tree to match GIMatchDag's --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The general approach is to generate a bottom-up tree matcher as described by
/// Chase.
///
/// References:
/// Hoffmann, O'Donnel: Pattern Matching in Trees (1982)
/// https://dl.acm.org/doi/10.1145/322290.322295
///
/// Chase: An Improvement to Bottom-up Tree Pattern Matching (1987)
/// https://dl.acm.org/doi/10.1145/41625.41640
//===----------------------------------------------------------------------===//

#ifndef LLVM_UTILS_TABLEGEN_GIMATCHTREEAUTOMATON_H
#define LLVM_UTILS_TABLEGEN_GIMATCHTREEAUTOMATON_H

#include "GIMatchDag.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

#include "../CodeGenTarget.h" // For enumerating instructions.

namespace llvm {
class raw_ostream;
class CodeGenInstruction;
class PatternForestBuilder;

/// Describes the binding of a variable to the matched MIR.
class GIMatchPatternVariableBinding {
  /// The name of the variable described by this binding.
  StringRef Name;
  // The matched instruction it is bound to.
  unsigned InstrID;
  // The matched operand (if appropriate) it is bound to.
  std::optional<unsigned> OpIdx;

public:
  GIMatchPatternVariableBinding(StringRef Name, unsigned InstrID,
                                std::optional<unsigned> OpIdx = std::nullopt)
      : Name(Name), InstrID(InstrID), OpIdx(OpIdx) {}

  bool isInstr() const { return !OpIdx; }
  StringRef getName() const { return Name; }
  unsigned getInstrID() const { return InstrID; }
  unsigned getOpIdx() const {
    assert(OpIdx && "Is not an operand binding");
    return *OpIdx;
  }
};

class GIMatchPatternInstrInfo {
  // The ID of the instruction which this instruction refers too.
  unsigned BaseInstrID;
  // The defining operand.
  unsigned FromOpIdx;

public:
  GIMatchPatternInstrInfo(unsigned BaseInstrID, unsigned FromOpIdx)
      : BaseInstrID(BaseInstrID), FromOpIdx(FromOpIdx) {}
  unsigned getBaseInstrID() const { return BaseInstrID; }
  unsigned getFromOpIdx() const { return FromOpIdx; }
};

class GIMatchPatternInfo {
public:
  using const_instr_infos_iterator =
      SmallVector<GIMatchPatternInstrInfo, 0>::const_iterator;
  using const_var_binding_iterator =
      SmallVector<GIMatchPatternVariableBinding, 0>::const_iterator;

private:
  /// A name for the pattern. This is primarily for debugging.
  StringRef Name;
  /// Opaque data the caller of the tree building code understands.
  void *Data;

  // List of the instructions used in the pattern.
  // The elements of this list form a tree, with the first element being the
  // root.
  SmallVector<GIMatchPatternInstrInfo, 0> InstrInfos;

  // The variable bindings associated with this pattern.
  SmallVector<GIMatchPatternVariableBinding, 0> VarBindings;

  // Is this info a variant of another info?
  bool IsVariant;

  // List of variants.
  SmallVector<unsigned, 8> Variants;

public:
  GIMatchPatternInfo(StringRef Name, void *Data, bool IsVariant = false)
      : Name(Name), Data(Data), IsVariant(IsVariant) {}

  StringRef getName() const { return Name; }

  template <class Ty> Ty *getTargetData() const {
    return static_cast<Ty *>(Data);
  }

  unsigned add(const GIMatchDagInstr *Instr, unsigned BaseInstrID,
               unsigned FromOpIdx) {
    unsigned ID = addInstrInfo(BaseInstrID, FromOpIdx);

    if (Instr) {
      if (!Instr->getUserAssignedName().empty())
        bindInstrVariable(Instr->getUserAssignedName(), ID);
      for (const auto &VarBinding : Instr->user_assigned_operand_names())
        bindOperandVariable(VarBinding.second, ID, VarBinding.first);
    }

    return ID;
  };

  unsigned addInstrInfo(unsigned BaseInstrID, unsigned FromOpIdx) {
    unsigned ID = InstrInfos.size();
    InstrInfos.emplace_back(BaseInstrID, FromOpIdx);
    return ID;
  }
  size_t getNumInstrInfo() const { return InstrInfos.size(); }
  const_instr_infos_iterator instr_infos_begin() const {
    return InstrInfos.begin();
  }
  const_instr_infos_iterator instr_infos_end() const {
    return InstrInfos.end();
  }
  iterator_range<const_instr_infos_iterator> instr_infos() const {
    return make_range(InstrInfos.begin(), InstrInfos.end());
  }

  void bindInstrVariable(StringRef Name, unsigned InstrID) {
    VarBindings.emplace_back(Name, InstrID);
  }
  void bindOperandVariable(StringRef Name, unsigned InstrID, unsigned OpIdx) {
    VarBindings.emplace_back(Name, InstrID, OpIdx);
  }
  const_var_binding_iterator var_bindings_begin() const {
    return VarBindings.begin();
  }
  const_var_binding_iterator var_bindings_end() const {
    return VarBindings.end();
  }
  iterator_range<const_var_binding_iterator> var_bindings() const {
    return make_range(VarBindings.begin(), VarBindings.end());
  }

  bool isVariant() const { return IsVariant; }
  bool hasVariants() const { return !Variants.empty(); }
  void addVariant(unsigned VariantID) {
    Variants.push_back(VariantID);
  }
  const SmallVectorImpl<unsigned> &getVariants() const { return Variants; }
};

class GIMatchTreeAutomaton {
  friend class PatternForestBuilder;

public:
  struct Table {
    // The label.
    const CodeGenInstruction *Inst;
    // Dimension of the compression table.
    unsigned DimC;
    // The compression table. Dimension is DimC X DimMatchSets.
    OwningArrayRef<unsigned> C;
    // Dimension and data of the transition table.
    OwningArrayRef<unsigned> DimT;
    OwningArrayRef<unsigned> T;
  };

private:
  // Number of match sets. This determines the dimension of the C array.
  unsigned DimMatchSets;

  // The compression and transistion tables.
  SmallVector<Table, 0> Tables;

  // LeafTables.
  SmallVector<std::pair<const CodeGenInstruction *, unsigned>, 0> LeafTables;

  // The matching rules.
  DenseMap<unsigned, SmallVector<unsigned, 0>> MatchingRules;
  SmallVector<GIMatchPatternInfo, 0> MatchingRuleInfos;

  void emitTable(raw_ostream &OS, const Table &T, unsigned Indent) const;

public:
  GIMatchTreeAutomaton(unsigned DimMatchSets);
  const DenseMap<unsigned, SmallVector<unsigned, 0>> &getMatchingRules() const {
    return MatchingRules;
  }
  const SmallVector<GIMatchPatternInfo, 0> &getMatchingRuleInfos() const {
    return MatchingRuleInfos;
  }
  void emitTransitions(raw_ostream &OS, unsigned Indent) const;
  void emitRuleMapping(raw_ostream &OS, unsigned Indent) const;
  void writeYAML(raw_ostream &OS, bool Compact = false) const;
  void dump() const;
};

class GIMatchTreeAutomatonBuilder {
  /// For information about target instructions.
  const CodeGenTarget Target;

  std::unique_ptr<PatternForestBuilder> PFBuilder;

public:
  GIMatchTreeAutomatonBuilder(RecordKeeper &Records);
  ~GIMatchTreeAutomatonBuilder();

  void addLeaf(StringRef Name, uint64_t ID, unsigned RootIdx,
               const GIMatchDag &MatchDag, void *Data);

  /// Construct the bottom up tree matcher.
  std::unique_ptr<GIMatchTreeAutomaton> run();

  void writeYAML(raw_ostream &OS) const;
  void dump() const;
};

} // end namespace llvm
#endif // ifndef LLVM_UTILS_TABLEGEN_GIMATCHTREEAUTOMATON_H
