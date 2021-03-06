//===-- M88kRegisterBankInfo.cpp -------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// This file implements the targeting of the RegisterBankInfo class for M88k.
/// \todo This should be generated by TableGen.
//===----------------------------------------------------------------------===//

#include "M88kRegisterBankInfo.h"
#include "M88kInstrInfo.h"
#include "MCTargetDesc/M88kMCTargetDesc.h"
#include "llvm/CodeGen/GlobalISel/LegalizationArtifactCombiner.h"
#include "llvm/CodeGen/GlobalISel/LegalizerHelper.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegisterBank.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"

#define GET_TARGET_REGBANK_IMPL
#include "M88kGenRegisterBank.inc"

// This file will be TableGen'ed at some point.
#include "M88kGenRegisterBankInfo.def"

using namespace llvm;

M88kRegisterBankInfo::M88kRegisterBankInfo(const TargetRegisterInfo &TRI)
    : M88kGenRegisterBankInfo() {}

const RegisterBank &
M88kRegisterBankInfo::getRegBankFromRegClass(const TargetRegisterClass &RC,
                                             LLT Ty) const {
  switch (RC.getID()) {
  case M88k::GPRRCRegClassID:
  case M88k::GPR64RCRegClassID:
    return getRegBank(M88k::GRRegBankID);
  case M88k::XRRCRegClassID:
    return getRegBank(M88k::XRRegBankID);
  default:
    llvm_unreachable("Unexpected register class");
  }
}

/// Returns whether opcode \p Opc is a pre-isel generic floating-point opcode,
/// having only floating-point operands.
static bool isPreISelGenericFloatingPointOpcode(unsigned Opc) {
  switch (Opc) {
  case TargetOpcode::G_FADD:
  case TargetOpcode::G_FSUB:
  case TargetOpcode::G_FMUL:
  case TargetOpcode::G_FMA:
  case TargetOpcode::G_FDIV:
  case TargetOpcode::G_FCONSTANT:
  case TargetOpcode::G_FPEXT:
  case TargetOpcode::G_FPTRUNC:
  case TargetOpcode::G_FCEIL:
  case TargetOpcode::G_FFLOOR:
  case TargetOpcode::G_FNEARBYINT:
  case TargetOpcode::G_FNEG:
  case TargetOpcode::G_FCOS:
  case TargetOpcode::G_FSIN:
  case TargetOpcode::G_FLOG10:
  case TargetOpcode::G_FLOG:
  case TargetOpcode::G_FLOG2:
  case TargetOpcode::G_FSQRT:
  case TargetOpcode::G_FABS:
  case TargetOpcode::G_FEXP:
  case TargetOpcode::G_FRINT:
  case TargetOpcode::G_INTRINSIC_TRUNC:
  case TargetOpcode::G_INTRINSIC_ROUND:
    return true;
  }
  return false;
}

const RegisterBankInfo::ValueMapping *
M88kRegisterBankInfo::getFPOperandsMapping(const MachineInstr &MI) const {
  const unsigned Opc = MI.getOpcode();
  const MachineFunction &MF = *MI.getParent()->getParent();
  const MachineRegisterInfo &MRI = MF.getRegInfo();

  const unsigned NumOperands = MI.getNumOperands();
  assert(NumOperands <= 3 &&
         "This code is for instructions with 3 or less operands");
  assert(isPreISelGenericFloatingPointOpcode(Opc) &&
         "No floating point istruction");

  bool RequiresXPR = false;
  for (unsigned I = 0; I < NumOperands; ++I)
    if (MRI.getType(MI.getOperand(0).getReg()).getScalarSizeInBits() == 80)
      RequiresXPR = true;

  //const RegisterBankInfo::ValueMapping *ValMap[3];
  SmallVector<const RegisterBankInfo::ValueMapping *, 3> ValMap;
  for (unsigned I = 0; I < NumOperands; ++I) {
  PartialMappingIdx RBIdx = PMI_None;
  LLT Ty = MRI.getType(MI.getOperand(I).getReg());
    switch (Ty.getSizeInBits()) {
    case 32:
      RBIdx = RequiresXPR ? PMI_XR32 : PMI_GR32;
      break;
    case 64:
      RBIdx = RequiresXPR ? PMI_XR64 : PMI_GR64;
      break;
    case 80:
      RBIdx = PMI_XR80;
      break;
    default:
      llvm_unreachable("Unsupport register size");
    }
    //ValMap[I] = getValueMapping(RBIdx);
    ValMap.push_back(getValueMapping(RBIdx));
  }

  //return getOperandsMapping(&ValMap[0], &ValMap[NumOperands-1]);
  return getOperandsMapping(ValMap);
}

const RegisterBankInfo::InstructionMapping &
M88kRegisterBankInfo::getInstrMapping(const MachineInstr &MI) const {
  const unsigned Opc = MI.getOpcode();

  // Try the default logic for non-generic instructions that are either copies
  // or already have some operands assigned to banks.
  if ((Opc != TargetOpcode::COPY && !isPreISelGenericOpcode(Opc)) ||
      Opc == TargetOpcode::G_PHI) {
    const RegisterBankInfo::InstructionMapping &Mapping =
        getInstrMappingImpl(MI);
    if (Mapping.isValid())
      return Mapping;
  }

  const MachineFunction &MF = *MI.getParent()->getParent();
  const MachineRegisterInfo &MRI = MF.getRegInfo();
  const TargetSubtargetInfo &STI = MF.getSubtarget();
  const TargetRegisterInfo &TRI = *STI.getRegisterInfo();

  unsigned NumOperands = MI.getNumOperands();
  const ValueMapping *OperandsMapping = nullptr;
  unsigned MappingID = DefaultMappingID;

  switch (Opc) {
    // Arithmetic ops.
  case TargetOpcode::G_ADD:
  case TargetOpcode::G_SUB:
  case TargetOpcode::G_PTR_ADD:
  case TargetOpcode::G_MUL:
  case TargetOpcode::G_SDIV:
  case TargetOpcode::G_UDIV:
    // Bitwise ops.
  case TargetOpcode::G_AND:
  case TargetOpcode::G_OR:
  case TargetOpcode::G_XOR:
    // Shift ops.
  case TargetOpcode::G_SHL:
  case TargetOpcode::G_ASHR:
  case TargetOpcode::G_LSHR:
    OperandsMapping = getValueMapping(PMI_GR32);
    break;
    // Floating point ops.
  case TargetOpcode::G_FADD:
  case TargetOpcode::G_FSUB:
  case TargetOpcode::G_FMUL:
  case TargetOpcode::G_FDIV:
    OperandsMapping = getFPOperandsMapping(MI);
    break;
  case TargetOpcode::G_FCONSTANT: {
    LLT Ty = MRI.getType(MI.getOperand(0).getReg());
    if (Ty.getSizeInBits() != 64 && Ty.getSizeInBits() != 32)
      return getInvalidInstructionMapping(); // TODO Support 80 bit FP.
    PartialMappingIdx RBIdx = (Ty.getSizeInBits() == 64) ? PMI_GR64 : PMI_GR32;
    OperandsMapping = getOperandsMapping(
        {getValueMapping(RBIdx), nullptr});
    break;
  }
  case TargetOpcode::G_FPEXT:
    OperandsMapping = getOperandsMapping(
        {getValueMapping(PMI_GR64), getValueMapping(PMI_GR32)});
    break;
  case TargetOpcode::G_FPTRUNC:
    OperandsMapping = getOperandsMapping(
        {getValueMapping(PMI_GR32), getValueMapping(PMI_GR64)});
    break;
  case TargetOpcode::G_FPTOSI:
  case TargetOpcode::G_FPTOUI: {
    LLT Ty = MRI.getType(MI.getOperand(1).getReg());
    if (Ty.getSizeInBits() != 64 && Ty.getSizeInBits() != 32)
      return getInvalidInstructionMapping(); // TODO Support 80 bit FP.
    PartialMappingIdx RBIdx = (Ty.getSizeInBits() == 64) ? PMI_GR64 : PMI_GR32;
    OperandsMapping = getOperandsMapping(
        {getValueMapping(PMI_GR32), getValueMapping(RBIdx)});
    break;
  }
  case TargetOpcode::G_SITOFP:
  case TargetOpcode::G_UITOFP: {
    LLT Ty = MRI.getType(MI.getOperand(0).getReg());
    if (Ty.getSizeInBits() != 64 && Ty.getSizeInBits() != 32)
      return getInvalidInstructionMapping(); // TODO Support 80 bit FP.
    PartialMappingIdx RBIdx = (Ty.getSizeInBits() == 64) ? PMI_GR64 : PMI_GR32;
    OperandsMapping = getOperandsMapping(
        {getValueMapping(RBIdx), getValueMapping(PMI_GR32)});
    break;
  }
  case TargetOpcode::G_UBFX:
  case TargetOpcode::G_SBFX:
    OperandsMapping = getOperandsMapping(
        {getValueMapping(PMI_GR32), getValueMapping(PMI_GR32),
         getValueMapping(PMI_GR32), getValueMapping(PMI_GR32)});
    break;
  case TargetOpcode::G_ROTR:
    OperandsMapping = getOperandsMapping({getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32)});
    break;
  case TargetOpcode::G_TRUNC:
    OperandsMapping = getValueMapping(PMI_GR32);
    break;
  case TargetOpcode::G_SEXT:
  case TargetOpcode::G_ZEXT:
  case TargetOpcode::G_ANYEXT:
    OperandsMapping = getValueMapping(PMI_GR32);
    break;
  case TargetOpcode::G_SEXT_INREG:
    OperandsMapping = getOperandsMapping(
        {getValueMapping(PMI_GR32), getValueMapping(PMI_GR32), nullptr});
    break;
  case TargetOpcode::G_SEXTLOAD:
  case TargetOpcode::G_ZEXTLOAD:
  case TargetOpcode::G_LOAD:
  case TargetOpcode::G_STORE:
    if (MRI.getType(MI.getOperand(0).getReg()).getSizeInBits() == 64)
      OperandsMapping = getOperandsMapping(
          {getValueMapping(PMI_GR64), getValueMapping(PMI_GR32)});
    else
      OperandsMapping = getValueMapping(PMI_GR32);
    break;
  case TargetOpcode::G_FRAME_INDEX:
  case TargetOpcode::G_GLOBAL_VALUE:
  case TargetOpcode::G_JUMP_TABLE:
  case TargetOpcode::G_CONSTANT:
  case TargetOpcode::G_BRCOND:
    OperandsMapping = getOperandsMapping({getValueMapping(PMI_GR32), nullptr});
    break;
  case TargetOpcode::G_BR:
    OperandsMapping = getOperandsMapping({nullptr});
    break;
  case TargetOpcode::G_BRINDIRECT:
    OperandsMapping = getValueMapping(PMI_GR32);
    break;
  case TargetOpcode::G_BRJT:
    OperandsMapping = getOperandsMapping(
        {getValueMapping(PMI_GR32), nullptr, getValueMapping(PMI_GR32)});
    break;
  case TargetOpcode::G_ICMP:
    OperandsMapping = getOperandsMapping({getValueMapping(PMI_GR32), nullptr,
                                          getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32)});
    break;
  case TargetOpcode::G_SELECT:
    // TODO FP not handled.
    OperandsMapping = getOperandsMapping({getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32)});
    break;
  case TargetOpcode::G_MERGE_VALUES: {
    // We only support G_MERGE_VALUES for creating a 64 bit value out of two
    // GPRs.
    LLT Ty = MRI.getType(MI.getOperand(0).getReg());
    LLT Ty1 = MRI.getType(MI.getOperand(1).getReg());
    LLT Ty2 = MRI.getType(MI.getOperand(2).getReg());
    if (Ty.getSizeInBits() != 64 || Ty1.getSizeInBits() != 32 ||
        Ty2.getSizeInBits() != 32)
      return getInvalidInstructionMapping();
    OperandsMapping = getOperandsMapping({getValueMapping(PMI_GR64),
                                          getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32)});
    break;
  }
  case TargetOpcode::G_UNMERGE_VALUES: {
    // We only support G_UNMERGE_VALUES for splitting a 64 bit value into two
    // GPRs.
    LLT Ty = MRI.getType(MI.getOperand(0).getReg());
    LLT Ty1 = MRI.getType(MI.getOperand(1).getReg());
    LLT Ty2 = MRI.getType(MI.getOperand(2).getReg());
    if (Ty.getSizeInBits() != 32 || Ty1.getSizeInBits() != 32 ||
        Ty2.getSizeInBits() != 64)
      return getInvalidInstructionMapping();
    OperandsMapping = getOperandsMapping({getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR32),
                                          getValueMapping(PMI_GR64)});
    break;
  }
  case TargetOpcode::COPY: {
    Register DstReg = MI.getOperand(0).getReg();
    Register SrcReg = MI.getOperand(1).getReg();
    // Check if one of the register is not a generic register.
    if ((Register::isPhysicalRegister(DstReg) ||
         !MRI.getType(DstReg).isValid()) ||
        (Register::isPhysicalRegister(SrcReg) ||
         !MRI.getType(SrcReg).isValid())) {
      const RegisterBank *DstRB = getRegBank(DstReg, MRI, TRI);
      const RegisterBank *SrcRB = getRegBank(SrcReg, MRI, TRI);
      if (!DstRB)
        DstRB = SrcRB;
      else if (!SrcRB)
        SrcRB = DstRB;
      // If both RB are null that means both registers are generic.
      // We shouldn't be here.
      assert(DstRB && SrcRB && "Both RegBank were nullptr");
      unsigned Size = getSizeInBits(DstReg, MRI, TRI);
      return getInstructionMapping(
          DefaultMappingID, copyCost(*DstRB, *SrcRB, Size),
          getCopyMapping(DstRB->getID(), SrcRB->getID(), Size),
          // We only care about the mapping of the destination.
          /*NumOperands*/ 1);
    }
    // Both registers are generic, use G_BITCAST.
    LLVM_FALLTHROUGH;
  }
  case TargetOpcode::G_BITCAST: {
    LLT DstTy = MRI.getType(MI.getOperand(0).getReg());
    LLT SrcTy = MRI.getType(MI.getOperand(1).getReg());
    unsigned Size = DstTy.getSizeInBits();
    bool DstIsGPR = !DstTy.isVector() && DstTy.getSizeInBits() <= 64;
    bool SrcIsGPR = !SrcTy.isVector() && SrcTy.getSizeInBits() <= 64;
    const RegisterBank &DstRB = DstIsGPR ? M88k::GRRegBank : M88k::XRRegBank;
    const RegisterBank &SrcRB = SrcIsGPR ? M88k::GRRegBank : M88k::XRRegBank;
    return getInstructionMapping(
        DefaultMappingID, copyCost(DstRB, SrcRB, Size),
        getCopyMapping(DstRB.getID(), SrcRB.getID(), Size),
        // We only care about the mapping of the destination for COPY.
        /*NumOperands*/ Opc == TargetOpcode::G_BITCAST ? 2 : 1);
  }
  default:
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
    MI.dump();
#endif
    return getInvalidInstructionMapping();
  }

  return getInstructionMapping(MappingID, /*Cost=*/1, OperandsMapping,
                               NumOperands);
}

RegisterBankInfo::InstructionMappings
M88kRegisterBankInfo::getInstrAlternativeMappings(
    const MachineInstr &MI) const {
  const unsigned Opc = MI.getOpcode();
  switch (Opc) {
  case TargetOpcode::G_FADD:
  case TargetOpcode::G_FSUB:
  case TargetOpcode::G_FMUL:
  case TargetOpcode::G_FDIV: {
    unsigned NumOperands = MI.getNumOperands();
    assert(NumOperands <= 3 &&
           "This code is for instructions with 3 or less operands");
    InstructionMappings AltMappings;
    AltMappings.push_back(&getInstructionMapping(
        /*ID*/ 1, /*Cost*/ 1, getValueMapping(PMI_XR32), NumOperands));
    AltMappings.push_back(&getInstructionMapping(
        /*ID*/ 2, /*Cost*/ 1, getValueMapping(PMI_XR80), NumOperands));
    return AltMappings;
  }
  default:
    break;
  }
  return RegisterBankInfo::getInstrAlternativeMappings(MI);
}

void M88kRegisterBankInfo::applyMappingImpl(
    const OperandsMapper &OpdMapper) const {
  return applyDefaultMapping(OpdMapper);
}
