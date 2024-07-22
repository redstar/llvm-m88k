/*===- TableGen'erated file -------------------------------------*- C++ -*-===*\
|*                                                                            *|
|* Register Bank Source Fragments                                             *|
|*                                                                            *|
|* Automatically generated file, do not edit!                                 *|
|*                                                                            *|
\*===----------------------------------------------------------------------===*/

#ifdef GET_REGBANK_DECLARATIONS
#undef GET_REGBANK_DECLARATIONS
namespace llvm {
namespace PPC {
enum : unsigned {
  InvalidRegBankID = ~0u,
  CRRegBankID = 0,
  FPRRegBankID = 1,
  GPRRegBankID = 2,
  VECRegBankID = 3,
  NumRegisterBanks,
};
} // end namespace PPC
} // end namespace llvm
#endif // GET_REGBANK_DECLARATIONS

#ifdef GET_TARGET_REGBANK_CLASS
#undef GET_TARGET_REGBANK_CLASS
private:
  static const RegisterBank *RegBanks[];
  static const unsigned Sizes[];

public:
  const RegisterBank &getRegBankFromRegClass(const TargetRegisterClass &RC, LLT Ty) const override;
protected:
  PPCGenRegisterBankInfo(unsigned HwMode = 0);

#endif // GET_TARGET_REGBANK_CLASS

#ifdef GET_TARGET_REGBANK_IMPL
#undef GET_TARGET_REGBANK_IMPL
namespace llvm {
namespace PPC {
const uint32_t CRRegBankCoverageData[] = {
    // 0-31
    (1u << (PPC::CRRCRegClassID - 0)) |
    (1u << (PPC::CRBITRCRegClassID - 0)) |
    0,
    // 32-63
    0,
};
const uint32_t FPRRegBankCoverageData[] = {
    // 0-31
    (1u << (PPC::VSSRCRegClassID - 0)) |
    (1u << (PPC::F4RCRegClassID - 0)) |
    (1u << (PPC::F8RCRegClassID - 0)) |
    (1u << (PPC::SPILLTOVSRRC_and_F4RCRegClassID - 0)) |
    (1u << (PPC::VSFRCRegClassID - 0)) |
    (1u << (PPC::SPILLTOVSRRC_and_VSFRCRegClassID - 0)) |
    (1u << (PPC::SPILLTOVSRRC_and_VFRCRegClassID - 0)) |
    (1u << (PPC::VFRCRegClassID - 0)) |
    0,
    // 32-63
    0,
};
const uint32_t GPRRegBankCoverageData[] = {
    // 0-31
    (1u << (PPC::G8RCRegClassID - 0)) |
    (1u << (PPC::GPRCRegClassID - 0)) |
    (1u << (PPC::G8RC_and_G8RC_NOX0RegClassID - 0)) |
    (1u << (PPC::GPRC_NOR0RegClassID - 0)) |
    (1u << (PPC::GPRC_and_GPRC_NOR0RegClassID - 0)) |
    (1u << (PPC::G8RC_NOX0RegClassID - 0)) |
    0,
    // 32-63
    0,
};
const uint32_t VECRegBankCoverageData[] = {
    // 0-31
    (1u << (PPC::VSRCRegClassID - 0)) |
    (1u << (PPC::VSSRCRegClassID - 0)) |
    (1u << (PPC::VSFRCRegClassID - 0)) |
    (1u << (PPC::VSRC_with_sub_64_in_SPILLTOVSRRCRegClassID - 0)) |
    (1u << (PPC::SPILLTOVSRRCRegClassID - 0)) |
    (1u << (PPC::SPILLTOVSRRC_and_VSFRCRegClassID - 0)) |
    (1u << (PPC::VRRC_with_sub_64_in_SPILLTOVSRRCRegClassID - 0)) |
    (1u << (PPC::VFRCRegClassID - 0)) |
    (1u << (PPC::SPILLTOVSRRC_and_VFRCRegClassID - 0)) |
    (1u << (PPC::F4RCRegClassID - 0)) |
    (1u << (PPC::F8RCRegClassID - 0)) |
    (1u << (PPC::SPILLTOVSRRC_and_F4RCRegClassID - 0)) |
    (1u << (PPC::VRRCRegClassID - 0)) |
    (1u << (PPC::VSLRCRegClassID - 0)) |
    0,
    // 32-63
    (1u << (PPC::VSLRC_with_sub_64_in_SPILLTOVSRRCRegClassID - 32)) |
    0,
};

constexpr RegisterBank CRRegBank(/* ID */ PPC::CRRegBankID, /* Name */ "CR", /* CoveredRegClasses */ CRRegBankCoverageData, /* NumRegClasses */ 54);
constexpr RegisterBank FPRRegBank(/* ID */ PPC::FPRRegBankID, /* Name */ "FPR", /* CoveredRegClasses */ FPRRegBankCoverageData, /* NumRegClasses */ 54);
constexpr RegisterBank GPRRegBank(/* ID */ PPC::GPRRegBankID, /* Name */ "GPR", /* CoveredRegClasses */ GPRRegBankCoverageData, /* NumRegClasses */ 54);
constexpr RegisterBank VECRegBank(/* ID */ PPC::VECRegBankID, /* Name */ "VEC", /* CoveredRegClasses */ VECRegBankCoverageData, /* NumRegClasses */ 54);
} // end namespace PPC

const RegisterBank *PPCGenRegisterBankInfo::RegBanks[] = {
    &PPC::CRRegBank,
    &PPC::FPRRegBank,
    &PPC::GPRRegBank,
    &PPC::VECRegBank,
};

const unsigned PPCGenRegisterBankInfo::Sizes[] = {
    // Mode = 0 (Default)
    32,
    64,
    64,
    128,
};

PPCGenRegisterBankInfo::PPCGenRegisterBankInfo(unsigned HwMode)
    : RegisterBankInfo(RegBanks, PPC::NumRegisterBanks, Sizes, HwMode) {
  // Assert that RegBank indices match their ID's
#ifndef NDEBUG
  for (auto RB : enumerate(RegBanks))
    assert(RB.index() == RB.value()->getID() && "Index != ID");
#endif // NDEBUG
}
const RegisterBank &
PPCGenRegisterBankInfo::getRegBankFromRegClass(const TargetRegisterClass &RC, LLT) const {
  constexpr uint32_t InvalidRegBankID = uint32_t(PPC::InvalidRegBankID) & 15;
  static const uint32_t RegClass2RegBank[5] = {
    (uint32_t(InvalidRegBankID) << 0) | // VSSRCRegClassID
    (uint32_t(PPC::GPRRegBankID) << 4) | // GPRCRegClassID
    (uint32_t(PPC::GPRRegBankID) << 8) | // GPRC_NOR0RegClassID
    (uint32_t(PPC::GPRRegBankID) << 12) | // GPRC_and_GPRC_NOR0RegClassID
    (uint32_t(PPC::CRRegBankID) << 16) | // CRBITRCRegClassID
    (uint32_t(InvalidRegBankID) << 20) | // F4RCRegClassID
    (uint32_t(InvalidRegBankID) << 24) |
    (uint32_t(PPC::CRRegBankID) << 28), // CRRCRegClassID
    (uint32_t(InvalidRegBankID) << 0) |
    (uint32_t(InvalidRegBankID) << 4) |
    (uint32_t(InvalidRegBankID) << 8) |
    (uint32_t(InvalidRegBankID) << 12) |
    (uint32_t(PPC::VECRegBankID) << 16) | // SPILLTOVSRRCRegClassID
    (uint32_t(InvalidRegBankID) << 20) | // VSFRCRegClassID
    (uint32_t(PPC::GPRRegBankID) << 24) | // G8RCRegClassID
    (uint32_t(PPC::GPRRegBankID) << 28), // G8RC_NOX0RegClassID
    (uint32_t(InvalidRegBankID) << 0) | // SPILLTOVSRRC_and_VSFRCRegClassID
    (uint32_t(PPC::GPRRegBankID) << 4) | // G8RC_and_G8RC_NOX0RegClassID
    (uint32_t(InvalidRegBankID) << 8) | // F8RCRegClassID
    (uint32_t(InvalidRegBankID) << 12) |
    (uint32_t(InvalidRegBankID) << 16) | // VFRCRegClassID
    (uint32_t(InvalidRegBankID) << 20) |
    (uint32_t(InvalidRegBankID) << 24) | // SPILLTOVSRRC_and_VFRCRegClassID
    (uint32_t(InvalidRegBankID) << 28), // SPILLTOVSRRC_and_F4RCRegClassID
    (uint32_t(InvalidRegBankID) << 0) |
    (uint32_t(InvalidRegBankID) << 4) |
    (uint32_t(InvalidRegBankID) << 8) |
    (uint32_t(PPC::VECRegBankID) << 12) | // VSRCRegClassID
    (uint32_t(PPC::VECRegBankID) << 16) | // VSRC_with_sub_64_in_SPILLTOVSRRCRegClassID
    (uint32_t(PPC::VECRegBankID) << 20) | // VRRCRegClassID
    (uint32_t(PPC::VECRegBankID) << 24) | // VSLRCRegClassID
    (uint32_t(PPC::VECRegBankID) << 28), // VRRC_with_sub_64_in_SPILLTOVSRRCRegClassID
    (uint32_t(InvalidRegBankID) << 0) |
    (uint32_t(InvalidRegBankID) << 4) |
    (uint32_t(InvalidRegBankID) << 8) |
    (uint32_t(PPC::VECRegBankID) << 12) // VSLRC_with_sub_64_in_SPILLTOVSRRCRegClassID
  };
  const unsigned RegClassID = RC.getID();
  if (LLVM_LIKELY(RegClassID < 36)) {
    unsigned RegBankID = (RegClass2RegBank[RegClassID / 8] >> ((RegClassID % 8) * 4)) & 15;
    if (RegBankID != InvalidRegBankID)
      return getRegBank(RegBankID);
  }  llvm_unreachable(llvm::Twine("Target needs to handle register class ID 0x").concat(llvm::Twine::utohexstr(RegClassID)).str().c_str());
}
} // end namespace llvm
#endif // GET_TARGET_REGBANK_IMPL
