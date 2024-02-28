//===- M88k.cpp ----------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ABIInfoImpl.h"
#include "TargetInfo.h"

using namespace clang;
using namespace clang::CodeGen;

//===----------------------------------------------------------------------===//
// M88k ABI Implementation
//
// This is a very simple ABI that relies a lot on DefaultABIInfo.
//===----------------------------------------------------------------------===//

namespace {
class M88kABIInfo final : public ABIInfo {
  DefaultABIInfo defaultInfo;

public:
  explicit M88kABIInfo(CodeGen::CodeGenTypes &CGT)
      : ABIInfo(CGT), defaultInfo(CGT) {}

  void computeInfo(CodeGen::CGFunctionInfo &FI) const override {}

  CodeGen::Address EmitVAArg(CodeGen::CodeGenFunction &CGF,
                             CodeGen::Address VAListAddr,
                             QualType Ty) const override {
  // Assume that va_list type is correct; should be pointer to LLVM type:
  // struct {
  //    int __va_arg;
  //    int *__va_stk;
  //    int *__va_reg;
  // };

  // How are structures handled?

  // Align the argument
  // Decide which pointer to use: __va_arg < 8 ? __va_reg : __va_stk
  Address VaArgPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 0, "__va_arg_ptr");
  llvm::Value *VaArg = CGF.Builder.CreateLoad(VaArgPtr, "__va_arg");
  llvm::Value *MaxRegs = llvm::ConstantInt::get(CGF.Int32Ty, 8);
  llvm::Value *InRegs = CGF.Builder.CreateICmpULT(VaArg, MaxRegs,
                                                 "fits_in_regs");

  llvm::BasicBlock *InRegBlock = CGF.createBasicBlock("vaarg.in_reg");
  llvm::BasicBlock *InStkBlock = CGF.createBasicBlock("vaarg.in_stk");
  llvm::BasicBlock *ContBlock = CGF.createBasicBlock("vaarg.end");
  CGF.Builder.CreateCondBr(InRegs, InRegBlock, InStkBlock);

  CGF.EmitBlock(InRegBlock);
  Address VaRegPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 1, "__va_reg_ptr");
  llvm::Value *VaReg = CGF.Builder.CreateLoad(VaRegPtr, "__va_reg");
  CGF.Builder.CreateBr(ContBlock);

  CGF.EmitBlock(InStkBlock);
  Address VaStkPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 1, "__va_stk_ptr");
  llvm::Value *VaStk = CGF.Builder.CreateLoad(VaStkPtr, "__va_stk");
  CGF.Builder.CreateBr(ContBlock);

  CGF.EmitBlock(InStkBlock);
  llvm::PHINode *PHI = CGF.Builder.CreatePHI(CGF.IntPtrTy, 2, "ptr");
  PHI->addIncoming(VaReg, InRegBlock);
  PHI->addIncoming(VaStk, InStkBlock);

  // Load value
  // Increment __va_arg and pointer
  llvm::Value *One = llvm::ConstantInt::get(CGF.Int32Ty, 1);
  llvm::Value *NewVaArg =
    CGF.Builder.CreateAdd(VaArg, One, "__va_arg_plus_1");
  CGF.Builder.CreateStore(NewVaArg, VaArgPtr);

  //Address VAListAddr = emitMergePHI(CGF, RegAddr, InRegBlock, MemAddr, InMemBlock,
  //                               "va_arg.addr");

#if 0

  // Every non-vector argument occupies 8 bytes and is passed by preference
  // in either GPRs or FPRs.  Vector arguments occupy 8 or 16 bytes and are
  // always passed on the stack.
  const SystemZTargetCodeGenInfo &SZCGI =
      static_cast<const SystemZTargetCodeGenInfo &>(
          CGT.getCGM().getTargetCodeGenInfo());
  Ty = getContext().getCanonicalType(Ty);
  auto TyInfo = getContext().getTypeInfoInChars(Ty);
  llvm::Type *ArgTy = CGF.ConvertTypeForMem(Ty);
  llvm::Type *DirectTy = ArgTy;
  ABIArgInfo AI = classifyArgumentType(Ty);
  bool IsIndirect = AI.isIndirect();
  bool InFPRs = false;
  bool IsVector = false;
  CharUnits UnpaddedSize;
  CharUnits DirectAlign;
  SZCGI.handleExternallyVisibleObjABI(Ty.getTypePtr(), CGT.getCGM(),
                                      /*IsParam*/true);
  if (IsIndirect) {
    DirectTy = llvm::PointerType::getUnqual(DirectTy);
    UnpaddedSize = DirectAlign = CharUnits::fromQuantity(8);
  } else {
    if (AI.getCoerceToType())
      ArgTy = AI.getCoerceToType();
    InFPRs = (!IsSoftFloatABI && (ArgTy->isFloatTy() || ArgTy->isDoubleTy()));
    IsVector = ArgTy->isVectorTy();
    UnpaddedSize = TyInfo.Width;
    DirectAlign = TyInfo.Align;
  }
  CharUnits PaddedSize = CharUnits::fromQuantity(8);
  if (IsVector && UnpaddedSize > PaddedSize)
    PaddedSize = CharUnits::fromQuantity(16);
  assert((UnpaddedSize <= PaddedSize) && "Invalid argument size.");

  CharUnits Padding = (PaddedSize - UnpaddedSize);

  llvm::Type *IndexTy = CGF.Int64Ty;
  llvm::Value *PaddedSizeV =
    llvm::ConstantInt::get(IndexTy, PaddedSize.getQuantity());

  if (IsVector) {
    // Work out the address of a vector argument on the stack.
    // Vector arguments are always passed in the high bits of a
    // single (8 byte) or double (16 byte) stack slot.
    Address OverflowArgAreaPtr =
        CGF.Builder.CreateStructGEP(VAListAddr, 2, "overflow_arg_area_ptr");
    Address OverflowArgArea =
        Address(CGF.Builder.CreateLoad(OverflowArgAreaPtr, "overflow_arg_area"),
                CGF.Int8Ty, TyInfo.Align);
    Address MemAddr = OverflowArgArea.withElementType(DirectTy);

    // Update overflow_arg_area_ptr pointer
    llvm::Value *NewOverflowArgArea = CGF.Builder.CreateGEP(
        OverflowArgArea.getElementType(), OverflowArgArea.getPointer(),
        PaddedSizeV, "overflow_arg_area");
    CGF.Builder.CreateStore(NewOverflowArgArea, OverflowArgAreaPtr);

    return MemAddr;
  }

  assert(PaddedSize.getQuantity() == 8);

  unsigned MaxRegs, RegCountField, RegSaveIndex;
  CharUnits RegPadding;
  if (InFPRs) {
    MaxRegs = 4; // Maximum of 4 FPR arguments
    RegCountField = 1; // __fpr
    RegSaveIndex = 16; // save offset for f0
    RegPadding = CharUnits(); // floats are passed in the high bits of an FPR
  } else {
    MaxRegs = 5; // Maximum of 5 GPR arguments
    RegCountField = 0; // __gpr
    RegSaveIndex = 2; // save offset for r2
    RegPadding = Padding; // values are passed in the low bits of a GPR
  }

  Address RegCountPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, RegCountField, "reg_count_ptr");
  llvm::Value *RegCount = CGF.Builder.CreateLoad(RegCountPtr, "reg_count");
  llvm::Value *MaxRegsV = llvm::ConstantInt::get(IndexTy, MaxRegs);
  llvm::Value *InRegs = CGF.Builder.CreateICmpULT(RegCount, MaxRegsV,
                                                 "fits_in_regs");

  llvm::BasicBlock *InRegBlock = CGF.createBasicBlock("vaarg.in_reg");
  llvm::BasicBlock *InMemBlock = CGF.createBasicBlock("vaarg.in_mem");
  llvm::BasicBlock *ContBlock = CGF.createBasicBlock("vaarg.end");
  CGF.Builder.CreateCondBr(InRegs, InRegBlock, InMemBlock);

  // Emit code to load the value if it was passed in registers.
  CGF.EmitBlock(InRegBlock);

  // Work out the address of an argument register.
  llvm::Value *ScaledRegCount =
    CGF.Builder.CreateMul(RegCount, PaddedSizeV, "scaled_reg_count");
  llvm::Value *RegBase =
    llvm::ConstantInt::get(IndexTy, RegSaveIndex * PaddedSize.getQuantity()
                                      + RegPadding.getQuantity());
  llvm::Value *RegOffset =
    CGF.Builder.CreateAdd(ScaledRegCount, RegBase, "reg_offset");
  Address RegSaveAreaPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 3, "reg_save_area_ptr");
  llvm::Value *RegSaveArea =
      CGF.Builder.CreateLoad(RegSaveAreaPtr, "reg_save_area");
  Address RawRegAddr(
      CGF.Builder.CreateGEP(CGF.Int8Ty, RegSaveArea, RegOffset, "raw_reg_addr"),
      CGF.Int8Ty, PaddedSize);
  Address RegAddr = RawRegAddr.withElementType(DirectTy);

  // Update the register count
  llvm::Value *One = llvm::ConstantInt::get(IndexTy, 1);
  llvm::Value *NewRegCount =
    CGF.Builder.CreateAdd(RegCount, One, "reg_count");
  CGF.Builder.CreateStore(NewRegCount, RegCountPtr);
  CGF.EmitBranch(ContBlock);

  // Emit code to load the value if it was passed in memory.
  CGF.EmitBlock(InMemBlock);

  // Work out the address of a stack argument.
  Address OverflowArgAreaPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 2, "overflow_arg_area_ptr");
  Address OverflowArgArea =
      Address(CGF.Builder.CreateLoad(OverflowArgAreaPtr, "overflow_arg_area"),
              CGF.Int8Ty, PaddedSize);
  Address RawMemAddr =
      CGF.Builder.CreateConstByteGEP(OverflowArgArea, Padding, "raw_mem_addr");
  Address MemAddr = RawMemAddr.withElementType(DirectTy);

  // Update overflow_arg_area_ptr pointer
  llvm::Value *NewOverflowArgArea =
    CGF.Builder.CreateGEP(OverflowArgArea.getElementType(),
                          OverflowArgArea.getPointer(), PaddedSizeV,
                          "overflow_arg_area");
  CGF.Builder.CreateStore(NewOverflowArgArea, OverflowArgAreaPtr);
  CGF.EmitBranch(ContBlock);

  // Return the appropriate result.
  CGF.EmitBlock(ContBlock);
  Address ResAddr = emitMergePHI(CGF, RegAddr, InRegBlock, MemAddr, InMemBlock,
                                 "va_arg.addr");

  if (IsIndirect)
    ResAddr = Address(CGF.Builder.CreateLoad(ResAddr, "indirect_arg"), ArgTy,
                      TyInfo.Align);

  return ResAddr;
#endif
    return VAListAddr;
  }
};

class M88kTargetCodeGenInfo final : public TargetCodeGenInfo {
public:
  explicit M88kTargetCodeGenInfo(CodeGen::CodeGenTypes &CGT)
      //: TargetCodeGenInfo(std::make_unique<M88kABIInfo>(CGT)) {}
      : TargetCodeGenInfo(std::make_unique<DefaultABIInfo>(CGT)) {}
};
}

std::unique_ptr<TargetCodeGenInfo>
CodeGen::createM88kTargetCodeGenInfo(CodeGenModule &CGM) {
  return std::make_unique<M88kTargetCodeGenInfo>(CGM.getTypes());
}
