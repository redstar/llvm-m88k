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

public:
  explicit M88kABIInfo(CodeGen::CodeGenTypes &CGT) : ABIInfo(CGT) {}

  ABIArgInfo classifyReturnType(QualType RetTy) const;
  ABIArgInfo classifyArgumentType(QualType RetTy) const;

  void computeInfo(CGFunctionInfo &FI) const override;

  CodeGen::Address EmitVAArg(CodeGen::CodeGenFunction &CGF,
                             CodeGen::Address VAListAddr,
                             QualType Ty) const override;
};

class M88kTargetCodeGenInfo final : public TargetCodeGenInfo {
public:
  explicit M88kTargetCodeGenInfo(CodeGen::CodeGenTypes &CGT)
      : TargetCodeGenInfo(std::make_unique<M88kABIInfo>(CGT)) {}
};
} // namespace

ABIArgInfo M88kABIInfo::classifyArgumentType(QualType Ty) const {
  Ty = useFirstFieldIfTransparentUnion(Ty);

  if (isAggregateTypeForABI(Ty)) {
    // Records with non-trivial destructors/copy-constructors should not be
    // passed by value.
    if (CGCXXABI::RecordArgABI RAA = getRecordArgABI(Ty, getCXXABI()))
      return getNaturalAlignIndirect(Ty, RAA == CGCXXABI::RAA_DirectInMemory);

    return getNaturalAlignIndirect(Ty);
  }

  // Treat an enum type as its underlying type.
  if (const EnumType *EnumTy = Ty->getAs<EnumType>())
    Ty = EnumTy->getDecl()->getIntegerType();

  ASTContext &Context = getContext();
  if (const auto *EIT = Ty->getAs<BitIntType>())
    if (EIT->getNumBits() >
        Context.getTypeSize(Context.getTargetInfo().hasInt128Type()
                                ? Context.Int128Ty
                                : Context.LongLongTy))
      return getNaturalAlignIndirect(Ty);

  return (isPromotableIntegerTypeForABI(Ty) ? ABIArgInfo::getExtend(Ty)
                                            : ABIArgInfo::getDirect());
}

ABIArgInfo M88kABIInfo::classifyReturnType(QualType RetTy) const {
  if (RetTy->isVoidType())
    return ABIArgInfo::getIgnore();

  if (isAggregateTypeForABI(RetTy))
    return getNaturalAlignIndirect(RetTy);

  // Treat an enum type as its underlying type.
  if (const EnumType *EnumTy = RetTy->getAs<EnumType>())
    RetTy = EnumTy->getDecl()->getIntegerType();

  if (const auto *EIT = RetTy->getAs<BitIntType>())
    if (EIT->getNumBits() >
        getContext().getTypeSize(getContext().getTargetInfo().hasInt128Type()
                                     ? getContext().Int128Ty
                                     : getContext().LongLongTy))
      return getNaturalAlignIndirect(RetTy);

  return (isPromotableIntegerTypeForABI(RetTy) ? ABIArgInfo::getExtend(RetTy)
                                               : ABIArgInfo::getDirect());
}

void M88kABIInfo::computeInfo(CGFunctionInfo &FI) const {
  if (!getCXXABI().classifyReturnType(FI))
    FI.getReturnInfo() = classifyReturnType(FI.getReturnType());
  for (auto &I : FI.arguments())
    I.info = classifyArgumentType(I.type);
}

CodeGen::Address M88kABIInfo::EmitVAArg(CodeGen::CodeGenFunction &CGF,
                                        CodeGen::Address VAListAddr,
                                        QualType Ty) const {
  // Assume that va_list type is correct; should be pointer to LLVM type:
  // struct {
  //    int __va_arg;
  //    int *__va_stk;
  //    int *__va_reg;
  // };

  // How are structures handled?

  // Align the argument
  CharUnits PtrAlign = CharUnits::fromQuantity(4);
  CharUnits DirectAlign = CharUnits::fromQuantity(8);
  CharUnits SlotSize = CharUnits::fromQuantity(4);

  Ty = getContext().getCanonicalType(Ty);
  auto TyInfo = getContext().getTypeInfoInChars(Ty);
  llvm::Type *ArgTy = CGF.ConvertTypeForMem(Ty);
  llvm::Type *DirectTy = ArgTy;
  CharUnits DirectSize = TyInfo.Width;

  // Decide which pointer to use: __va_arg < 8 ? __va_reg : __va_stk.
  Address VaArgPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 0, "__va_arg.addr");
  llvm::Value *VaArg = CGF.Builder.CreateLoad(VaArgPtr, "__va_arg");
  llvm::Value *MaxRegs = llvm::ConstantInt::get(CGF.Int32Ty, 8);
  llvm::Value *InRegs =
      CGF.Builder.CreateICmpULT(VaArg, MaxRegs, "fits_in_regs");

  llvm::BasicBlock *InRegBlock = CGF.createBasicBlock("vaarg.in_reg");
  llvm::BasicBlock *InStkBlock = CGF.createBasicBlock("vaarg.in_stk");
  llvm::BasicBlock *ContBlock = CGF.createBasicBlock("vaarg.end");
  CGF.Builder.CreateCondBr(InRegs, InRegBlock, InStkBlock);

  // Value comes from register.
  CGF.EmitBlock(InRegBlock);
  Address VaRegPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 2, "__va_reg.addr");
  Address VaReg = Address(CGF.Builder.CreateLoad(VaRegPtr, "__va_reg"),
                          CGF.Int8Ty, PtrAlign);
  CGF.Builder.CreateBr(ContBlock);

  // Value comes from stack.
  CGF.EmitBlock(InStkBlock);
  Address VaStkPtr =
      CGF.Builder.CreateStructGEP(VAListAddr, 1, "__va_stk.addr");
  Address VaStk = Address(CGF.Builder.CreateLoad(VaStkPtr, "__va_stk"),
                          CGF.Int8Ty, PtrAlign);
  CGF.Builder.CreateBr(ContBlock);

  CGF.EmitBlock(ContBlock);
  Address VaAddr =
      emitMergePHI(CGF, VaReg, InRegBlock, VaStk, InStkBlock, "va_arg.addr");

  // Load value and increment pointer.
  Address ResAddr =
      emitVoidPtrDirectVAArg(CGF, VaAddr, DirectTy, DirectSize, DirectAlign,
                             SlotSize, /*AllowHigherAlign=*/true,
                             /*ForceRightAdjust=*/true);

  // Increment and store __va_arg.
  llvm::Value *One = llvm::ConstantInt::get(CGF.Int32Ty, 1);
  llvm::Value *NewVaArg = CGF.Builder.CreateAdd(VaArg, One, "__va_arg.inc");
  CGF.Builder.CreateStore(NewVaArg, VaArgPtr);

  return ResAddr;
}

std::unique_ptr<TargetCodeGenInfo>
CodeGen::createM88kTargetCodeGenInfo(CodeGenModule &CGM) {
  return std::make_unique<M88kTargetCodeGenInfo>(CGM.getTypes());
}
