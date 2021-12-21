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
