//===-- M88kMCTargetDesc.cpp - M88k target descriptions -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "M88kMCTargetDesc.h"
#include "TargetInfo/M88kTargetInfo.h"
#include "llvm/MC/MCDwarf.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/TargetRegistry.h"

using namespace llvm;

#define GET_INSTRINFO_MC_DESC
#include "M88kGenInstrInfo.inc"

#define GET_SUBTARGETINFO_MC_DESC
#include "M88kGenSubtargetInfo.inc"

#define GET_REGINFO_MC_DESC
#include "M88kGenRegisterInfo.inc"

static MCInstrInfo *createM88kMCInstrInfo() {
  MCInstrInfo *X = new MCInstrInfo();
  InitM88kMCInstrInfo(X);
  return X;
}

static MCRegisterInfo *createM88kMCRegisterInfo(const Triple &TT) {
  MCRegisterInfo *X = new MCRegisterInfo();
  InitM88kMCRegisterInfo(X, M88k::R1);
  return X;
}

static MCSubtargetInfo *createM88kMCSubtargetInfo(const Triple &TT,
                                                  StringRef CPU, StringRef FS) {
  return createM88kMCSubtargetInfoImpl(TT, CPU, /*TuneCPU*/ CPU, FS);
}


extern "C" LLVM_EXTERNAL_VISIBILITY void LLVMInitializeM88kTargetMC() {
  // Register the MCInstrInfo.
  TargetRegistry::RegisterMCInstrInfo(getTheM88kTarget(),
                                      createM88kMCInstrInfo);
  // Register the MCRegisterInfo.
  TargetRegistry::RegisterMCRegInfo(getTheM88kTarget(),
                                    createM88kMCRegisterInfo);

  // Register the MCSubtargetInfo.
  TargetRegistry::RegisterMCSubtargetInfo(getTheM88kTarget(),
                                          createM88kMCSubtargetInfo);
}
