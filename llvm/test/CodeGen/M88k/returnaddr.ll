; RUN: llc < %s -mtriple=m88k-openbsd -mcpu=mc88100 -m88k-enable-delay-slot-filler=false -verify-machineinstrs | FileCheck %s
; RUN: llc < %s -mtriple=m88k-openbsd -mcpu=mc88110 -m88k-enable-delay-slot-filler=false -verify-machineinstrs | FileCheck %s

define ptr @ra0() nounwind {
  %fp = tail call ptr @llvm.returnaddress(i32 0)
  ret ptr %fp
}

define ptr @ra1() nounwind {
  %fp = tail call ptr @llvm.returnaddress(i32 1)
  ret ptr %fp
}

define ptr @ra2() nounwind {
  %fp = tail call ptr @llvm.returnaddress(i32 2)
  ret ptr %fp
}
