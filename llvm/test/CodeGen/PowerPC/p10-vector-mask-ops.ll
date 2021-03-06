; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -verify-machineinstrs -mtriple=powerpc64le-unknown-linux-gnu \
; RUN:   -mcpu=pwr10 -ppc-asm-full-reg-names -ppc-vsr-nums-as-vr < %s | \
; RUN:   FileCheck %s
; RUN: llc -verify-machineinstrs -mtriple=powerpc64-unknown-linux-gnu \
; RUN:   -mcpu=pwr10 -ppc-asm-full-reg-names -ppc-vsr-nums-as-vr < %s | \
; RUN:   FileCheck %s
; RUN: llc -verify-machineinstrs -mtriple=powerpc64-ibm-aix-xcoff \
; RUN:   -mcpu=pwr10 -ppc-asm-full-reg-names -ppc-vsr-nums-as-vr < %s | \
; RUN:   FileCheck %s

; This test case aims to test the vector mask manipulation operations
; on Power10.

declare i32 @llvm.ppc.altivec.vextractbm(<16 x i8>)
declare i32 @llvm.ppc.altivec.vextracthm(<8 x i16>)
declare i32 @llvm.ppc.altivec.vextractwm(<4 x i32>)
declare i32 @llvm.ppc.altivec.vextractdm(<2 x i64>)
declare i32 @llvm.ppc.altivec.vextractqm(<1 x i128>)

define i32 @test_vextractbm(<16 x i8> %a) {
; CHECK-LABEL: test_vextractbm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vextractbm r3, v2
; CHECK-NEXT:    blr
entry:
  %ext = tail call i32 @llvm.ppc.altivec.vextractbm(<16 x i8> %a)
  ret i32 %ext
}

define i32 @test_vextracthm(<8 x i16> %a) {
; CHECK-LABEL: test_vextracthm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vextracthm r3, v2
; CHECK-NEXT:    blr
entry:
  %ext = tail call i32 @llvm.ppc.altivec.vextracthm(<8 x i16> %a)
  ret i32 %ext
}

define i32 @test_vextractwm(<4 x i32> %a) {
; CHECK-LABEL: test_vextractwm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vextractwm r3, v2
; CHECK-NEXT:    blr
entry:
  %ext = tail call i32 @llvm.ppc.altivec.vextractwm(<4 x i32> %a)
  ret i32 %ext
}

define i32 @test_vextractdm(<2 x i64> %a) {
; CHECK-LABEL: test_vextractdm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vextractdm r3, v2
; CHECK-NEXT:    blr
entry:
  %ext = tail call i32 @llvm.ppc.altivec.vextractdm(<2 x i64> %a)
  ret i32 %ext
}

define i32 @test_vextractqm(<1 x i128> %a) {
; CHECK-LABEL: test_vextractqm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vextractqm r3, v2
; CHECK-NEXT:    blr
entry:
  %ext = tail call i32 @llvm.ppc.altivec.vextractqm(<1 x i128> %a)
  ret i32 %ext
}

declare <16 x i8> @llvm.ppc.altivec.vexpandbm(<16 x i8>)
declare <8 x i16> @llvm.ppc.altivec.vexpandhm(<8 x i16>)
declare <4 x i32> @llvm.ppc.altivec.vexpandwm(<4 x i32>)
declare <2 x i64> @llvm.ppc.altivec.vexpanddm(<2 x i64>)
declare <1 x i128> @llvm.ppc.altivec.vexpandqm(<1 x i128>)

define <16 x i8> @test_vexpandbm(<16 x i8> %a) {
; CHECK-LABEL: test_vexpandbm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vexpandbm v2, v2
; CHECK-NEXT:    blr
entry:
  %exp = tail call <16 x i8> @llvm.ppc.altivec.vexpandbm(<16 x i8> %a)
  ret <16 x i8> %exp
}

define <8 x i16> @test_vexpandhm(<8 x i16> %a) {
; CHECK-LABEL: test_vexpandhm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vexpandhm v2, v2
; CHECK-NEXT:    blr
entry:
  %exp = tail call <8 x i16> @llvm.ppc.altivec.vexpandhm(<8 x i16> %a)
  ret <8 x i16> %exp
}

define <4 x i32> @test_vexpandwm(<4 x i32> %a) {
; CHECK-LABEL: test_vexpandwm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vexpandwm v2, v2
; CHECK-NEXT:    blr
entry:
  %exp = tail call <4 x i32> @llvm.ppc.altivec.vexpandwm(<4 x i32> %a)
  ret <4 x i32> %exp
}

define <2 x i64> @test_vexpanddm(<2 x i64> %a) {
; CHECK-LABEL: test_vexpanddm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vexpanddm v2, v2
; CHECK-NEXT:    blr
entry:
  %exp = tail call <2 x i64> @llvm.ppc.altivec.vexpanddm(<2 x i64> %a)
  ret <2 x i64> %exp
}

define <1 x i128> @test_vexpandqm(<1 x i128> %a) {
; CHECK-LABEL: test_vexpandqm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vexpandqm v2, v2
; CHECK-NEXT:    blr
entry:
  %exp = tail call <1 x i128> @llvm.ppc.altivec.vexpandqm(<1 x i128> %a)
  ret <1 x i128> %exp
}

declare i64 @llvm.ppc.altivec.vcntmbb(<16 x i8>, i32)
declare i64 @llvm.ppc.altivec.vcntmbh(<8 x i16>, i32)
declare i64 @llvm.ppc.altivec.vcntmbw(<4 x i32>, i32)
declare i64 @llvm.ppc.altivec.vcntmbd(<2 x i64>, i32)

define i64 @test_vcntmbb(<16 x i8> %a) {
; CHECK-LABEL: test_vcntmbb:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vcntmbb r3, v2, 1
; CHECK-NEXT:    blr
entry:
  %cnt = tail call i64 @llvm.ppc.altivec.vcntmbb(<16 x i8> %a, i32 1)
  ret i64 %cnt
}

define i64 @test_vcntmbh(<8 x i16> %a) {
; CHECK-LABEL: test_vcntmbh:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vcntmbh r3, v2, 0
; CHECK-NEXT:    blr
entry:
  %cnt = tail call i64 @llvm.ppc.altivec.vcntmbh(<8 x i16> %a, i32 0)
  ret i64 %cnt
}

define i64 @test_vcntmbw(<4 x i32> %a) {
; CHECK-LABEL: test_vcntmbw:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vcntmbw r3, v2, 1
; CHECK-NEXT:    blr
entry:
  %cnt = tail call i64 @llvm.ppc.altivec.vcntmbw(<4 x i32> %a, i32 1)
  ret i64 %cnt
}

define i64 @test_vcntmbd(<2 x i64> %a) {
; CHECK-LABEL: test_vcntmbd:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    vcntmbd r3, v2, 0
; CHECK-NEXT:    blr
entry:
  %cnt = tail call i64 @llvm.ppc.altivec.vcntmbd(<2 x i64> %a, i32 0)
  ret i64 %cnt
}

declare <16 x i8> @llvm.ppc.altivec.mtvsrbm(i64)
declare <8 x i16> @llvm.ppc.altivec.mtvsrhm(i64)
declare <4 x i32> @llvm.ppc.altivec.mtvsrwm(i64)
declare <2 x i64> @llvm.ppc.altivec.mtvsrdm(i64)
declare <1 x i128> @llvm.ppc.altivec.mtvsrqm(i64)

define <16 x i8>  @test_mtvsrbm(i64 %a) {
; CHECK-LABEL: test_mtvsrbm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrbm v2, r3
; CHECK-NEXT:    blr
entry:
  %mv = tail call <16 x i8> @llvm.ppc.altivec.mtvsrbm(i64 %a)
  ret <16 x i8> %mv
}

define <16 x i8>  @test_mtvsrbmi() {
; CHECK-LABEL: test_mtvsrbmi:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrbmi v2, 1
; CHECK-NEXT:    blr
entry:
  %mv = tail call <16 x i8> @llvm.ppc.altivec.mtvsrbm(i64 1)
  ret <16 x i8> %mv
}

define <16 x i8>  @test_mtvsrbmi2() {
; CHECK-LABEL: test_mtvsrbmi2:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrbmi v2, 255
; CHECK-NEXT:    blr
entry:
  %mv = tail call <16 x i8> @llvm.ppc.altivec.mtvsrbm(i64 255)
  ret <16 x i8> %mv
}

define <16 x i8>  @test_mtvsrbmi3() {
; CHECK-LABEL: test_mtvsrbmi3:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrbmi v2, 65535
; CHECK-NEXT:    blr
entry:
  %mv = tail call <16 x i8> @llvm.ppc.altivec.mtvsrbm(i64 65535)
  ret <16 x i8> %mv
}

define <16 x i8>  @test_mtvsrbmi4() {
; CHECK-LABEL: test_mtvsrbmi4:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrbmi v2, 0
; CHECK-NEXT:    blr
entry:
  %mv = tail call <16 x i8> @llvm.ppc.altivec.mtvsrbm(i64 65536)
  ret <16 x i8> %mv
}

define <16 x i8>  @test_mtvsrbmi5() {
; CHECK-LABEL: test_mtvsrbmi5:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrbmi v2, 10
; CHECK-NEXT:    blr
entry:
  %mv = tail call <16 x i8> @llvm.ppc.altivec.mtvsrbm(i64 65546)
  ret <16 x i8> %mv
}

define <8 x i16> @test_mtvsrhm(i64 %a) {
; CHECK-LABEL: test_mtvsrhm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrhm v2, r3
; CHECK-NEXT:    blr
entry:
  %mv = tail call <8 x i16> @llvm.ppc.altivec.mtvsrhm(i64 %a)
  ret <8 x i16> %mv
}

define <4 x i32> @test_mtvsrwm(i64 %a) {
; CHECK-LABEL: test_mtvsrwm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrwm v2, r3
; CHECK-NEXT:    blr
entry:
  %mv = tail call <4 x i32> @llvm.ppc.altivec.mtvsrwm(i64 %a)
  ret <4 x i32> %mv
}

define <2 x i64> @test_mtvsrdm(i64 %a) {
; CHECK-LABEL: test_mtvsrdm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrdm v2, r3
; CHECK-NEXT:    blr
entry:
  %mv = tail call <2 x i64> @llvm.ppc.altivec.mtvsrdm(i64 %a)
  ret <2 x i64> %mv
}

define <1 x i128> @test_mtvsrqm(i64 %a) {
; CHECK-LABEL: test_mtvsrqm:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    mtvsrqm v2, r3
; CHECK-NEXT:    blr
entry:
  %mv = tail call <1 x i128> @llvm.ppc.altivec.mtvsrqm(i64 %a)
  ret <1 x i128> %mv
}
