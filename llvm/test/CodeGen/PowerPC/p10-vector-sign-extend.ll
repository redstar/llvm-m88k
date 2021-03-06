; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -verify-machineinstrs -mtriple=powerpc64le-unknown-linux-gnu \
; RUN:   -mcpu=pwr10 -ppc-asm-full-reg-names -ppc-vsr-nums-as-vr < %s | \
; RUN:   FileCheck %s
; RUN: llc -verify-machineinstrs -mtriple=powerpc64-ibm-aix-xcoff \
; RUN:   -mcpu=pwr10 -ppc-asm-full-reg-names -ppc-vsr-nums-as-vr < %s | \
; RUN:   FileCheck %s

; This test case aims to test vector sign extend builtins.

declare <1 x i128> @llvm.ppc.altivec.vextsd2q(<2 x i64>) nounwind readnone

define <1 x i128> @test_vextsd2q(<2 x i64> %x) nounwind readnone {
; CHECK-LABEL: test_vextsd2q:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vextsd2q v2, v2
; CHECK-NEXT:    blr
  %tmp = tail call <1 x i128> @llvm.ppc.altivec.vextsd2q(<2 x i64> %x)
  ret <1 x i128> %tmp
}
