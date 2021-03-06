; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-- | FileCheck %s --implicit-check-not IMPLICIT_DEF

define void @foo(ptr %p) {
; CHECK-LABEL: foo:
; CHECK:       # %bb.0:
; CHECK-NEXT:    xorps %xmm0, %xmm0
; CHECK-NEXT:    movlps %xmm0, (%rdi)
; CHECK-NEXT:    retq
  %t = insertelement <2 x float> undef, float 0.0, i32 0
  %v = insertelement <2 x float> %t,   float 0.0, i32 1
  br label %bb8

bb8:
  store <2 x float> %v, ptr %p
  ret void
}
