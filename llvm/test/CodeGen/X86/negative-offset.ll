; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Test that a constant consisting of a global symbol with a negative offset
; is properly folded and isel'd.

@G = external dso_local global [8 x i32]
define ptr @negative_offset(ptr %a) {
; CHECK-LABEL: negative_offset:
; CHECK:       # %bb.0:
; CHECK-NEXT:    movl $G, %eax
; CHECK-NEXT:    notq %rax
; CHECK-NEXT:    addq %rdi, %rax
; CHECK-NEXT:    retq
  %t = getelementptr i8, ptr %a, i64 sub (i64 -1, i64 ptrtoint (ptr @G to i64))
  ret ptr %t
}
