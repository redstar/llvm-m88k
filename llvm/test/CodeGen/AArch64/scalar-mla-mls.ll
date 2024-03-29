; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -verify-machineinstrs -mtriple=aarch64-none-linux-gnu -mattr=+neon | FileCheck %s

define ptr @test_scalar_msub(ptr %a, ptr %b) {
; CHECK-LABEL: test_scalar_msub:
; CHECK:       // %bb.0: // %entry
; CHECK-NEXT:    ldp w8, w11, [x1]
; CHECK-NEXT:    ldp w9, w10, [x0]
; CHECK-NEXT:    mul w12, w8, w9
; CHECK-NEXT:    mul w8, w10, w8
; CHECK-NEXT:    madd w8, w11, w9, w8
; CHECK-NEXT:    msub w9, w11, w10, w12
; CHECK-NEXT:    stp w9, w8, [x0]
; CHECK-NEXT:    ret
entry:
  %0 = load i32, ptr %a, align 4
  %1 = load i32, ptr %b, align 4
  %mul = mul nsw i32 %1, %0
  %_M_imag = getelementptr inbounds i8, ptr %a, i64 4
  %2 = load i32, ptr %_M_imag, align 4
  %_M_imag.i = getelementptr inbounds i8, ptr %b, i64 4
  %3 = load i32, ptr %_M_imag.i, align 4
  %mul3 = mul nsw i32 %3, %2
  %sub = sub nsw i32 %mul, %mul3
  %mul6 = mul nsw i32 %3, %0
  %mul9 = mul nsw i32 %2, %1
  %add = add nsw i32 %mul6, %mul9
  store i32 %add, ptr %_M_imag, align 4
  store i32 %sub, ptr %a, align 4
  ret ptr %a
}

define ptr @test_scalar_msub_i64(ptr %a, ptr %b) {
; CHECK-LABEL: test_scalar_msub_i64:
; CHECK:       // %bb.0: // %entry
; CHECK-NEXT:    ldr x8, [x1]
; CHECK-NEXT:    ldur x9, [x0, #4]
; CHECK-NEXT:    ldr x10, [x0]
; CHECK-NEXT:    ldur x12, [x1, #4]
; CHECK-NEXT:    mul x11, x9, x8
; CHECK-NEXT:    mul x8, x8, x10
; CHECK-NEXT:    madd x10, x12, x10, x11
; CHECK-NEXT:    msub x8, x12, x9, x8
; CHECK-NEXT:    stur x10, [x0, #4]
; CHECK-NEXT:    str x8, [x0]
; CHECK-NEXT:    ret
entry:
  %0 = load i64, ptr %a, align 8
  %1 = load i64, ptr %b, align 8
  %mul = mul nsw i64 %1, %0
  %_M_imag = getelementptr inbounds i8, ptr %a, i64 4
  %2 = load i64, ptr %_M_imag, align 8
  %_M_imag.i = getelementptr inbounds i8, ptr %b, i64 4
  %3 = load i64, ptr %_M_imag.i, align 8
  %mul3 = mul nsw i64 %3, %2
  %sub = sub nsw i64 %mul, %mul3
  %mul6 = mul nsw i64 %3, %0
  %mul9 = mul nsw i64 %2, %1
  %add = add nsw i64 %mul6, %mul9
  store i64 %add, ptr %_M_imag, align 8
  store i64 %sub, ptr %a, align 8
  ret ptr %a
}
