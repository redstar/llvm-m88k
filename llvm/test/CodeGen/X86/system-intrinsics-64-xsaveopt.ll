; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+xsaveopt | FileCheck %s

define void @test_xsaveopt(ptr %ptr, i32 %hi, i32 %lo) {
; CHECK-LABEL: test_xsaveopt
; CHECK: movl     %edx, %eax
; CHECK: movl     %esi, %edx
; CHECK: xsaveopt (%rdi)
  call void @llvm.x86.xsaveopt(ptr %ptr, i32 %hi, i32 %lo)
  ret void;
}
declare void @llvm.x86.xsaveopt(ptr, i32, i32)

define void @test_xsaveopt64(ptr %ptr, i32 %hi, i32 %lo) {
; CHECK-LABEL: test_xsaveopt64
; CHECK: movl       %edx, %eax
; CHECK: movl       %esi, %edx
; CHECK: xsaveopt64 (%rdi)
  call void @llvm.x86.xsaveopt64(ptr %ptr, i32 %hi, i32 %lo)
  ret void;
}
declare void @llvm.x86.xsaveopt64(ptr, i32, i32)
