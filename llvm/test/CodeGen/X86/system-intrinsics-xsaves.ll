; RUN: llc < %s -mtriple=i686-unknown-unknown -mattr=+xsave,+xsaves | FileCheck %s

define void @test_xsaves(ptr %ptr, i32 %hi, i32 %lo) {
; CHECK-LABEL: test_xsaves
; CHECK: movl   8(%esp), %edx
; CHECK: movl   12(%esp), %eax
; CHECK: movl   4(%esp), %ecx
; CHECK: xsaves (%ecx)
  call void @llvm.x86.xsaves(ptr %ptr, i32 %hi, i32 %lo)
  ret void;
}
declare void @llvm.x86.xsaves(ptr, i32, i32)

define void @test_xrstors(ptr %ptr, i32 %hi, i32 %lo) {
; CHECK-LABEL: test_xrstors
; CHECK: movl    8(%esp), %edx
; CHECK: movl    12(%esp), %eax
; CHECK: movl    4(%esp), %ecx
; CHECK: xrstors (%ecx)
  call void @llvm.x86.xrstors(ptr %ptr, i32 %hi, i32 %lo)
  ret void;
}
declare void @llvm.x86.xrstors(ptr, i32, i32)
