; RUN: llc %s -combiner-tokenfactor-inline-limit=5 -o - | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.snork = type { i8 }
%struct.wombat = type { [15 x i32] }

; CHECK:          pushq   %rbx
; CHECK-NEXT:     andq    $-32, %rsp
; CHECK-NEXT:     subq    $66144, %rsp            # imm = 0x10260
; CHECK-NEXT:     .cfi_offset %rbx, -24
; CHECK-NEXT:     movabsq $-868076584853899022, %rax # imm = 0xF3F3F8F201F2F8F2
; CHECK-NEXT:     movq    %rax, (%rsp)
; CHECK-NEXT:     movb    $-13, 8263(%rsp)
; CHECK-NEXT:     movq    %rdi, %rbx
; CHECK-NEXT:     callq   hoge
; CHECK-NEXT:     movq    %rbx, %rdi
; CHECK-NEXT:     callq   hoge
; CHECK-NEXT:     callq   hoge
; CHECK-NEXT:     callq   hoge
; CHECK-NEXT:     callq   eggs
; CHECK-NEXT:     callq   hoge
; CHECK-NEXT:     movq    %rbx, %rax
; CHECK-NEXT:     leaq    -8(%rbp), %rsp
; CHECK-NEXT:     popq    %rbx
; CHECK-NEXT:     popq    %rbp
; CHECK-NEXT:    .cfi_def_cfa %rsp, 8
; CHECK-NEXT:    retq
define void @spam(ptr noalias sret(%struct.snork) %arg, ptr %arg2) {
bb:
  %tmp = alloca i8, i64 66112, align 32
  %tmp7 = ptrtoint ptr %tmp to i64
  %tmp914 = inttoptr i64 undef to ptr
  %tmp915 = inttoptr i64 undef to ptr
  %tmp916 = inttoptr i64 undef to ptr
  %tmp917 = inttoptr i64 undef to ptr
  %tmp918 = inttoptr i64 undef to ptr
  %tmp921 = inttoptr i64 undef to ptr
  %tmp2055 = inttoptr i64 %tmp7 to ptr
  store i64 -868076584853899022, ptr %tmp2055, align 1
  %tmp2056 = add i64 %tmp7, 8263
  %tmp2057 = inttoptr i64 %tmp2056 to ptr
  store i8 -13, ptr %tmp2057, align 1
  br label %bb2058

bb2058:                                           ; preds = %bb
  call void @hoge(ptr %arg)
  call void @hoge(ptr %arg)
  call void @hoge(ptr %tmp915)
  call void @hoge(ptr %tmp916)
  call void @eggs(ptr %tmp918, ptr %tmp914, ptr %tmp917)
  call void @hoge(ptr %tmp921)
  ret void
}

declare void @hoge(ptr)

declare void @eggs(ptr, ptr, ptr)
