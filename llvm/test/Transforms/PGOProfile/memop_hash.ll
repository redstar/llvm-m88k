; RUN: opt < %s -passes=pgo-instr-gen -S | FileCheck %s

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @llvm.memcpy.p0.p0.i32(ptr nocapture writeonly, ptr nocapture readonly, i32, i1)

define i64 @foo1(ptr %a, ptr %b, i32 %s) {
entry:
  call void @llvm.memcpy.p0.p0.i32(ptr %a, ptr %b, i32 %s, i1 false);
  ret i64 0
}

define i64 @foo2(ptr %a, ptr %b, i32 %s) {
entry:
  ret i64 0
}

; The two hashes should not be equal as the existence of the memcpy should change the hash.
;
; CHECK: @foo1
; CHECK: call void @llvm.instrprof.increment(ptr @__profn_foo1, i64 [[FOO1_HASH:[0-9]+]], i32 1, i32 0)
; CHECK: @foo2
; CHECK-NOT: call void @llvm.instrprof.increment(ptr @__profn_foo2, i64 [[FOO1_HASH]], i32 1, i32 0)
