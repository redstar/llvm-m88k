; Test var arg functionality.
;
; RUN: llc < %s -mtriple=m88k-openbsd -mcpu=mc88100 -m88k-enable-delay-slot-filler=false -verify-machineinstrs | FileCheck %s
; RUN: llc < %s -mtriple=m88k-openbsd -mcpu=mc88110 -m88k-enable-delay-slot-filler=false -verify-machineinstrs | FileCheck %s

declare void @llvm.va_start(ptr) #1
declare void @llvm.va_end(ptr)

%struct.__va_list_tag = type { i32, ptr, ptr }

define i32 @sum(i32 noundef %num_args, ...) {
entry:
  %num_args.addr = alloca i32, align 4
  %val = alloca i32, align 4
  %ap = alloca %struct.__va_list_tag, align 4
  %i = alloca i32, align 4
  store i32 %num_args, ptr %num_args.addr, align 4
  store i32 0, ptr %val, align 4
  call void @llvm.va_start(ptr %ap)
  call void @llvm.va_end(ptr %ap)
  %0 = load i32, ptr %val, align 4
  ret i32 %0
}
