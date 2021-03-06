; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown | FileCheck %s --check-prefix=X64
; RUN: llc < %s -mtriple=i386-unknown-unknown   | FileCheck %s --check-prefix=X32

define i8 @select_i8_neg1_or_0(i1 %a) {
; X64-LABEL: select_i8_neg1_or_0:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    andb $1, %al
; X64-NEXT:    negb %al
; X64-NEXT:    # kill: def $al killed $al killed $eax
; X64-NEXT:    retq
;
; X32-LABEL: select_i8_neg1_or_0:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    andb $1, %al
; X32-NEXT:    negb %al
; X32-NEXT:    retl
  %b = sext i1 %a to i8
  ret i8 %b
}

define i8 @select_i8_neg1_or_0_zeroext(i1 zeroext %a) {
; X64-LABEL: select_i8_neg1_or_0_zeroext:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    negb %al
; X64-NEXT:    # kill: def $al killed $al killed $eax
; X64-NEXT:    retq
;
; X32-LABEL: select_i8_neg1_or_0_zeroext:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    negb %al
; X32-NEXT:    retl
  %b = sext i1 %a to i8
  ret i8 %b
}

define i16 @select_i16_neg1_or_0(i1 %a) {
; X64-LABEL: select_i16_neg1_or_0:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    andl $1, %eax
; X64-NEXT:    negl %eax
; X64-NEXT:    # kill: def $ax killed $ax killed $eax
; X64-NEXT:    retq
;
; X32-LABEL: select_i16_neg1_or_0:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    andl $1, %eax
; X32-NEXT:    negl %eax
; X32-NEXT:    # kill: def $ax killed $ax killed $eax
; X32-NEXT:    retl
  %b = sext i1 %a to i16
  ret i16 %b
}

define i16 @select_i16_neg1_or_0_zeroext(i1 zeroext %a) {
; X64-LABEL: select_i16_neg1_or_0_zeroext:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    negl %eax
; X64-NEXT:    # kill: def $ax killed $ax killed $eax
; X64-NEXT:    retq
;
; X32-LABEL: select_i16_neg1_or_0_zeroext:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    negl %eax
; X32-NEXT:    # kill: def $ax killed $ax killed $eax
; X32-NEXT:    retl
  %b = sext i1 %a to i16
  ret i16 %b
}

define i32 @select_i32_neg1_or_0(i1 %a) {
; X64-LABEL: select_i32_neg1_or_0:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    andl $1, %eax
; X64-NEXT:    negl %eax
; X64-NEXT:    retq
;
; X32-LABEL: select_i32_neg1_or_0:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    andl $1, %eax
; X32-NEXT:    negl %eax
; X32-NEXT:    retl
  %b = sext i1 %a to i32
  ret i32 %b
}

define i32 @select_i32_neg1_or_0_zeroext(i1 zeroext %a) {
; X64-LABEL: select_i32_neg1_or_0_zeroext:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    negl %eax
; X64-NEXT:    retq
;
; X32-LABEL: select_i32_neg1_or_0_zeroext:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    negl %eax
; X32-NEXT:    retl
  %b = sext i1 %a to i32
  ret i32 %b
}

define i64 @select_i64_neg1_or_0(i1 %a) {
; X64-LABEL: select_i64_neg1_or_0:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    andl $1, %eax
; X64-NEXT:    negq %rax
; X64-NEXT:    retq
;
; X32-LABEL: select_i64_neg1_or_0:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    andl $1, %eax
; X32-NEXT:    negl %eax
; X32-NEXT:    movl %eax, %edx
; X32-NEXT:    retl
  %b = sext i1 %a to i64
  ret i64 %b
}

define i64 @select_i64_neg1_or_0_zeroext(i1 zeroext %a) {
; X64-LABEL: select_i64_neg1_or_0_zeroext:
; X64:       # %bb.0:
; X64-NEXT:    movl %edi, %eax
; X64-NEXT:    negq %rax
; X64-NEXT:    retq
;
; X32-LABEL: select_i64_neg1_or_0_zeroext:
; X32:       # %bb.0:
; X32-NEXT:    movzbl {{[0-9]+}}(%esp), %eax
; X32-NEXT:    negl %eax
; X32-NEXT:    movl %eax, %edx
; X32-NEXT:    retl
  %b = sext i1 %a to i64
  ret i64 %b
}

