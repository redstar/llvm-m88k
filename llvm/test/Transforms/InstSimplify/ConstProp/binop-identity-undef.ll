; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -passes=instsimplify -S %s | FileCheck %s

define i32 @and1() {
; CHECK-LABEL: @and1(
; CHECK-NEXT:    ret i32 undef
;
  %r = and i32 undef, -1
  ret i32 %r
}

define i32 @and2() {
; CHECK-LABEL: @and2(
; CHECK-NEXT:    ret i32 undef
;
  %r = and i32 -1, undef
  ret i32 %r
}

define i32 @and3_no_identity() {
; CHECK-LABEL: @and3_no_identity(
; CHECK-NEXT:    ret i32 0
;
  %r = and i32 10, undef
  ret i32 %r
}

define i32 @or1() {
; CHECK-LABEL: @or1(
; CHECK-NEXT:    ret i32 undef
;
  %r = or i32 0, undef
  ret i32 %r
}

define i32 @or2() {
; CHECK-LABEL: @or2(
; CHECK-NEXT:    ret i32 undef
;
  %r = or i32 undef, 0
  ret i32 %r
}

define i32 @or3_no_identity() {
; CHECK-LABEL: @or3_no_identity(
; CHECK-NEXT:    ret i32 -1
;
  %r = or i32 undef, 10
  ret i32 %r
}
