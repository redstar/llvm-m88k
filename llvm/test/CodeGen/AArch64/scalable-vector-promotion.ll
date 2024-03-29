; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -mtriple=aarch64 -passes='require<profile-summary>,function(codegenprepare)' -S < %s | FileCheck %s

; This test intends to check vector promotion for scalable vector. Current target lowering
; rejects scalable vector before reaching getConstantVector() in CodeGenPrepare. This test
; will assert once target lowering is ready, then we can bring in implementation for non-splat
; codepath for scalable vector.

define void @simpleOneInstructionPromotion(ptr %addr1, ptr %dest) {
; CHECK-LABEL: @simpleOneInstructionPromotion(
; CHECK-NEXT:    [[IN1:%.*]] = load <vscale x 2 x i32>, ptr [[ADDR1:%.*]], align 8
; CHECK-NEXT:    [[EXTRACT:%.*]] = extractelement <vscale x 2 x i32> [[IN1]], i32 1
; CHECK-NEXT:    [[OUT:%.*]] = or i32 [[EXTRACT]], 1
; CHECK-NEXT:    store i32 [[OUT]], ptr [[DEST:%.*]], align 4
; CHECK-NEXT:    ret void
;
  %in1 = load <vscale x 2 x i32>, ptr %addr1, align 8
  %extract = extractelement <vscale x 2 x i32> %in1, i32 1
  %out = or i32 %extract, 1
  store i32 %out, ptr %dest, align 4
  ret void
}

