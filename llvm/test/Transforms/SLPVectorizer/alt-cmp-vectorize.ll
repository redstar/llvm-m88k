; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -S -passes=slp-vectorizer < %s | FileCheck %s

define i32 @alt_cmp(i16 %call46) {
; CHECK-LABEL: @alt_cmp(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[CALL47:%.*]] = tail call i16 null(i16 0)
; CHECK-NEXT:    [[TMP0:%.*]] = insertelement <4 x i16> <i16 0, i16 poison, i16 0, i16 0>, i16 [[CALL46:%.*]], i32 1
; CHECK-NEXT:    [[TMP1:%.*]] = insertelement <4 x i16> <i16 0, i16 poison, i16 0, i16 0>, i16 [[CALL47]], i32 1
; CHECK-NEXT:    [[TMP2:%.*]] = icmp ult <4 x i16> [[TMP0]], [[TMP1]]
; CHECK-NEXT:    [[TMP3:%.*]] = icmp ugt <4 x i16> [[TMP0]], [[TMP1]]
; CHECK-NEXT:    [[TMP4:%.*]] = shufflevector <4 x i1> [[TMP2]], <4 x i1> [[TMP3]], <4 x i32> <i32 0, i32 5, i32 2, i32 3>
; CHECK-NEXT:    [[TMP5:%.*]] = call i1 @llvm.vector.reduce.or.v4i1(<4 x i1> [[TMP4]])
; CHECK-NEXT:    [[TMP6:%.*]] = zext i1 [[TMP5]] to i16
; CHECK-NEXT:    [[OP_RDX:%.*]] = or i16 [[TMP6]], 0
; CHECK-NEXT:    [[EXT:%.*]] = zext i16 [[OP_RDX]] to i32
; CHECK-NEXT:    ret i32 [[EXT]]
;
entry:
  %0 = icmp ult i16 0, 0
  %cond40 = zext i1 %0 to i16
  %add41 = or i16 0, %cond40
  %call47 = tail call i16 null(i16 0)
  %.not299 = icmp ugt i16 %call46, %call47
  %cond60 = zext i1 %.not299 to i16
  %add61 = or i16 %add41, %cond60
  %1 = icmp ugt i16 0, 0
  %cond76 = zext i1 %1 to i16
  %add77 = or i16 %add61, %cond76
  %2 = icmp ult i16 0, 0
  %cond144 = zext i1 %2 to i16
  %add145 = or i16 %add77, %cond144
  %ext = zext i16 %add145 to i32
  ret i32 %ext
}
