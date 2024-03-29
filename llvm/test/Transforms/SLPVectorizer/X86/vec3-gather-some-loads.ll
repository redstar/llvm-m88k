; NOTE: Assertions have been autogenerated by utils/update_test_checks.py UTC_ARGS: --version 4
; RUN: opt -passes=slp-vectorizer -mtriple=x86_64-apple-macosx -S %s | FileCheck %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"

define void @test_insert_loads(ptr %A, ptr noalias %B, float %0) #0 {
; CHECK-LABEL: define void @test_insert_loads(
; CHECK-SAME: ptr [[A:%.*]], ptr noalias [[B:%.*]], float [[TMP0:%.*]]) #[[ATTR0:[0-9]+]] {
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[MULADD_0:%.*]] = tail call float @llvm.fmuladd.f32(float [[TMP0]], float 1.000000e+00, float 1.000000e+00)
; CHECK-NEXT:    [[TMP1:%.*]] = insertelement <2 x float> poison, float [[TMP0]], i32 0
; CHECK-NEXT:    [[TMP2:%.*]] = shufflevector <2 x float> [[TMP1]], <2 x float> poison, <2 x i32> zeroinitializer
; CHECK-NEXT:    [[TMP3:%.*]] = call <2 x float> @llvm.fmuladd.v2f32(<2 x float> [[TMP2]], <2 x float> <float 3.000000e+00, float 2.000000e+00>, <2 x float> <float 3.000000e+00, float 2.000000e+00>)
; CHECK-NEXT:    [[A_28:%.*]] = getelementptr i8, ptr [[A]], i64 28
; CHECK-NEXT:    [[L_A_28:%.*]] = load float, ptr [[A_28]], align 4
; CHECK-NEXT:    [[A_12:%.*]] = getelementptr i8, ptr [[A]], i64 12
; CHECK-NEXT:    [[L_A_12:%.*]] = load float, ptr [[A_12]], align 4
; CHECK-NEXT:    [[GEP_4:%.*]] = getelementptr i8, ptr [[B]], i64 4
; CHECK-NEXT:    [[L_B_0:%.*]] = load float, ptr [[B]], align 4
; CHECK-NEXT:    [[GEP_28:%.*]] = getelementptr i8, ptr [[B]], i64 28
; CHECK-NEXT:    [[GEP_20:%.*]] = getelementptr i8, ptr [[B]], i64 20
; CHECK-NEXT:    [[TMP4:%.*]] = insertelement <4 x float> poison, float [[TMP0]], i32 0
; CHECK-NEXT:    [[TMP5:%.*]] = shufflevector <4 x float> [[TMP4]], <4 x float> poison, <4 x i32> zeroinitializer
; CHECK-NEXT:    [[TMP6:%.*]] = insertelement <4 x float> <float poison, float poison, float poison, float 4.000000e+00>, float [[L_A_12]], i32 0
; CHECK-NEXT:    [[TMP7:%.*]] = insertelement <4 x float> [[TMP6]], float [[L_A_28]], i32 1
; CHECK-NEXT:    [[TMP8:%.*]] = shufflevector <4 x float> [[TMP7]], <4 x float> poison, <4 x i32> <i32 0, i32 1, i32 1, i32 3>
; CHECK-NEXT:    [[TMP9:%.*]] = insertelement <4 x float> <float poison, float 0.000000e+00, float 0.000000e+00, float 4.000000e+00>, float [[L_B_0]], i32 0
; CHECK-NEXT:    [[TMP10:%.*]] = call <4 x float> @llvm.fmuladd.v4f32(<4 x float> [[TMP5]], <4 x float> [[TMP8]], <4 x float> [[TMP9]])
; CHECK-NEXT:    store <4 x float> [[TMP10]], ptr [[GEP_4]], align 4
; CHECK-NEXT:    store <2 x float> [[TMP3]], ptr [[GEP_20]], align 4
; CHECK-NEXT:    store float [[MULADD_0]], ptr [[GEP_28]], align 4
; CHECK-NEXT:    ret void
;
entry:
  %muladd.0 = tail call float @llvm.fmuladd.f32(float %0, float 1.000000e+00, float 1.000000e+00)
  %muladd.1 = tail call float @llvm.fmuladd.f32(float %0, float 2.000000e+00, float 2.000000e+00)
  %muladd.2 = tail call float @llvm.fmuladd.f32(float %0, float 3.000000e+00, float 3.000000e+00)
  %muladd.3 = tail call float @llvm.fmuladd.f32(float %0, float 4.000000e+00, float 4.000000e+00)
  %A.28 = getelementptr i8, ptr %A, i64 28
  %l.A.28 = load float, ptr %A.28, align 4
  %muladd.4 = tail call float @llvm.fmuladd.f32(float %0, float %l.A.28, float 0.000000e+00)
  %muladd.5 = tail call float @llvm.fmuladd.f32(float %0, float %l.A.28, float 0.000000e+00)
  %A.12 = getelementptr i8, ptr %A, i64 12
  %l.A.12  = load float, ptr %A.12, align 4
  %gep.4  = getelementptr i8, ptr %B, i64 4
  %gep.12 = getelementptr i8, ptr %B, i64 12
  %l.B.0 = load float, ptr %B, align 4
  %muladd.6  = tail call float @llvm.fmuladd.f32(float %0, float %l.A.12, float %l.B.0)
  %gep.28 = getelementptr i8, ptr %B, i64 28
  %gep.24 = getelementptr i8, ptr %B, i64 24
  %gep.20 = getelementptr i8, ptr %B, i64 20
  %gep.16 = getelementptr i8, ptr %B, i64 16
  %gep.8 = getelementptr i8, ptr %B, i64 8
  store float %muladd.6, ptr %gep.4, align 4
  store float %muladd.5, ptr %gep.8, align 8
  store float %muladd.4, ptr %gep.12, align 4
  store float %muladd.3, ptr %gep.16, align 16
  store float %muladd.2, ptr %gep.20, align 4
  store float %muladd.1, ptr %gep.24, align 8
  store float %muladd.0, ptr %gep.28, align 4
  ret void
}

declare float @llvm.fmuladd.f32(float, float, float)

attributes #0 = { "target-cpu"="skylake-avx512" }
