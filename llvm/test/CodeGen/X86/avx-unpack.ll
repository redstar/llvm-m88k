; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=avx | FileCheck %s

define <8 x float> @unpackhips(<8 x float> %src1, <8 x float> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhips:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpckhps {{.*#+}} ymm0 = ymm0[2],ymm1[2],ymm0[3],ymm1[3],ymm0[6],ymm1[6],ymm0[7],ymm1[7]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <8 x float> %src1, <8 x float> %src2, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  ret <8 x float> %shuffle.i
}

define <4 x double> @unpackhipd(<4 x double> %src1, <4 x double> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhipd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpckhpd {{.*#+}} ymm0 = ymm0[1],ymm1[1],ymm0[3],ymm1[3]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <4 x double> %src1, <4 x double> %src2, <4 x i32> <i32 1, i32 5, i32 3, i32 7>
  ret <4 x double> %shuffle.i
}

define <8 x float> @unpacklops(<8 x float> %src1, <8 x float> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklops:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpcklps {{.*#+}} ymm0 = ymm0[0],ymm1[0],ymm0[1],ymm1[1],ymm0[4],ymm1[4],ymm0[5],ymm1[5]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <8 x float> %src1, <8 x float> %src2, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  ret <8 x float> %shuffle.i
}

define <4 x double> @unpacklopd(<4 x double> %src1, <4 x double> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklopd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpcklpd {{.*#+}} ymm0 = ymm0[0],ymm1[0],ymm0[2],ymm1[2]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <4 x double> %src1, <4 x double> %src2, <4 x i32> <i32 0, i32 4, i32 2, i32 6>
  ret <4 x double> %shuffle.i
}

define <8 x float> @unpacklops_not(<8 x float> %src1, <8 x float> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklops_not:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpckhps {{.*#+}} xmm2 = xmm0[2],xmm1[2],xmm0[3],xmm1[3]
; CHECK-NEXT:    vunpcklps {{.*#+}} xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1]
; CHECK-NEXT:    vinsertf128 $1, %xmm2, %ymm0, %ymm0
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <8 x float> %src1, <8 x float> %src2, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 2, i32 10, i32 3, i32 11>
  ret <8 x float> %shuffle.i
}

define <4 x double> @unpacklopd_not(<4 x double> %src1, <4 x double> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklopd_not:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpckhpd {{.*#+}} xmm2 = xmm0[1],xmm1[1]
; CHECK-NEXT:    vmovlhps {{.*#+}} xmm0 = xmm0[0],xmm1[0]
; CHECK-NEXT:    vinsertf128 $1, %xmm2, %ymm0, %ymm0
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <4 x double> %src1, <4 x double> %src2, <4 x i32> <i32 0, i32 4, i32 1, i32 5>
  ret <4 x double> %shuffle.i
}

define <8 x float> @unpackhips_not(<8 x float> %src1, <8 x float> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhips_not:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermilps {{.*#+}} ymm1 = ymm1[u,2,u,3,u,4,u,5]
; CHECK-NEXT:    vpermilps {{.*#+}} ymm0 = ymm0[2,u,3,u,4,u,5,u]
; CHECK-NEXT:    vblendps {{.*#+}} ymm0 = ymm0[0],ymm1[1],ymm0[2],ymm1[3],ymm0[4],ymm1[5],ymm0[6],ymm1[7]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <8 x float> %src1, <8 x float> %src2, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 4, i32 12, i32 5, i32 13>
  ret <8 x float> %shuffle.i
}

define <4 x double> @unpackhipd_not(<4 x double> %src1, <4 x double> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhipd_not:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vperm2f128 {{.*#+}} ymm1 = ymm1[2,3,2,3]
; CHECK-NEXT:    vperm2f128 {{.*#+}} ymm0 = ymm0[2,3,2,3]
; CHECK-NEXT:    vshufpd {{.*#+}} ymm0 = ymm0[0],ymm1[0],ymm0[3],ymm1[3]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <4 x double> %src1, <4 x double> %src2, <4 x i32> <i32 2, i32 6, i32 3, i32 7>
  ret <4 x double> %shuffle.i
}

;;;;
;;;; Unpack versions using the fp unit for int unpacking
;;;;

define <8 x i32> @unpackhips1(<8 x i32> %src1, <8 x i32> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhips1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpckhps {{.*#+}} ymm0 = ymm0[2],ymm1[2],ymm0[3],ymm1[3],ymm0[6],ymm1[6],ymm0[7],ymm1[7]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <8 x i32> %src1, <8 x i32> %src2, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  ret <8 x i32> %shuffle.i
}

define <8 x i32> @unpackhips2(ptr %src1, ptr %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhips2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vmovaps (%rdi), %ymm0
; CHECK-NEXT:    vunpckhps {{.*#+}} ymm0 = ymm0[2],mem[2],ymm0[3],mem[3],ymm0[6],mem[6],ymm0[7],mem[7]
; CHECK-NEXT:    retq
  %a = load <8 x i32>, ptr %src1
  %b = load <8 x i32>, ptr %src2
  %shuffle.i = shufflevector <8 x i32> %a, <8 x i32> %b, <8 x i32> <i32 2, i32 10, i32 3, i32 11, i32 6, i32 14, i32 7, i32 15>
  ret <8 x i32> %shuffle.i
}

define <4 x i64> @unpackhipd1(<4 x i64> %src1, <4 x i64> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhipd1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpckhpd {{.*#+}} ymm0 = ymm0[1],ymm1[1],ymm0[3],ymm1[3]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <4 x i64> %src1, <4 x i64> %src2, <4 x i32> <i32 1, i32 5, i32 3, i32 7>
  ret <4 x i64> %shuffle.i
}

define <4 x i64> @unpackhipd2(ptr %src1, ptr %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhipd2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vmovaps (%rdi), %ymm0
; CHECK-NEXT:    vunpckhpd {{.*#+}} ymm0 = ymm0[1],mem[1],ymm0[3],mem[3]
; CHECK-NEXT:    retq
  %a = load <4 x i64>, ptr %src1
  %b = load <4 x i64>, ptr %src2
  %shuffle.i = shufflevector <4 x i64> %a, <4 x i64> %b, <4 x i32> <i32 1, i32 5, i32 3, i32 7>
  ret <4 x i64> %shuffle.i
}

define <8 x i32> @unpacklops1(<8 x i32> %src1, <8 x i32> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklops1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpcklps {{.*#+}} ymm0 = ymm0[0],ymm1[0],ymm0[1],ymm1[1],ymm0[4],ymm1[4],ymm0[5],ymm1[5]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <8 x i32> %src1, <8 x i32> %src2, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  ret <8 x i32> %shuffle.i
}

define <8 x i32> @unpacklops2(ptr %src1, ptr %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklops2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vmovaps (%rdi), %ymm0
; CHECK-NEXT:    vunpcklps {{.*#+}} ymm0 = ymm0[0],mem[0],ymm0[1],mem[1],ymm0[4],mem[4],ymm0[5],mem[5]
; CHECK-NEXT:    retq
  %a = load <8 x i32>, ptr %src1
  %b = load <8 x i32>, ptr %src2
  %shuffle.i = shufflevector <8 x i32> %a, <8 x i32> %b, <8 x i32> <i32 0, i32 8, i32 1, i32 9, i32 4, i32 12, i32 5, i32 13>
  ret <8 x i32> %shuffle.i
}

define <4 x i64> @unpacklopd1(<4 x i64> %src1, <4 x i64> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklopd1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vunpcklpd {{.*#+}} ymm0 = ymm0[0],ymm1[0],ymm0[2],ymm1[2]
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <4 x i64> %src1, <4 x i64> %src2, <4 x i32> <i32 0, i32 4, i32 2, i32 6>
  ret <4 x i64> %shuffle.i
}

define <4 x i64> @unpacklopd2(ptr %src1, ptr %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklopd2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vmovaps (%rdi), %ymm0
; CHECK-NEXT:    vunpcklpd {{.*#+}} ymm0 = ymm0[0],mem[0],ymm0[2],mem[2]
; CHECK-NEXT:    retq
  %a = load <4 x i64>, ptr %src1
  %b = load <4 x i64>, ptr %src2
  %shuffle.i = shufflevector <4 x i64> %a, <4 x i64> %b, <4 x i32> <i32 0, i32 4, i32 2, i32 6>
  ret <4 x i64> %shuffle.i
}

define <16 x i16> @unpackhwd_undef(<16 x i16> %src1) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhwd_undef:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpunpckhwd {{.*#+}} xmm1 = xmm0[4,4,5,5,6,6,7,7]
; CHECK-NEXT:    vextractf128 $1, %ymm0, %xmm0
; CHECK-NEXT:    vpunpckhwd {{.*#+}} xmm0 = xmm0[4,4,5,5,6,6,7,7]
; CHECK-NEXT:    vinsertf128 $1, %xmm0, %ymm1, %ymm0
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <16 x i16> %src1, <16 x i16> %src1, <16 x i32> <i32 4, i32 20, i32 5, i32 21, i32 6, i32 22, i32 7, i32 23, i32 12, i32 28, i32 13, i32 29, i32 14, i32 30, i32 15, i32 31>
  ret <16 x i16> %shuffle.i
}

define <16 x i16> @unpacklwd_undef(<16 x i16> %src1) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklwd_undef:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpunpcklwd {{.*#+}} xmm1 = xmm0[0,0,1,1,2,2,3,3]
; CHECK-NEXT:    vextractf128 $1, %ymm0, %xmm0
; CHECK-NEXT:    vpunpcklwd {{.*#+}} xmm0 = xmm0[0,0,1,1,2,2,3,3]
; CHECK-NEXT:    vinsertf128 $1, %xmm0, %ymm1, %ymm0
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <16 x i16> %src1, <16 x i16> %src1, <16 x i32> <i32 0, i32 16, i32 1, i32 17, i32 2, i32 18, i32 3, i32 19, i32 8, i32 24, i32 9, i32 25, i32 10, i32 26, i32 11, i32 27>
  ret <16 x i16> %shuffle.i
}

define <32 x i8> @unpackhbw_undef(<32 x i8> %src1, <32 x i8> %src2) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpackhbw_undef:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpunpckhbw {{.*#+}} xmm1 = xmm0[8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15]
; CHECK-NEXT:    vextractf128 $1, %ymm0, %xmm0
; CHECK-NEXT:    vpunpckhbw {{.*#+}} xmm0 = xmm0[8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15]
; CHECK-NEXT:    vinsertf128 $1, %xmm0, %ymm1, %ymm0
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <32 x i8> %src1, <32 x i8> %src1, <32 x i32> <i32 8, i32 40, i32 9, i32 41, i32 10, i32 42, i32 11, i32 43, i32 12, i32 44, i32 13, i32 45, i32 14, i32 46, i32 15, i32 47, i32 24, i32 56, i32 25, i32 57, i32 26, i32 58, i32 27, i32 59, i32 28, i32 60, i32 29, i32 61, i32 30, i32 62, i32 31, i32 63>
  ret <32 x i8> %shuffle.i
}

define <32 x i8> @unpacklbw_undef(<32 x i8> %src1) nounwind uwtable readnone ssp {
; CHECK-LABEL: unpacklbw_undef:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpunpcklbw {{.*#+}} xmm1 = xmm0[0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7]
; CHECK-NEXT:    vextractf128 $1, %ymm0, %xmm0
; CHECK-NEXT:    vpunpcklbw {{.*#+}} xmm0 = xmm0[0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7]
; CHECK-NEXT:    vinsertf128 $1, %xmm0, %ymm1, %ymm0
; CHECK-NEXT:    retq
  %shuffle.i = shufflevector <32 x i8> %src1, <32 x i8> %src1, <32 x i32> <i32 0, i32 32, i32 1, i32 33, i32 2, i32 34, i32 3, i32 35, i32 4, i32 36, i32 5, i32 37, i32 6, i32 38, i32 7, i32 39, i32 16, i32 48, i32 17, i32 49, i32 18, i32 50, i32 19, i32 51, i32 20, i32 52, i32 21, i32 53, i32 22, i32 54, i32 23, i32 55>
  ret <32 x i8> %shuffle.i
}

