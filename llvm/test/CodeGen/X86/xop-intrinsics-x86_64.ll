; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx,+fma4,+xop | FileCheck %s

define <2 x double> @test_int_x86_xop_vpermil2pd(<2 x double> %a0, <2 x double> %a1, <2 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2pd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2pd $1, %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x double> @llvm.x86.xop.vpermil2pd(<2 x double> %a0, <2 x double> %a1, <2 x i64> %a2, i8 1) ;  [#uses=1]
  ret <2 x double> %res
}
define <2 x double> @test_int_x86_xop_vpermil2pd_mr(<2 x double> %a0, ptr %a1, <2 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2pd_mr:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2pd $1, %xmm1, (%rdi), %xmm0, %xmm0
; CHECK-NEXT:    retq
  %vec = load <2 x double>, ptr %a1
  %res = call <2 x double> @llvm.x86.xop.vpermil2pd(<2 x double> %a0, <2 x double> %vec, <2 x i64> %a2, i8 1) ;  [#uses=1]
  ret <2 x double> %res
}
define <2 x double> @test_int_x86_xop_vpermil2pd_rm(<2 x double> %a0, <2 x double> %a1, ptr %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2pd_rm:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2pd $1, (%rdi), %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %vec = load <2 x i64>, ptr %a2
  %res = call <2 x double> @llvm.x86.xop.vpermil2pd(<2 x double> %a0, <2 x double> %a1, <2 x i64> %vec, i8 1) ;  [#uses=1]
  ret <2 x double> %res
}
declare <2 x double> @llvm.x86.xop.vpermil2pd(<2 x double>, <2 x double>, <2 x i64>, i8) nounwind readnone

define <4 x double> @test_int_x86_xop_vpermil2pd_256(<4 x double> %a0, <4 x double> %a1, <4 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2pd_256:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2pd $2, %ymm2, %ymm1, %ymm0, %ymm0
; CHECK-NEXT:    retq
  %res = call <4 x double> @llvm.x86.xop.vpermil2pd.256(<4 x double> %a0, <4 x double> %a1, <4 x i64> %a2, i8 2) ;
  ret <4 x double> %res
}
define <4 x double> @test_int_x86_xop_vpermil2pd_256_mr(<4 x double> %a0, ptr %a1, <4 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2pd_256_mr:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2pd $2, %ymm1, (%rdi), %ymm0, %ymm0
; CHECK-NEXT:    retq
  %vec = load <4 x double>, ptr %a1
  %res = call <4 x double> @llvm.x86.xop.vpermil2pd.256(<4 x double> %a0, <4 x double> %vec, <4 x i64> %a2, i8 2) ;
  ret <4 x double> %res
}
define <4 x double> @test_int_x86_xop_vpermil2pd_256_rm(<4 x double> %a0, <4 x double> %a1, ptr %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2pd_256_rm:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2pd $2, (%rdi), %ymm1, %ymm0, %ymm0
; CHECK-NEXT:    retq
  %vec = load <4 x i64>, ptr %a2
  %res = call <4 x double> @llvm.x86.xop.vpermil2pd.256(<4 x double> %a0, <4 x double> %a1, <4 x i64> %vec, i8 2) ;
  ret <4 x double> %res
}
declare <4 x double> @llvm.x86.xop.vpermil2pd.256(<4 x double>, <4 x double>, <4 x i64>, i8) nounwind readnone

define <4 x float> @test_int_x86_xop_vpermil2ps(<4 x float> %a0, <4 x float> %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2ps:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2ps $3, %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x float> @llvm.x86.xop.vpermil2ps(<4 x float> %a0, <4 x float> %a1, <4 x i32> %a2, i8 3) ;
  ret <4 x float> %res
}
declare <4 x float> @llvm.x86.xop.vpermil2ps(<4 x float>, <4 x float>, <4 x i32>, i8) nounwind readnone

define <8 x float> @test_int_x86_xop_vpermil2ps_256(<8 x float> %a0, <8 x float> %a1, <8 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpermil2ps_256:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpermil2ps $4, %ymm2, %ymm1, %ymm0, %ymm0
; CHECK-NEXT:    retq
  %res = call <8 x float> @llvm.x86.xop.vpermil2ps.256(<8 x float> %a0, <8 x float> %a1, <8 x i32> %a2, i8 4) ;
  ret <8 x float> %res
}
declare <8 x float> @llvm.x86.xop.vpermil2ps.256(<8 x float>, <8 x float>, <8 x i32>, i8) nounwind readnone

define <2 x i64> @test_int_x86_xop_vpcmov(<2 x i64> %a0, <2 x i64> %a1, <2 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpcmov:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpcmov %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %1 = xor <2 x i64> %a2, <i64 -1, i64 -1>
  %2 = and <2 x i64> %a0, %a2
  %3 = and <2 x i64> %a1, %1
  %4 = or <2 x i64> %2, %3
  ret <2 x i64> %4
}

define <4 x i64> @test_int_x86_xop_vpcmov_256(<4 x i64> %a0, <4 x i64> %a1, <4 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpcmov_256:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpcmov %ymm2, %ymm1, %ymm0, %ymm0
; CHECK-NEXT:    retq
  %1 = xor <4 x i64> %a2, <i64 -1, i64 -1, i64 -1, i64 -1>
  %2 = and <4 x i64> %a0, %a2
  %3 = and <4 x i64> %a1, %1
  %4 = or <4 x i64> %2, %3
  ret <4 x i64> %4
}
define <4 x i64> @test_int_x86_xop_vpcmov_256_mr(<4 x i64> %a0, ptr %a1, <4 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpcmov_256_mr:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpcmov %ymm1, (%rdi), %ymm0, %ymm0
; CHECK-NEXT:    retq
  %vec = load <4 x i64>, ptr %a1
  %1 = xor <4 x i64> %a2, <i64 -1, i64 -1, i64 -1, i64 -1>
  %2 = and <4 x i64> %a0, %a2
  %3 = and <4 x i64> %vec, %1
  %4 = or <4 x i64> %2, %3
  ret <4 x i64> %4
}
define <4 x i64> @test_int_x86_xop_vpcmov_256_rm(<4 x i64> %a0, <4 x i64> %a1, ptr %a2) {
; CHECK-LABEL: test_int_x86_xop_vpcmov_256_rm:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpcmov (%rdi), %ymm1, %ymm0, %ymm0
; CHECK-NEXT:    retq
  %vec = load <4 x i64>, ptr %a2
  %1 = xor <4 x i64> %vec, <i64 -1, i64 -1, i64 -1, i64 -1>
  %2 = and <4 x i64> %a0, %vec
  %3 = and <4 x i64> %a1, %1
  %4 = or <4 x i64> %2, %3
  ret <4 x i64> %4
}

define <4 x i32> @test_int_x86_xop_vphaddbd(<16 x i8> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddbd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddbd %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vphaddbd(<16 x i8> %a0) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vphaddbd(<16 x i8>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vphaddbq(<16 x i8> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddbq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddbq %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vphaddbq(<16 x i8> %a0) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vphaddbq(<16 x i8>) nounwind readnone

define <8 x i16> @test_int_x86_xop_vphaddbw(<16 x i8> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddbw:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddbw %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <8 x i16> @llvm.x86.xop.vphaddbw(<16 x i8> %a0) ;
  ret <8 x i16> %res
}
declare <8 x i16> @llvm.x86.xop.vphaddbw(<16 x i8>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vphadddq(<4 x i32> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphadddq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphadddq %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vphadddq(<4 x i32> %a0) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vphadddq(<4 x i32>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vphaddubd(<16 x i8> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddubd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddubd %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vphaddubd(<16 x i8> %a0) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vphaddubd(<16 x i8>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vphaddubq(<16 x i8> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddubq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddubq %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vphaddubq(<16 x i8> %a0) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vphaddubq(<16 x i8>) nounwind readnone

define <8 x i16> @test_int_x86_xop_vphaddubw(<16 x i8> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddubw:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddubw %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <8 x i16> @llvm.x86.xop.vphaddubw(<16 x i8> %a0) ;
  ret <8 x i16> %res
}
declare <8 x i16> @llvm.x86.xop.vphaddubw(<16 x i8>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vphaddudq(<4 x i32> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddudq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddudq %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vphaddudq(<4 x i32> %a0) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vphaddudq(<4 x i32>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vphadduwd(<8 x i16> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphadduwd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphadduwd %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vphadduwd(<8 x i16> %a0) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vphadduwd(<8 x i16>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vphadduwq(<8 x i16> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphadduwq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphadduwq %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vphadduwq(<8 x i16> %a0) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vphadduwq(<8 x i16>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vphaddwd(<8 x i16> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddwd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddwd %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vphaddwd(<8 x i16> %a0) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vphaddwd(<8 x i16>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vphaddwq(<8 x i16> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphaddwq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphaddwq %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vphaddwq(<8 x i16> %a0) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vphaddwq(<8 x i16>) nounwind readnone

define <8 x i16> @test_int_x86_xop_vphsubbw(<16 x i8> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphsubbw:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphsubbw %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <8 x i16> @llvm.x86.xop.vphsubbw(<16 x i8> %a0) ;
  ret <8 x i16> %res
}
declare <8 x i16> @llvm.x86.xop.vphsubbw(<16 x i8>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vphsubdq(<4 x i32> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphsubdq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphsubdq %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vphsubdq(<4 x i32> %a0) ;
  ret <2 x i64> %res
}
define <2 x i64> @test_int_x86_xop_vphsubdq_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vphsubdq_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphsubdq (%rdi), %xmm0
; CHECK-NEXT:    retq
  %vec = load <4 x i32>, ptr %a0
  %res = call <2 x i64> @llvm.x86.xop.vphsubdq(<4 x i32> %vec) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vphsubdq(<4 x i32>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vphsubwd(<8 x i16> %a0) {
; CHECK-LABEL: test_int_x86_xop_vphsubwd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphsubwd %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vphsubwd(<8 x i16> %a0) ;
  ret <4 x i32> %res
}
define <4 x i32> @test_int_x86_xop_vphsubwd_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vphsubwd_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vphsubwd (%rdi), %xmm0
; CHECK-NEXT:    retq
  %vec = load <8 x i16>, ptr %a0
  %res = call <4 x i32> @llvm.x86.xop.vphsubwd(<8 x i16> %vec) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vphsubwd(<8 x i16>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpmacsdd(<4 x i32> %a0, <4 x i32> %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacsdd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacsdd %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpmacsdd(<4 x i32> %a0, <4 x i32> %a1, <4 x i32> %a2) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpmacsdd(<4 x i32>, <4 x i32>, <4 x i32>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vpmacsdqh(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacsdqh:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacsdqh %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vpmacsdqh(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vpmacsdqh(<4 x i32>, <4 x i32>, <2 x i64>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vpmacsdql(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacsdql:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacsdql %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vpmacsdql(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vpmacsdql(<4 x i32>, <4 x i32>, <2 x i64>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpmacssdd(<4 x i32> %a0, <4 x i32> %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacssdd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacssdd %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpmacssdd(<4 x i32> %a0, <4 x i32> %a1, <4 x i32> %a2) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpmacssdd(<4 x i32>, <4 x i32>, <4 x i32>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vpmacssdqh(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacssdqh:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacssdqh %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vpmacssdqh(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vpmacssdqh(<4 x i32>, <4 x i32>, <2 x i64>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vpmacssdql(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacssdql:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacssdql %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vpmacssdql(<4 x i32> %a0, <4 x i32> %a1, <2 x i64> %a2) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vpmacssdql(<4 x i32>, <4 x i32>, <2 x i64>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpmacsswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacsswd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacsswd %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpmacsswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpmacsswd(<8 x i16>, <8 x i16>, <4 x i32>) nounwind readnone

define <8 x i16> @test_int_x86_xop_vpmacssww(<8 x i16> %a0, <8 x i16> %a1, <8 x i16> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacssww:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacssww %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <8 x i16> @llvm.x86.xop.vpmacssww(<8 x i16> %a0, <8 x i16> %a1, <8 x i16> %a2) ;
  ret <8 x i16> %res
}
declare <8 x i16> @llvm.x86.xop.vpmacssww(<8 x i16>, <8 x i16>, <8 x i16>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpmacswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacswd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacswd %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpmacswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpmacswd(<8 x i16>, <8 x i16>, <4 x i32>) nounwind readnone

define <8 x i16> @test_int_x86_xop_vpmacsww(<8 x i16> %a0, <8 x i16> %a1, <8 x i16> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmacsww:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmacsww %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <8 x i16> @llvm.x86.xop.vpmacsww(<8 x i16> %a0, <8 x i16> %a1, <8 x i16> %a2) ;
  ret <8 x i16> %res
}
declare <8 x i16> @llvm.x86.xop.vpmacsww(<8 x i16>, <8 x i16>, <8 x i16>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpmadcsswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmadcsswd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmadcsswd %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpmadcsswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpmadcsswd(<8 x i16>, <8 x i16>, <4 x i32>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpmadcswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmadcswd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmadcswd %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpmadcswd(<8 x i16> %a0, <8 x i16> %a1, <4 x i32> %a2) ;
  ret <4 x i32> %res
}
define <4 x i32> @test_int_x86_xop_vpmadcswd_mem(<8 x i16> %a0, ptr %a1, <4 x i32> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpmadcswd_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpmadcswd %xmm1, (%rdi), %xmm0, %xmm0
; CHECK-NEXT:    retq
  %vec = load <8 x i16>, ptr %a1
  %res = call <4 x i32> @llvm.x86.xop.vpmadcswd(<8 x i16> %a0, <8 x i16> %vec, <4 x i32> %a2) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpmadcswd(<8 x i16>, <8 x i16>, <4 x i32>) nounwind readnone

define <16 x i8> @test_int_x86_xop_vpperm(<16 x i8> %a0, <16 x i8> %a1, <16 x i8> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpperm:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpperm %xmm2, %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <16 x i8> @llvm.x86.xop.vpperm(<16 x i8> %a0, <16 x i8> %a1, <16 x i8> %a2) ;
  ret <16 x i8> %res
}
define <16 x i8> @test_int_x86_xop_vpperm_rm(<16 x i8> %a0, <16 x i8> %a1, ptr %a2) {
; CHECK-LABEL: test_int_x86_xop_vpperm_rm:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpperm (%rdi), %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %vec = load <16 x i8>, ptr %a2
  %res = call <16 x i8> @llvm.x86.xop.vpperm(<16 x i8> %a0, <16 x i8> %a1, <16 x i8> %vec) ;
  ret <16 x i8> %res
}
define <16 x i8> @test_int_x86_xop_vpperm_mr(<16 x i8> %a0, ptr %a1, <16 x i8> %a2) {
; CHECK-LABEL: test_int_x86_xop_vpperm_mr:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpperm %xmm1, (%rdi), %xmm0, %xmm0
; CHECK-NEXT:    retq
  %vec = load <16 x i8>, ptr %a1
  %res = call <16 x i8> @llvm.x86.xop.vpperm(<16 x i8> %a0, <16 x i8> %vec, <16 x i8> %a2) ;
  ret <16 x i8> %res
}
declare <16 x i8> @llvm.x86.xop.vpperm(<16 x i8>, <16 x i8>, <16 x i8>) nounwind readnone

define <16 x i8> @test_int_x86_xop_vpshab(<16 x i8> %a0, <16 x i8> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshab:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshab %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <16 x i8> @llvm.x86.xop.vpshab(<16 x i8> %a0, <16 x i8> %a1) ;
  ret <16 x i8> %res
}
declare <16 x i8> @llvm.x86.xop.vpshab(<16 x i8>, <16 x i8>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpshad(<4 x i32> %a0, <4 x i32> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshad:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshad %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpshad(<4 x i32> %a0, <4 x i32> %a1) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpshad(<4 x i32>, <4 x i32>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vpshaq(<2 x i64> %a0, <2 x i64> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshaq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshaq %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vpshaq(<2 x i64> %a0, <2 x i64> %a1) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vpshaq(<2 x i64>, <2 x i64>) nounwind readnone

define <8 x i16> @test_int_x86_xop_vpshaw(<8 x i16> %a0, <8 x i16> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshaw:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshaw %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <8 x i16> @llvm.x86.xop.vpshaw(<8 x i16> %a0, <8 x i16> %a1) ;
  ret <8 x i16> %res
}
declare <8 x i16> @llvm.x86.xop.vpshaw(<8 x i16>, <8 x i16>) nounwind readnone

define <16 x i8> @test_int_x86_xop_vpshlb(<16 x i8> %a0, <16 x i8> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshlb:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshlb %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <16 x i8> @llvm.x86.xop.vpshlb(<16 x i8> %a0, <16 x i8> %a1) ;
  ret <16 x i8> %res
}
declare <16 x i8> @llvm.x86.xop.vpshlb(<16 x i8>, <16 x i8>) nounwind readnone

define <4 x i32> @test_int_x86_xop_vpshld(<4 x i32> %a0, <4 x i32> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshld:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshld %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x i32> @llvm.x86.xop.vpshld(<4 x i32> %a0, <4 x i32> %a1) ;
  ret <4 x i32> %res
}
declare <4 x i32> @llvm.x86.xop.vpshld(<4 x i32>, <4 x i32>) nounwind readnone

define <2 x i64> @test_int_x86_xop_vpshlq(<2 x i64> %a0, <2 x i64> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshlq:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshlq %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x i64> @llvm.x86.xop.vpshlq(<2 x i64> %a0, <2 x i64> %a1) ;
  ret <2 x i64> %res
}
declare <2 x i64> @llvm.x86.xop.vpshlq(<2 x i64>, <2 x i64>) nounwind readnone

define <8 x i16> @test_int_x86_xop_vpshlw(<8 x i16> %a0, <8 x i16> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshlw:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshlw %xmm1, %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <8 x i16> @llvm.x86.xop.vpshlw(<8 x i16> %a0, <8 x i16> %a1) ;
  ret <8 x i16> %res
}
define <8 x i16> @test_int_x86_xop_vpshlw_rm(<8 x i16> %a0, ptr %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshlw_rm:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshlw (%rdi), %xmm0, %xmm0
; CHECK-NEXT:    retq
  %vec = load <8 x i16>, ptr %a1
  %res = call <8 x i16> @llvm.x86.xop.vpshlw(<8 x i16> %a0, <8 x i16> %vec) ;
  ret <8 x i16> %res
}
define <8 x i16> @test_int_x86_xop_vpshlw_mr(ptr %a0, <8 x i16> %a1) {
; CHECK-LABEL: test_int_x86_xop_vpshlw_mr:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vpshlw %xmm0, (%rdi), %xmm0
; CHECK-NEXT:    retq
  %vec = load <8 x i16>, ptr %a0
  %res = call <8 x i16> @llvm.x86.xop.vpshlw(<8 x i16> %vec, <8 x i16> %a1) ;
  ret <8 x i16> %res
}
declare <8 x i16> @llvm.x86.xop.vpshlw(<8 x i16>, <8 x i16>) nounwind readnone

define <4 x float> @test_int_x86_xop_vfrcz_ss(<4 x float> %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_ss:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczss %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x float> @llvm.x86.xop.vfrcz.ss(<4 x float> %a0) ;
  ret <4 x float> %res
}
define <4 x float> @test_int_x86_xop_vfrcz_ss_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_ss_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczss (%rdi), %xmm0
; CHECK-NEXT:    retq
  %elem = load float, ptr %a0
  %vec = insertelement <4 x float> undef, float %elem, i32 0
  %res = call <4 x float> @llvm.x86.xop.vfrcz.ss(<4 x float> %vec) ;
  ret <4 x float> %res
}
declare <4 x float> @llvm.x86.xop.vfrcz.ss(<4 x float>) nounwind readnone

define <2 x double> @test_int_x86_xop_vfrcz_sd(<2 x double> %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_sd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczsd %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x double> @llvm.x86.xop.vfrcz.sd(<2 x double> %a0) ;
  ret <2 x double> %res
}
define <2 x double> @test_int_x86_xop_vfrcz_sd_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_sd_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczsd (%rdi), %xmm0
; CHECK-NEXT:    retq
  %elem = load double, ptr %a0
  %vec = insertelement <2 x double> undef, double %elem, i32 0
  %res = call <2 x double> @llvm.x86.xop.vfrcz.sd(<2 x double> %vec) ;
  ret <2 x double> %res
}
declare <2 x double> @llvm.x86.xop.vfrcz.sd(<2 x double>) nounwind readnone

define <2 x double> @test_int_x86_xop_vfrcz_pd(<2 x double> %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_pd:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczpd %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <2 x double> @llvm.x86.xop.vfrcz.pd(<2 x double> %a0) ;
  ret <2 x double> %res
}
define <2 x double> @test_int_x86_xop_vfrcz_pd_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_pd_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczpd (%rdi), %xmm0
; CHECK-NEXT:    retq
  %vec = load <2 x double>, ptr %a0
  %res = call <2 x double> @llvm.x86.xop.vfrcz.pd(<2 x double> %vec) ;
  ret <2 x double> %res
}
declare <2 x double> @llvm.x86.xop.vfrcz.pd(<2 x double>) nounwind readnone

define <4 x double> @test_int_x86_xop_vfrcz_pd_256(<4 x double> %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_pd_256:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczpd %ymm0, %ymm0
; CHECK-NEXT:    retq
  %res = call <4 x double> @llvm.x86.xop.vfrcz.pd.256(<4 x double> %a0) ;
  ret <4 x double> %res
}
define <4 x double> @test_int_x86_xop_vfrcz_pd_256_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_pd_256_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczpd (%rdi), %ymm0
; CHECK-NEXT:    retq
  %vec = load <4 x double>, ptr %a0
  %res = call <4 x double> @llvm.x86.xop.vfrcz.pd.256(<4 x double> %vec) ;
  ret <4 x double> %res
}
declare <4 x double> @llvm.x86.xop.vfrcz.pd.256(<4 x double>) nounwind readnone

define <4 x float> @test_int_x86_xop_vfrcz_ps(<4 x float> %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_ps:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczps %xmm0, %xmm0
; CHECK-NEXT:    retq
  %res = call <4 x float> @llvm.x86.xop.vfrcz.ps(<4 x float> %a0) ;
  ret <4 x float> %res
}
define <4 x float> @test_int_x86_xop_vfrcz_ps_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_ps_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczps (%rdi), %xmm0
; CHECK-NEXT:    retq
  %vec = load <4 x float>, ptr %a0
  %res = call <4 x float> @llvm.x86.xop.vfrcz.ps(<4 x float> %vec) ;
  ret <4 x float> %res
}
declare <4 x float> @llvm.x86.xop.vfrcz.ps(<4 x float>) nounwind readnone

define <8 x float> @test_int_x86_xop_vfrcz_ps_256(<8 x float> %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_ps_256:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczps %ymm0, %ymm0
; CHECK-NEXT:    retq
  %res = call <8 x float> @llvm.x86.xop.vfrcz.ps.256(<8 x float> %a0) ;
  ret <8 x float> %res
}
define <8 x float> @test_int_x86_xop_vfrcz_ps_256_mem(ptr %a0) {
; CHECK-LABEL: test_int_x86_xop_vfrcz_ps_256_mem:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vfrczps (%rdi), %ymm0
; CHECK-NEXT:    retq
  %vec = load <8 x float>, ptr %a0
  %res = call <8 x float> @llvm.x86.xop.vfrcz.ps.256(<8 x float> %vec) ;
  ret <8 x float> %res
}
declare <8 x float> @llvm.x86.xop.vfrcz.ps.256(<8 x float>) nounwind readnone
