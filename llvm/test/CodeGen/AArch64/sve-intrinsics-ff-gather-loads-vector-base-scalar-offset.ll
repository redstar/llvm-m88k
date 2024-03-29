; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -mtriple=aarch64-linux-gnu -mattr=+sve -verify-machineinstrs < %s | FileCheck %s

;
; LDFF1B, LDFF1W, LDFF1H, LDFF1D: vector base + scalar offset (index)
;   e.g. ldff1b { z0.d }, p0/z, [x0, z0.d]
;

; LDFF1B
define <vscale x 4 x i32> @gldff1b_s_scalar_offset(<vscale x 4 x i1> %pg, <vscale x 4 x i32> %base, i64 %offset) {
; CHECK-LABEL: gldff1b_s_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1b { z0.s }, p0/z, [x0, z0.s, uxtw]
; CHECK-NEXT:    ret
  %load = call <vscale x 4 x i8> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i8.nxv4i32(<vscale x 4 x i1> %pg,
                                                                                             <vscale x 4 x i32> %base,
                                                                                             i64 %offset)
  %res = zext <vscale x 4 x i8> %load to <vscale x 4 x i32>
  ret <vscale x 4 x i32> %res
}

define <vscale x 2 x i64> @gldff1b_d_scalar_offset(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1b_d_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1b { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x i8> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i8.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                             <vscale x 2 x i64> %base,
                                                                                             i64 %offset)
  %res = zext <vscale x 2 x i8> %load to <vscale x 2 x i64>
  ret <vscale x 2 x i64> %res
}

; LDFF1H
define <vscale x 4 x i32> @gldff1h_s_scalar_offset(<vscale x 4 x i1> %pg, <vscale x 4 x i32> %base, i64 %offset) {
; CHECK-LABEL: gldff1h_s_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1h { z0.s }, p0/z, [x0, z0.s, uxtw]
; CHECK-NEXT:    ret
  %load = call <vscale x 4 x i16> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i16.nxv4i32(<vscale x 4 x i1> %pg,
                                                                                               <vscale x 4 x i32> %base,
                                                                                               i64 %offset)
  %res = zext <vscale x 4 x i16> %load to <vscale x 4 x i32>
  ret <vscale x 4 x i32> %res
}

define <vscale x 2 x i64> @gldff1h_d_scalar_offset(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1h_d_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1h { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x i16> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i16.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                               <vscale x 2 x i64> %base,
                                                                                               i64 %offset)
  %res = zext <vscale x 2 x i16> %load to <vscale x 2 x i64>
  ret <vscale x 2 x i64> %res
}

; LDFF1W
define <vscale x 4 x i32> @gldff1w_s_scalar_offset(<vscale x 4 x i1> %pg, <vscale x 4 x i32> %base, i64 %offset) {
; CHECK-LABEL: gldff1w_s_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1w { z0.s }, p0/z, [x0, z0.s, uxtw]
; CHECK-NEXT:    ret
  %load = call <vscale x 4 x i32> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i32.nxv4i32(<vscale x 4 x i1> %pg,
                                                                                               <vscale x 4 x i32> %base,
                                                                                               i64 %offset)
  ret <vscale x 4 x i32> %load
}

define <vscale x 2 x i64> @gldff1w_d_scalar_offset(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1w_d_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1w { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x i32> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i32.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                               <vscale x 2 x i64> %base,
                                                                                               i64 %offset)
  %res = zext <vscale x 2 x i32> %load to <vscale x 2 x i64>
  ret <vscale x 2 x i64> %res
}

define <vscale x 4 x float> @gldff1w_s_scalar_offset_float(<vscale x 4 x i1> %pg, <vscale x 4 x i32> %base, i64 %offset) {
; CHECK-LABEL: gldff1w_s_scalar_offset_float:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1w { z0.s }, p0/z, [x0, z0.s, uxtw]
; CHECK-NEXT:    ret
  %load = call <vscale x 4 x float> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4f32.nxv4i32(<vscale x 4 x i1> %pg,
                                                                                                 <vscale x 4 x i32> %base,
                                                                                                 i64 %offset)
  ret <vscale x 4 x float> %load
}

; LDFF1D
define <vscale x 2 x i64> @gldff1d_d_scalar_offset(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1d_d_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1d { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x i64> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i64.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                               <vscale x 2 x i64> %base,
                                                                                               i64 %offset)
  ret <vscale x 2 x i64> %load
}

define <vscale x 2 x double> @gldff1d_d_scalar_offset_double(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1d_d_scalar_offset_double:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1d { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x double> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2f64.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                                  <vscale x 2 x i64> %base,
                                                                                                  i64 %offset)
  ret <vscale x 2 x double> %load
}

; LDFF1SB, LDFF1SW, LDFF1SH: vector base + scalar offset (index)
;   e.g. ldff1b { z0.d }, p0/z, [x0, z0.d]
;

; LDFF1SB
define <vscale x 4 x i32> @gldff1sb_s_scalar_offset(<vscale x 4 x i1> %pg, <vscale x 4 x i32> %base, i64 %offset) {
; CHECK-LABEL: gldff1sb_s_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1sb { z0.s }, p0/z, [x0, z0.s, uxtw]
; CHECK-NEXT:    ret
  %load = call <vscale x 4 x i8> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i8.nxv4i32(<vscale x 4 x i1> %pg,
                                                                                             <vscale x 4 x i32> %base,
                                                                                             i64 %offset)
  %res = sext <vscale x 4 x i8> %load to <vscale x 4 x i32>
  ret <vscale x 4 x i32> %res
}

define <vscale x 2 x i64> @gldff1sb_d_scalar_offset(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1sb_d_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1sb { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x i8> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i8.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                             <vscale x 2 x i64> %base,
                                                                                             i64 %offset)
  %res = sext <vscale x 2 x i8> %load to <vscale x 2 x i64>
  ret <vscale x 2 x i64> %res
}

; LDFF1SH
define <vscale x 4 x i32> @gldff1sh_s_scalar_offset(<vscale x 4 x i1> %pg, <vscale x 4 x i32> %base, i64 %offset) {
; CHECK-LABEL: gldff1sh_s_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1sh { z0.s }, p0/z, [x0, z0.s, uxtw]
; CHECK-NEXT:    ret
  %load = call <vscale x 4 x i16> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i16.nxv4i32(<vscale x 4 x i1> %pg,
                                                                                               <vscale x 4 x i32> %base,
                                                                                               i64 %offset)
  %res = sext <vscale x 4 x i16> %load to <vscale x 4 x i32>
  ret <vscale x 4 x i32> %res
}

define <vscale x 2 x i64> @gldff1sh_d_scalar_offset(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1sh_d_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1sh { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x i16> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i16.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                               <vscale x 2 x i64> %base,
                                                                                               i64 %offset)
  %res = sext <vscale x 2 x i16> %load to <vscale x 2 x i64>
  ret <vscale x 2 x i64> %res
}

; LDFF1SW
define <vscale x 2 x i64> @gldff1sw_d_scalar_offset(<vscale x 2 x i1> %pg, <vscale x 2 x i64> %base, i64 %offset) {
; CHECK-LABEL: gldff1sw_d_scalar_offset:
; CHECK:       // %bb.0:
; CHECK-NEXT:    ldff1sw { z0.d }, p0/z, [x0, z0.d]
; CHECK-NEXT:    ret
  %load = call <vscale x 2 x i32> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i32.nxv2i64(<vscale x 2 x i1> %pg,
                                                                                               <vscale x 2 x i64> %base,
                                                                                               i64 %offset)
  %res = sext <vscale x 2 x i32> %load to <vscale x 2 x i64>
  ret <vscale x 2 x i64> %res
}

; LDFF1B/LDFF1SB
declare <vscale x 4 x i8> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i8.nxv4i32(<vscale x 4 x i1>, <vscale x 4 x i32>, i64)
declare <vscale x 2 x i8> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i8.nxv2i64(<vscale x 2 x i1>, <vscale x 2 x i64>, i64)

; LDFF1H/LDFF1SH
declare <vscale x 4 x i16> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i16.nxv4i32(<vscale x 4 x i1>, <vscale x 4 x i32>, i64)
declare <vscale x 2 x i16> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i16.nxv2i64(<vscale x 2 x i1>, <vscale x 2 x i64>, i64)

; LDFF1W/LDFF1SW
declare <vscale x 4 x i32> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4i32.nxv4i32(<vscale x 4 x i1>, <vscale x 4 x i32>, i64)
declare <vscale x 2 x i32> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i32.nxv2i64(<vscale x 2 x i1>, <vscale x 2 x i64>, i64)

declare <vscale x 4 x float> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv4f32.nxv4i32(<vscale x 4 x i1>, <vscale x 4 x i32>, i64)

; LDFF1D
declare <vscale x 2 x i64> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2i64.nxv2i64(<vscale x 2 x i1>, <vscale x 2 x i64>, i64)

declare <vscale x 2 x double> @llvm.aarch64.sve.ldff1.gather.scalar.offset.nxv2f64.nxv2i64(<vscale x 2 x i1>, <vscale x 2 x i64>, i64)
