// RUN: mlir-opt -split-input-file -verify-diagnostics %s | FileCheck %s

//===----------------------------------------------------------------------===//
// spv.CL.exp
//===----------------------------------------------------------------------===//

func.func @exp(%arg0 : f32) -> () {
  // CHECK: spv.CL.exp {{%.*}} : f32
  %2 = spv.CL.exp %arg0 : f32
  return
}

func.func @expvec(%arg0 : vector<3xf16>) -> () {
  // CHECK: spv.CL.exp {{%.*}} : vector<3xf16>
  %2 = spv.CL.exp %arg0 : vector<3xf16>
  return
}

// -----

func.func @exp(%arg0 : i32) -> () {
  // expected-error @+1 {{op operand #0 must be 16/32/64-bit float or vector of 16/32/64-bit float values}}
  %2 = spv.CL.exp %arg0 : i32
  return
}

// -----

func.func @exp(%arg0 : vector<5xf32>) -> () {
  // expected-error @+1 {{op operand #0 must be 16/32/64-bit float or vector of 16/32/64-bit float values of length 2/3/4}}
  %2 = spv.CL.exp %arg0 : vector<5xf32>
  return
}

// -----

func.func @exp(%arg0 : f32, %arg1 : f32) -> () {
  // expected-error @+1 {{expected ':'}}
  %2 = spv.CL.exp %arg0, %arg1 : i32
  return
}

// -----

func.func @exp(%arg0 : i32) -> () {
  // expected-error @+1 {{expected non-function type}}
  %2 = spv.CL.exp %arg0 :
  return
}

// -----

//===----------------------------------------------------------------------===//
// spv.CL.fabs
//===----------------------------------------------------------------------===//

func.func @fabs(%arg0 : f32) -> () {
  // CHECK: spv.CL.fabs {{%.*}} : f32
  %2 = spv.CL.fabs %arg0 : f32
  return
}

func.func @fabsvec(%arg0 : vector<3xf16>) -> () {
  // CHECK: spv.CL.fabs {{%.*}} : vector<3xf16>
  %2 = spv.CL.fabs %arg0 : vector<3xf16>
  return
}

func.func @fabsf64(%arg0 : f64) -> () {
  // CHECK: spv.CL.fabs {{%.*}} : f64
  %2 = spv.CL.fabs %arg0 : f64
  return
}

// -----

func.func @fabs(%arg0 : i32) -> () {
  // expected-error @+1 {{op operand #0 must be 16/32/64-bit float or vector of 16/32/64-bit float values}}
  %2 = spv.CL.fabs %arg0 : i32
  return
}

// -----

func.func @fabs(%arg0 : vector<5xf32>) -> () {
  // expected-error @+1 {{op operand #0 must be 16/32/64-bit float or vector of 16/32/64-bit float values of length 2/3/4}}
  %2 = spv.CL.fabs %arg0 : vector<5xf32>
  return
}

// -----

func.func @fabs(%arg0 : f32, %arg1 : f32) -> () {
  // expected-error @+1 {{expected ':'}}
  %2 = spv.CL.fabs %arg0, %arg1 : i32
  return
}

// -----

func.func @fabs(%arg0 : i32) -> () {
  // expected-error @+1 {{expected non-function type}}
  %2 = spv.CL.fabs %arg0 :
  return
}

// -----

//===----------------------------------------------------------------------===//
// spv.CL.s_abs
//===----------------------------------------------------------------------===//

func.func @sabs(%arg0 : i32) -> () {
  // CHECK: spv.CL.s_abs {{%.*}} : i32
  %2 = spv.CL.s_abs %arg0 : i32
  return
}

func.func @sabsvec(%arg0 : vector<3xi16>) -> () {
  // CHECK: spv.CL.s_abs {{%.*}} : vector<3xi16>
  %2 = spv.CL.s_abs %arg0 : vector<3xi16>
  return
}

func.func @sabsi64(%arg0 : i64) -> () {
  // CHECK: spv.CL.s_abs {{%.*}} : i64
  %2 = spv.CL.s_abs %arg0 : i64
  return
}

func.func @sabsi8(%arg0 : i8) -> () {
  // CHECK: spv.CL.s_abs {{%.*}} : i8
  %2 = spv.CL.s_abs %arg0 : i8
  return
}

// -----

func.func @sabs(%arg0 : f32) -> () {
  // expected-error @+1 {{op operand #0 must be 8/16/32/64-bit integer or vector of 8/16/32/64-bit integer values}}
  %2 = spv.CL.s_abs %arg0 : f32
  return
}

// -----

func.func @sabs(%arg0 : vector<5xi32>) -> () {
  // expected-error @+1 {{op operand #0 must be 8/16/32/64-bit integer or vector of 8/16/32/64-bit integer values of length 2/3/4}}
  %2 = spv.CL.s_abs %arg0 : vector<5xi32>
  return
}

// -----

func.func @sabs(%arg0 : i32, %arg1 : i32) -> () {
  // expected-error @+1 {{expected ':'}}
  %2 = spv.CL.s_abs %arg0, %arg1 : i32
  return
}

// -----

func.func @sabs(%arg0 : i32) -> () {
  // expected-error @+1 {{expected non-function type}}
  %2 = spv.CL.s_abs %arg0 :
  return
}

// -----

//===----------------------------------------------------------------------===//
// spv.CL.fma
//===----------------------------------------------------------------------===//

func.func @fma(%a : f32, %b : f32, %c : f32) -> () {
  // CHECK: spv.CL.fma {{%[^,]*}}, {{%[^,]*}}, {{%[^,]*}} : f32
  %2 = spv.CL.fma %a, %b, %c : f32
  return
}

// -----

func.func @fma(%a : vector<3xf32>, %b : vector<3xf32>, %c : vector<3xf32>) -> () {
  // CHECK: spv.CL.fma {{%[^,]*}}, {{%[^,]*}}, {{%[^,]*}} : vector<3xf32>
  %2 = spv.CL.fma %a, %b, %c : vector<3xf32>
  return
}
