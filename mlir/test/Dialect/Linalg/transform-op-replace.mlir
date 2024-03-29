// RUN: mlir-opt -transform-interpreter %s -allow-unregistered-dialect -verify-diagnostics --split-input-file | FileCheck %s

// CHECK: func.func @foo() {
// CHECK:   "dummy_op"() : () -> ()
// CHECK: }
// CHECK-NOT: func.func @bar
func.func @bar() {
  "another_op"() : () -> ()
}

module attributes {transform.with_named_sequence} {
  transform.named_sequence @__transform_main(%arg1: !transform.any_op {transform.readonly}) {
    %0 = transform.structured.match ops{["func.func"]} in %arg1 : (!transform.any_op) -> !transform.any_op
    transform.structured.replace %0 {
      builtin.module {
        func.func @foo() {
          "dummy_op"() : () -> ()
        }
      }
    } : (!transform.any_op) -> !transform.any_op
    transform.yield
  }
}

// -----

func.func @bar(%arg0: i1) {
  "another_op"(%arg0) : (i1) -> ()
}

module attributes {transform.with_named_sequence} {
  transform.named_sequence @__transform_main(%arg1: !transform.any_op {transform.readonly}) {
    %0 = transform.structured.match ops{["another_op"]} in %arg1 : (!transform.any_op) -> !transform.any_op
    // expected-error @+1 {{expected target without operands}}
    transform.structured.replace %0 {
      "dummy_op"() : () -> ()
    } : (!transform.any_op) -> !transform.any_op
    transform.yield
  }
}

// -----

func.func @bar() {
  "another_op"() : () -> ()
}

module attributes {transform.with_named_sequence} {
  transform.named_sequence @__transform_main(%arg1: !transform.any_op {transform.readonly}) {
    %0 = transform.structured.match ops{["another_op"]} in %arg1 : (!transform.any_op) -> !transform.any_op
    transform.structured.replace %0 {
    ^bb0(%a: i1):
      // expected-error @+1 {{expected replacement without operands}}
      "dummy_op"(%a) : (i1) -> ()
    } : (!transform.any_op) -> !transform.any_op
    transform.yield
  }
}
