// Test use-sample-profile attribute is present only when SampleFDO
// is enabled.
//
// RUN: %clang_cc1 -O2 \
// RUN:     -fprofile-sample-use=%S/Inputs/pgo-sample.prof %s -emit-llvm -o - \
// RUN:     2>&1 | FileCheck %s
// RUN: %clang_cc1 -O2 %s -emit-llvm -o - \
// RUN:     2>&1 | FileCheck %s --check-prefix=NOATTR

// CHECK: define{{.*}} @func{{.*}} #[[ATTRID:[0-9]+]]
// CHECK: attributes #[[ATTRID]] = {{.*}} "use-sample-profile"
// NOATTR: define{{.*}} @func{{.*}} #[[ATTRID:[0-9]+]]
// NOATTR-NOT: attributes #[[ATTRID]] = {{.*}} "use-sample-profile"

int func(int a) { return a; }
