; RUN: opt < %s -passes=pgo-icall-prom -S -icp-total-percent-threshold=10 | FileCheck %s

; PR42413: Previously the call promotion code did not correctly update the byval
; attribute. Check that it does. This situation can come up in LTO scenarios
; where struct types end up not matching.

target triple = "i686-unknown-linux-gnu"

%struct.Foo.1 = type { i32 }
%struct.Foo.2 = type { i32 }

@foo = common global ptr null, align 8

define i32 @func4(ptr byval(%struct.Foo.1) %p) {
entry:
  %v = load i32, ptr %p
  ret i32 %v
}

define i32 @func5(ptr byval(%struct.Foo.1) %p) {
entry:
  %v = load i32, ptr %p
  ret i32 %v
}

define i32 @bar(ptr %f2) {
entry:
  %tmp = load ptr, ptr @foo, align 8
  %call = call i32 %tmp(ptr byval(%struct.Foo.2) %f2), !prof !1
  ret i32 %call
}

!1 = !{!"VP", i32 0, i64 3000, i64 7651369219802541373, i64 1000, i64 3667884930908592509, i64 1000}


; CHECK: define i32 @bar(ptr %f2)
;     Use byval(%struct.Foo.2).
; CHECK: call i32 @func4(ptr byval(%struct.Foo.2) %f2)
;     Same but when callee doesn't have explicit byval type.
; CHECK: call i32 @func5(ptr byval(%struct.Foo.2) %f2)
;     Original call stays the same.
; CHECK: call i32 %tmp(ptr byval(%struct.Foo.2) %f2)
