
; RUN: opt < %s -passes=pgo-instr-gen -S | FileCheck %s --check-prefix=GEN
; RUN: opt < %s -passes=pgo-instr-gen,instrprof -S | FileCheck %s --check-prefix=LOWER

; This test is to verify that PGO runtime library calls get created with the
; appropriate operand bundle funclet information when an indirect call
; was marked with as belonging to a particular funclet.

; Test case based on this source:
;  extern void may_throw(int);
;
;  class base {
;  public:
;    base() : x(0) {};
;    int get_x() const { return x; }
;    virtual void update() { x++; }
;    int x;
;  };
;
;  class derived : public base {
;  public:
;    derived() {}
;    virtual void update() { x--; }
;  };
;
;  void run(base* b, int count) {
;    try {
;      may_throw(count);
;    }
;    catch (...) {
;      // Virtual function call in exception handler for value profiling.
;      b->update();
;    }
;  }

%class.base = type { ptr, i32 }
define dso_local void @"?run@@YAXPEAVbase@@H@Z"(ptr %b, i32 %count) personality ptr @__CxxFrameHandler3 {
entry:
  invoke void @"?may_throw@@YAXH@Z"(i32 %count)
          to label %try.cont unwind label %catch.dispatch

catch.dispatch:                                   ; preds = %entry
  %tmp = catchswitch within none [label %catch] unwind to caller

catch:                                            ; preds = %catch.dispatch
  %tmp1 = catchpad within %tmp [ptr null, i32 64, ptr null]
  %vtable = load ptr, ptr %b, align 8
  %tmp3 = load ptr, ptr %vtable, align 8
  call void %tmp3(ptr %b) [ "funclet"(token %tmp1) ]
  catchret from %tmp1 to label %try.cont

try.cont:                                         ; preds = %catch, %entry
  ret void
}

; GEN: catch:
; GEN: call void @llvm.instrprof.value.profile(
; GEN-SAME: [ "funclet"(token %tmp1) ]

; LOWER: catch:
; LOWER: call void @__llvm_profile_instrument_target(
; LOWER-SAME: [ "funclet"(token %tmp1) ]

declare dso_local void @"?may_throw@@YAXH@Z"(i32)
declare dso_local i32 @__CxxFrameHandler3(...)
