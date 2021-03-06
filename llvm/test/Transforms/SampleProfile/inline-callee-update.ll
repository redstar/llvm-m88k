; Make sure Import GUID list for ThinLTO properly maintained while update function's entry count for inlining

; RUN: opt < %s -passes='thinlto-pre-link<O2>' -pgo-kind=pgo-sample-use-pipeline -sample-profile-file=%S/Inputs/inline-callee-update.prof -S | FileCheck %s

@y = global ptr null, align 8
@z = global ptr null, align 8

; CHECK: define ptr @sample_loader_inlinee() {{.*}} !prof ![[ENTRY:[0-9]+]]
define ptr @sample_loader_inlinee() #0 !dbg !3 {
bb:
  %tmp = call ptr @direct_leaf_func(ptr null), !dbg !4
  %cmp = icmp ne ptr %tmp, null
  br i1 %cmp, label %then, label %else

then:                                             ; preds = %bb
  %tmp1 = load ptr, ptr @z, align 8, !dbg !5
  %tmp2 = call ptr %tmp1(), !dbg !5
  ret ptr %tmp2

else:                                             ; preds = %bb
  ret ptr null
}

; CHECK: define ptr @cgscc_inlinee() {{.*}} !prof ![[ENTRY:[0-9]+]]
define ptr @cgscc_inlinee() #0 !dbg !6 {
bb:
  %tmp = call ptr @direct_leaf_func(ptr null), !dbg !7
  %cmp = icmp ne ptr %tmp, null
  br i1 %cmp, label %then, label %else

then:                                             ; preds = %bb
  %tmp1 = load ptr, ptr @y, align 8, !dbg !8
  %tmp2 = call ptr %tmp1(), !dbg !8
  ret ptr %tmp2

else:                                             ; preds = %bb
  ret ptr null
}

define ptr @test_sample_loader_inline(ptr %arg) #0 !dbg !9 {
bb:
  %tmp = call ptr @sample_loader_inlinee(), !dbg !10
  ret ptr %tmp
}

define ptr @test_cgscc_inline(ptr %arg) #0 !dbg !11 {
bb:
  %tmp = call ptr @cgscc_inlinee(), !dbg !12
  ret ptr %tmp
}

declare ptr @direct_leaf_func(ptr)

attributes #0 = {"use-sample-profile"}

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2}

!0 = distinct !DICompileUnit(language: DW_LANG_C_plus_plus, file: !1, isOptimized: false, runtimeVersion: 0, emissionKind: NoDebug)
!1 = !DIFile(filename: "test.cc", directory: "/")
!2 = !{i32 2, !"Debug Info Version", i32 3}
!3 = distinct !DISubprogram(name: "sample_loader_inlinee", scope: !1, file: !1, line: 11, spFlags: DISPFlagDefinition, unit: !0)
!4 = !DILocation(line: 12, scope: !3)
!5 = !DILocation(line: 13, scope: !3)
!6 = distinct !DISubprogram(name: "cgscc_inlinee", scope: !1, file: !1, line: 31, spFlags: DISPFlagDefinition, unit: !0)
!7 = !DILocation(line: 32, scope: !6)
!8 = !DILocation(line: 33, scope: !6)
!9 = distinct !DISubprogram(name: "test_sample_loader_inline", scope: !1, file: !1, line: 3, spFlags: DISPFlagDefinition, unit: !0)
!10 = !DILocation(line: 4, scope: !9)
!11 = distinct !DISubprogram(name: "test_cgscc_inline", scope: !1, file: !1, line: 20, spFlags: DISPFlagDefinition, unit: !0)
!12 = !DILocation(line: 21, scope: !11)

; Make sure the ImportGUID stays with entry count metadata for ThinLTO-PreLink
; CHECK: ![[ENTRY]] = !{!"function_entry_count", i64 1, i64 -9171813444624716006}
