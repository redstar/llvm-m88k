@X = external global i32

declare i32 @foo()

define void @bar() !dbg !4 {
	load i32, ptr @X, !dbg !10
	call i32 @foo(), !dbg !11
	ret void, !dbg !12
}

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.8.0 (trunk 251407) (llvm/trunk 251401)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2)
!1 = !DIFile(filename: "linkused.b.c", directory: ".")
!2 = !{}
!4 = distinct !DISubprogram(name: "bar", scope: !1, file: !1, line: 5, type: !5, isLocal: false, isDefinition: true, scopeLine: 5, isOptimized: true, unit: !0, retainedNodes: !2)
!5 = !DISubroutineType(types: !6)
!6 = !{null}
!7 = !{i32 2, !"Dwarf Version", i32 4}
!8 = !{i32 2, !"Debug Info Version", i32 3}
!9 = !{!"clang version 3.8.0 (trunk 251407) (llvm/trunk 251401)"}
!10 = !DILocation(line: 6, column: 7, scope: !4)
!11 = !DILocation(line: 6, column: 3, scope: !4)
!12 = !DILocation(line: 7, column: 1, scope: !4)
