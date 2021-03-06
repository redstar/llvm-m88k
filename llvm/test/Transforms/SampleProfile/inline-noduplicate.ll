; RUN: opt < %s -passes=sample-profile -sample-profile-file=%S/Inputs/inline.prof -S | FileCheck %s

; Similar to inline.ll test, but the callee contains a noduplicate instruction.

@.str = private unnamed_addr constant [11 x i8] c"sum is %d\0A\00", align 1

declare void @foo()
declare void @bar()

; Function Attrs: nounwind uwtable
define i32 @_Z3sumii(i32 %x, i32 %y) #0 !dbg !4 {
entry:
  call void @foo() noduplicate
  ; Just to inflate the cost
  call void @bar() "call-inline-cost"="1000"
  %x.addr = alloca i32, align 4
  %y.addr = alloca i32, align 4
  store i32 %x, ptr %x.addr, align 4
  store i32 %y, ptr %y.addr, align 4
  %0 = load i32, ptr %x.addr, align 4, !dbg !11
  %1 = load i32, ptr %y.addr, align 4, !dbg !11
  %add = add nsw i32 %0, %1, !dbg !11
  ret i32 %add, !dbg !11
}

; Function Attrs: uwtable
define i32 @main() #0 !dbg !7 {
entry:
  %retval = alloca i32, align 4
  %s = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 0, ptr %retval
  store i32 0, ptr %i, align 4, !dbg !12
  br label %while.cond, !dbg !13

while.cond:                                       ; preds = %if.end, %entry
  %0 = load i32, ptr %i, align 4, !dbg !14
  %inc = add nsw i32 %0, 1, !dbg !14
  store i32 %inc, ptr %i, align 4, !dbg !14
  %cmp = icmp slt i32 %0, 400000000, !dbg !14
  br i1 %cmp, label %while.body, label %while.end, !dbg !14

while.body:                                       ; preds = %while.cond
  %1 = load i32, ptr %i, align 4, !dbg !16
  %cmp1 = icmp ne i32 %1, 100, !dbg !16
  br i1 %cmp1, label %if.then, label %if.else, !dbg !16


if.then:                                          ; preds = %while.body
  %2 = load i32, ptr %i, align 4, !dbg !18
  %3 = load i32, ptr %s, align 4, !dbg !18
  %call = call i32 @_Z3sumii(i32 %2, i32 %3), !dbg !18
; _Z3sumii should not be inlined because of the noduplicate call to foo.
; CHECK: call i32 @_Z3sumii
; CHECK-NOT: call void @foo
  store i32 %call, ptr %s, align 4, !dbg !18
  br label %if.end, !dbg !18

if.else:                                          ; preds = %while.body
  store i32 30, ptr %s, align 4, !dbg !20
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  br label %while.cond, !dbg !22

while.end:                                        ; preds = %while.cond
  %4 = load i32, ptr %s, align 4, !dbg !24
  %call2 = call i32 (ptr, ...) @printf(ptr @.str, i32 %4), !dbg !24
  ret i32 0, !dbg !25
}

declare i32 @printf(ptr, ...) #2

attributes #0 = { "use-sample-profile" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!8, !9}
!llvm.ident = !{!10}

!0 = distinct !DICompileUnit(language: DW_LANG_C_plus_plus, producer: "clang version 3.5 ", isOptimized: false, emissionKind: NoDebug, file: !1, enums: !2, retainedTypes: !2, globals: !2, imports: !2)
!1 = !DIFile(filename: "calls.cc", directory: ".")
!2 = !{}
!4 = distinct !DISubprogram(name: "sum", line: 3, isLocal: false, isDefinition: true, virtualIndex: 6, flags: DIFlagPrototyped, isOptimized: false, unit: !0, scopeLine: 3, file: !1, scope: !5, type: !6, retainedNodes: !2)
!5 = !DIFile(filename: "calls.cc", directory: ".")
!6 = !DISubroutineType(types: !2)
!7 = distinct !DISubprogram(name: "main", line: 7, isLocal: false, isDefinition: true, virtualIndex: 6, flags: DIFlagPrototyped, isOptimized: false, unit: !0, scopeLine: 7, file: !1, scope: !5, type: !6, retainedNodes: !2)
!8 = !{i32 2, !"Dwarf Version", i32 4}
!9 = !{i32 1, !"Debug Info Version", i32 3}
!10 = !{!"clang version 3.5 "}
!11 = !DILocation(line: 4, scope: !4)
!12 = !DILocation(line: 8, scope: !7)
!13 = !DILocation(line: 9, scope: !7)
!14 = !DILocation(line: 9, scope: !15)
!15 = !DILexicalBlockFile(discriminator: 2, file: !1, scope: !7)
!16 = !DILocation(line: 10, scope: !17)
!17 = distinct !DILexicalBlock(line: 10, column: 0, file: !1, scope: !7)
!18 = !DILocation(line: 10, scope: !19)
!19 = !DILexicalBlockFile(discriminator: 2, file: !1, scope: !17)
!20 = !DILocation(line: 10, scope: !21)
!21 = !DILexicalBlockFile(discriminator: 4, file: !1, scope: !17)
!22 = !DILocation(line: 10, scope: !23)
!23 = !DILexicalBlockFile(discriminator: 6, file: !1, scope: !17)
!24 = !DILocation(line: 11, scope: !7)
!25 = !DILocation(line: 12, scope: !7)
