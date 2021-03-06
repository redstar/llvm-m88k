; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -passes='default<O3>' -S < %s  | FileCheck %s --check-prefixes=ALL,O3
; RUN: opt -passes='default<O2>' -S < %s  | FileCheck %s --check-prefixes=ALL,O2
; RUN: opt -passes='default<O1>' -S < %s  | FileCheck %s --check-prefixes=ALL,O1

; All these tests should optimize to a single comparison
; of the original argument with null. There should be no loops.

%struct.node = type { %struct.node*, i32 }

define dso_local zeroext i1 @is_not_empty_variant1(%struct.node* %p) {
; ALL-LABEL: @is_not_empty_variant1(
; ALL-NEXT:  entry:
; ALL-NEXT:    [[TOBOOL_NOT3_I:%.*]] = icmp ne %struct.node* [[P:%.*]], null
; ALL-NEXT:    ret i1 [[TOBOOL_NOT3_I]]
;
entry:
  %p.addr = alloca %struct.node*, align 8
  store %struct.node* %p, %struct.node** %p.addr, align 8
  %0 = load %struct.node*, %struct.node** %p.addr, align 8
  %call = call i32 @count_nodes_variant1(%struct.node* %0)
  %cmp = icmp sgt i32 %call, 0
  ret i1 %cmp
}

define internal i32 @count_nodes_variant1(%struct.node* %p) {
entry:
  %p.addr = alloca %struct.node*, align 8
  %size = alloca i32, align 4
  store %struct.node* %p, %struct.node** %p.addr, align 8
  %0 = bitcast i32* %size to i8*
  store i32 0, i32* %size, align 4
  br label %while.cond

while.cond:
  %1 = load %struct.node*, %struct.node** %p.addr, align 8
  %tobool = icmp ne %struct.node* %1, null
  br i1 %tobool, label %while.body, label %while.end

while.body:
  %2 = load %struct.node*, %struct.node** %p.addr, align 8
  %next = getelementptr inbounds %struct.node, %struct.node* %2, i32 0, i32 0
  %3 = load %struct.node*, %struct.node** %next, align 8
  store %struct.node* %3, %struct.node** %p.addr, align 8
  %4 = load i32, i32* %size, align 4
  %inc = add nsw i32 %4, 1
  store i32 %inc, i32* %size, align 4
  br label %while.cond, !llvm.loop !0

while.end:
  %5 = load i32, i32* %size, align 4
  %6 = bitcast i32* %size to i8*
  ret i32 %5
}

define dso_local zeroext i1 @is_not_empty_variant2(%struct.node* %p) {
; ALL-LABEL: @is_not_empty_variant2(
; ALL-NEXT:  entry:
; ALL-NEXT:    [[TOBOOL_NOT4_I:%.*]] = icmp ne %struct.node* [[P:%.*]], null
; ALL-NEXT:    ret i1 [[TOBOOL_NOT4_I]]
;
entry:
  %p.addr = alloca %struct.node*, align 8
  store %struct.node* %p, %struct.node** %p.addr, align 8
  %0 = load %struct.node*, %struct.node** %p.addr, align 8
  %call = call i64 @count_nodes_variant2(%struct.node* %0)
  %cmp = icmp ugt i64 %call, 0
  ret i1 %cmp
}

define internal i64 @count_nodes_variant2(%struct.node* %p) {
entry:
  %p.addr = alloca %struct.node*, align 8
  %size = alloca i64, align 8
  store %struct.node* %p, %struct.node** %p.addr, align 8
  %0 = bitcast i64* %size to i8*
  store i64 0, i64* %size, align 8
  br label %while.cond

while.cond:
  %1 = load %struct.node*, %struct.node** %p.addr, align 8
  %tobool = icmp ne %struct.node* %1, null
  br i1 %tobool, label %while.body, label %while.end

while.body:
  %2 = load %struct.node*, %struct.node** %p.addr, align 8
  %next = getelementptr inbounds %struct.node, %struct.node* %2, i32 0, i32 0
  %3 = load %struct.node*, %struct.node** %next, align 8
  store %struct.node* %3, %struct.node** %p.addr, align 8
  %4 = load i64, i64* %size, align 8
  %inc = add i64 %4, 1
  store i64 %inc, i64* %size, align 8
  %5 = load i64, i64* %size, align 8
  %cmp = icmp ne i64 %5, 0
  call void @_ZL6assumeb(i1 zeroext %cmp)
  br label %while.cond, !llvm.loop !2

while.end:
  %6 = load i64, i64* %size, align 8
  %7 = bitcast i64* %size to i8*
  ret i64 %6
}

define dso_local zeroext i1 @is_not_empty_variant3(%struct.node* %p) {
; O3-LABEL: @is_not_empty_variant3(
; O3-NEXT:  entry:
; O3-NEXT:    [[TOBOOL_NOT4_I:%.*]] = icmp ne %struct.node* [[P:%.*]], null
; O3-NEXT:    ret i1 [[TOBOOL_NOT4_I]]
;
; O2-LABEL: @is_not_empty_variant3(
; O2-NEXT:  entry:
; O2-NEXT:    [[TOBOOL_NOT4_I:%.*]] = icmp ne %struct.node* [[P:%.*]], null
; O2-NEXT:    ret i1 [[TOBOOL_NOT4_I]]
;
; O1-LABEL: @is_not_empty_variant3(
; O1-NEXT:  entry:
; O1-NEXT:    [[TOBOOL_NOT4_I:%.*]] = icmp eq %struct.node* [[P:%.*]], null
; O1-NEXT:    br i1 [[TOBOOL_NOT4_I]], label [[COUNT_NODES_VARIANT3_EXIT:%.*]], label [[WHILE_BODY_I:%.*]]
; O1:       while.body.i:
; O1-NEXT:    [[SIZE_06_I:%.*]] = phi i64 [ [[INC_I:%.*]], [[WHILE_BODY_I]] ], [ 0, [[ENTRY:%.*]] ]
; O1-NEXT:    [[P_ADDR_05_I:%.*]] = phi %struct.node* [ [[TMP0:%.*]], [[WHILE_BODY_I]] ], [ [[P]], [[ENTRY]] ]
; O1-NEXT:    [[CMP_I:%.*]] = icmp ne i64 [[SIZE_06_I]], -1
; O1-NEXT:    call void @llvm.assume(i1 [[CMP_I]])
; O1-NEXT:    [[NEXT_I:%.*]] = getelementptr inbounds [[STRUCT_NODE:%.*]], %struct.node* [[P_ADDR_05_I]], i64 0, i32 0
; O1-NEXT:    [[TMP0]] = load %struct.node*, %struct.node** [[NEXT_I]], align 8
; O1-NEXT:    [[INC_I]] = add i64 [[SIZE_06_I]], 1
; O1-NEXT:    [[TOBOOL_NOT_I:%.*]] = icmp eq %struct.node* [[TMP0]], null
; O1-NEXT:    br i1 [[TOBOOL_NOT_I]], label [[COUNT_NODES_VARIANT3_EXIT_LOOPEXIT:%.*]], label [[WHILE_BODY_I]], !llvm.loop [[LOOP0:![0-9]+]]
; O1:       count_nodes_variant3.exit.loopexit:
; O1-NEXT:    [[PHI_CMP:%.*]] = icmp ne i64 [[INC_I]], 0
; O1-NEXT:    br label [[COUNT_NODES_VARIANT3_EXIT]]
; O1:       count_nodes_variant3.exit:
; O1-NEXT:    [[SIZE_0_LCSSA_I:%.*]] = phi i1 [ false, [[ENTRY]] ], [ [[PHI_CMP]], [[COUNT_NODES_VARIANT3_EXIT_LOOPEXIT]] ]
; O1-NEXT:    ret i1 [[SIZE_0_LCSSA_I]]
;
entry:
  %p.addr = alloca %struct.node*, align 8
  store %struct.node* %p, %struct.node** %p.addr, align 8
  %0 = load %struct.node*, %struct.node** %p.addr, align 8
  %call = call i64 @count_nodes_variant3(%struct.node* %0)
  %cmp = icmp ugt i64 %call, 0
  ret i1 %cmp
}

define internal i64 @count_nodes_variant3(%struct.node* %p) {
entry:
  %p.addr = alloca %struct.node*, align 8
  %size = alloca i64, align 8
  store %struct.node* %p, %struct.node** %p.addr, align 8
  %0 = bitcast i64* %size to i8*
  store i64 0, i64* %size, align 8
  br label %while.cond

while.cond:
  %1 = load %struct.node*, %struct.node** %p.addr, align 8
  %tobool = icmp ne %struct.node* %1, null
  br i1 %tobool, label %while.body, label %while.end

while.body:
  %2 = load i64, i64* %size, align 8
  %cmp = icmp ne i64 %2, -1
  call void @_ZL6assumeb(i1 zeroext %cmp)
  %3 = load %struct.node*, %struct.node** %p.addr, align 8
  %next = getelementptr inbounds %struct.node, %struct.node* %3, i32 0, i32 0
  %4 = load %struct.node*, %struct.node** %next, align 8
  store %struct.node* %4, %struct.node** %p.addr, align 8
  %5 = load i64, i64* %size, align 8
  %inc = add i64 %5, 1
  store i64 %inc, i64* %size, align 8
  br label %while.cond, !llvm.loop !3

while.end:
  %6 = load i64, i64* %size, align 8
  %7 = bitcast i64* %size to i8*
  ret i64 %6
}

define internal void @_ZL6assumeb(i1 zeroext %expression) {
entry:
  %expression.addr = alloca i8, align 1
  %frombool = zext i1 %expression to i8
  store i8 %frombool, i8* %expression.addr, align 1
  %0 = load i8, i8* %expression.addr, align 1
  %tobool = trunc i8 %0 to i1
  call void @llvm.assume(i1 %tobool)
  ret void
}

declare void @llvm.assume(i1 noundef)

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
!2 = distinct !{!2, !1}
!3 = distinct !{!3, !1}
