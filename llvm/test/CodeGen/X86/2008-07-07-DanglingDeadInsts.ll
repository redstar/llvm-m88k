; RUN: llc < %s -mtriple=i386-apple-darwin9

	%struct.ogg_stream_state = type { ptr, i32, i32, i32, ptr, ptr, i32, i32, i32, i32, [282 x i8], i32, i32, i32, i32, i32, i64, i64 }
	%struct.res_state = type { i32, i32, i32, i32, ptr, ptr, i32, i32 }
	%struct.vorbis_comment = type { ptr, ptr, i32, ptr }

declare i32 @strlen(ptr) nounwind readonly 

define i32 @res_init(ptr %state, i32 %channels, i32 %outfreq, i32 %infreq, i32 %op1, ...) nounwind  {
entry:
	br i1 false, label %bb95, label %bb

bb:		; preds = %entry
	br i1 false, label %bb95, label %bb24

bb24:		; preds = %bb
	br i1 false, label %bb40.preheader, label %bb26

bb26:		; preds = %bb24
	ret i32 -1

bb40.preheader:		; preds = %bb24
	br i1 false, label %bb39, label %bb49.outer

bb39:		; preds = %bb39, %bb40.preheader
	shl i32 0, 1		; <i32>:0 [#uses=0]
	br i1 false, label %bb39, label %bb49.outer

bb49.outer:		; preds = %bb39, %bb40.preheader
	getelementptr %struct.res_state, ptr %state, i32 0, i32 3		; <ptr>:1 [#uses=0]
	getelementptr %struct.res_state, ptr %state, i32 0, i32 7		; <ptr>:2 [#uses=0]
	%base10.1 = select i1 false, ptr null, ptr null		; <ptr> [#uses=1]
	br label %bb74

bb69:		; preds = %bb74
	br label %bb71

bb71:		; preds = %bb74, %bb69
	store float 0.000000e+00, ptr null, align 4
	add i32 0, 1		; <i32>:3 [#uses=1]
	%indvar.next137 = add i32 %indvar136, 1		; <i32> [#uses=1]
	br i1 false, label %bb74, label %bb73

bb73:		; preds = %bb71
	%.rec = add i32 %base10.2.ph.rec, 1		; <i32> [#uses=2]
	getelementptr float, ptr %base10.1, i32 %.rec		; <ptr>:4 [#uses=1]
	br label %bb74

bb74:		; preds = %bb73, %bb71, %bb49.outer
	%N13.1.ph = phi i32 [ 0, %bb49.outer ], [ 0, %bb73 ], [ %N13.1.ph, %bb71 ]		; <i32> [#uses=1]
	%dest12.2.ph = phi ptr [ null, %bb49.outer ], [ %4, %bb73 ], [ %dest12.2.ph, %bb71 ]		; <ptr> [#uses=1]
	%x8.0.ph = phi i32 [ 0, %bb49.outer ], [ %3, %bb73 ], [ %x8.0.ph, %bb71 ]		; <i32> [#uses=1]
	%base10.2.ph.rec = phi i32 [ 0, %bb49.outer ], [ %.rec, %bb73 ], [ %base10.2.ph.rec, %bb71 ]		; <i32> [#uses=2]
	%indvar136 = phi i32 [ %indvar.next137, %bb71 ], [ 0, %bb73 ], [ 0, %bb49.outer ]		; <i32> [#uses=1]
	br i1 false, label %bb71, label %bb69

bb95:		; preds = %bb, %entry
	ret i32 -1
}

define i32 @read_resampled(ptr %d, ptr %buffer, i32 %samples) nounwind  {
entry:
	br i1 false, label %bb17.preheader, label %bb30

bb17.preheader:		; preds = %entry
	load i32, ptr null, align 4		; <i32>:0 [#uses=0]
	br label %bb16

bb16:		; preds = %bb16, %bb17.preheader
	%i1.036 = phi i32 [ 0, %bb17.preheader ], [ %1, %bb16 ]		; <i32> [#uses=1]
	add i32 %i1.036, 1		; <i32>:1 [#uses=2]
	icmp ult i32 %1, 0		; <i1>:2 [#uses=0]
	br label %bb16

bb30:		; preds = %entry
	ret i32 0
}

define i32 @ogg_stream_reset_serialno(ptr %os, i32 %serialno) nounwind  {
entry:
	unreachable
}

define void @vorbis_lsp_to_curve(ptr %curve, ptr %map, i32 %n, i32 %ln, ptr %lsp, i32 %m, float %amp, float %ampoffset) nounwind  {
entry:
	unreachable
}

define i32 @vorbis_comment_query_count(ptr %vc, ptr %tag) nounwind  {
entry:
	%strlen = call i32 @strlen( ptr null )		; <i32> [#uses=1]
	%endptr = getelementptr i8, ptr null, i32 %strlen		; <ptr> [#uses=0]
	unreachable
}

define fastcc i32 @push(ptr %state, ptr %pool, ptr %poolfill, ptr %offset, ptr %dest, i32 %dststep, ptr %source, i32 %srcstep, i32 %srclen) nounwind  {
entry:
	unreachable
}
