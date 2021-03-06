; RUN: llc < %s -mtriple=i686-pc-linux-gnu -mattr=+sse2
; PR2076

define void @h264_h_loop_filter_luma_mmx2(ptr %pix, i32 %stride, i32 %alpha, i32 %beta, ptr %tc0) nounwind  {
entry:
	%tmp164 = getelementptr [16 x i32], ptr null, i32 0, i32 11		; <ptr> [#uses=1]
	%tmp169 = getelementptr [16 x i32], ptr null, i32 0, i32 13		; <ptr> [#uses=1]
	%tmp174 = getelementptr [16 x i32], ptr null, i32 0, i32 15		; <ptr> [#uses=1]
	%tmp154.sum317 = add i32 0, %stride		; <i32> [#uses=1]
	%tmp154.sum315 = mul i32 %stride, 6		; <i32> [#uses=1]
	%tmp154.sum = mul i32 %stride, 7		; <i32> [#uses=1]
	%pix_addr.0327.rec = mul i32 0, 0		; <i32> [#uses=4]
	br i1 false, label %bb292, label %bb32

bb32:		; preds = %entry
	%pix_addr.0327.sum340 = add i32 %pix_addr.0327.rec, 0		; <i32> [#uses=1]
	%tmp154 = getelementptr i8, ptr %pix, i32 %pix_addr.0327.sum340		; <ptr> [#uses=1]
	%pix_addr.0327.sum339 = add i32 %pix_addr.0327.rec, %tmp154.sum317		; <i32> [#uses=1]
	%tmp181 = getelementptr i8, ptr %pix, i32 %pix_addr.0327.sum339		; <ptr> [#uses=1]
	%pix_addr.0327.sum338 = add i32 %pix_addr.0327.rec, %tmp154.sum315		; <i32> [#uses=1]
	%tmp186 = getelementptr i8, ptr %pix, i32 %pix_addr.0327.sum338		; <ptr> [#uses=1]
	%pix_addr.0327.sum337 = add i32 %pix_addr.0327.rec, %tmp154.sum		; <i32> [#uses=1]
	%tmp191 = getelementptr i8, ptr %pix, i32 %pix_addr.0327.sum337		; <ptr> [#uses=1]
	call void asm sideeffect "movd  $4, %mm0                \0A\09movd  $5, %mm1                \0A\09movd  $6, %mm2                \0A\09movd  $7, %mm3                \0A\09punpcklbw %mm1, %mm0         \0A\09punpcklbw %mm3, %mm2         \0A\09movq %mm0, %mm1              \0A\09punpcklwd %mm2, %mm0         \0A\09punpckhwd %mm2, %mm1         \0A\09movd  %mm0, $0                \0A\09punpckhdq %mm0, %mm0         \0A\09movd  %mm0, $1                \0A\09movd  %mm1, $2                \0A\09punpckhdq %mm1, %mm1         \0A\09movd  %mm1, $3                \0A\09", "=*m,=*m,=*m,=*m,*m,*m,*m,*m,~{dirflag},~{fpsr},~{flags}"( ptr elementtype( i32) null, ptr elementtype(i32) %tmp164, ptr elementtype(i32) %tmp169, ptr elementtype(i32) %tmp174, ptr elementtype(i32) %tmp154, ptr elementtype(i32) %tmp181, ptr elementtype(i32) %tmp186, ptr elementtype(i32) %tmp191 ) nounwind 
	unreachable

bb292:		; preds = %entry
	ret void
}
