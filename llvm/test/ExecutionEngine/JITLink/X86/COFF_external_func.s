# REQUIRES: asserts
# RUN: llvm-mc -filetype=obj -triple=x86_64-windows-msvc %s -o %t
# RUN: llvm-jitlink -abs func=0xcafef00d --debug-only=jitlink -noexec %t 2>&1 | FileCheck %s
#
# Check an external symbol to a functon is created.
#
# CHECK: Creating graph symbols...
# CHECK:   7: Creating external graph symbol for COFF symbol "func" in (external) (index: 0)

	.text

	.def	main;
	.scl	2;
	.type	32;
	.endef
	.globl	main
	.p2align	4, 0x90
main:
	callq	func
	retq
