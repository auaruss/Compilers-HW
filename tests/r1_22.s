start:
	movq	$42, %rax
	jmp	conclusion
	.globl _main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$0, %rsp
	jmp start
conclusion:
	addq	$0, %rsp
	popq	%rbp
	retq
