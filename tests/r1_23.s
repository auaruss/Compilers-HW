start:
	movq	$32, %rax
	addq	$10, %rax
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