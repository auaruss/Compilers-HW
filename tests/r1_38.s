start:
	movq	$10, %rax
	addq	$32, %rax
	jmp	conclusion
	.globl main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$0, %rsp
	jmp start
conclusion:
	addq	$0, %rsp
	popq	%rbp
	retq
