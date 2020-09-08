start:
	movq	$42, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, -16(%rbp)
	movq	-16(%rbp), %rax
	jmp	conclusion
	.globl _main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$16, %rsp
	jmp start
conclusion:
	addq	$16, %rsp
	popq	%rbp
	retq
