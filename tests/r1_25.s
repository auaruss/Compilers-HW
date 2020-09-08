start:
	movq	$10, -8(%rbp)
	addq	$11, -8(%rbp)
	movq	$4, -16(%rbp)
	negq	-16(%rbp)
	movq	-16(%rbp), %rax
	movq	%rax, -24(%rbp)
	movq	$25, -32(%rbp)
	movq	-24(%rbp), %rax
	addq	%rax, -32(%rbp)
	movq	-8(%rbp), %rax
	addq	-32(%rbp), %rax
	jmp	conclusion
	.globl _main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$32, %rsp
	jmp start
conclusion:
	addq	$32, %rsp
	popq	%rbp
	retq
