start:
	movq	$30, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, -16(%rbp)
	addq	$14, -16(%rbp)
	movq	$2, -24(%rbp)
	movq	-24(%rbp), %rax
	movq	%rax, -32(%rbp)
	negq	-32(%rbp)
	movq	-16(%rbp), %rax
	addq	-32(%rbp), %rax
	jmp	conclusion
	.globl main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$32, %rsp
	jmp start
conclusion:
	addq	$32, %rsp
	popq	%rbp
	retq
