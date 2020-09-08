start:
	movq	$1, -8(%rbp)
	movq	$46, -16(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, -24(%rbp)
	addq	$7, -24(%rbp)
	movq	$4, -32(%rbp)
	movq	-24(%rbp), %rax
	addq	%rax, -32(%rbp)
	movq	-24(%rbp), %rax
	movq	%rax, -40(%rbp)
	movq	-16(%rbp), %rax
	addq	%rax, -40(%rbp)
	movq	-32(%rbp), %rax
	movq	%rax, -48(%rbp)
	negq	-48(%rbp)
	movq	-40(%rbp), %rax
	addq	-48(%rbp), %rax
	jmp	conclusion
	.globl _main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$48, %rsp
	jmp start
conclusion:
	addq	$48, %rsp
	popq	%rbp
	retq
