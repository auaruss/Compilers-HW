start:
	movq	$7, -8(%rbp)
	addq	$3, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, -16(%rbp)
	movq	-16(%rbp), %rax
	movq	%rax, -24(%rbp)
	negq	-24(%rbp)
	movq	$52, %rax
	addq	-24(%rbp), %rax
	jmp	conclusion
	.globl _main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$24, %rsp
	jmp start
conclusion:
	addq	$24, %rsp
	popq	%rbp
	retq
