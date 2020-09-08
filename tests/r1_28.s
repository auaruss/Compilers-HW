start:
	movq	$22, -24(%rbp)
	movq	-24(%rbp), %rax
	movq	%rax, -8(%rbp)
	movq	$20, -16(%rbp)
	movq	-8(%rbp), %rax
	addq	-16(%rbp), %rax
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
