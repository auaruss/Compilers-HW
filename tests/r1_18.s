start:
	movq	$99, -8(%rbp)
	movq	$22, -16(%rbp)
	movq	$42, -24(%rbp)
	movq	-24(%rbp), %rax
	jmp	conclusion
	.globl main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$24, %rsp
	jmp start
conclusion:
	addq	$24, %rsp
	popq	%rbp
	retq
