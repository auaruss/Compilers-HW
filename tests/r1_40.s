start:
	movq	$10, -8(%rbp)
	negq	-8(%rbp)
	movq	$52, %rax
	addq	-8(%rbp), %rax
	jmp	conclusion
	.globl _main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$8, %rsp
	jmp start
conclusion:
	addq	$8, %rsp
	popq	%rbp
	retq