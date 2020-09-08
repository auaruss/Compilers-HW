start:
	movq	$41, -8(%rbp)
	movq	-8(%rbp), %rax
	addq	$1, %rax
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
