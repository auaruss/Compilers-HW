start:
	callq	read_int
	movq	%rax, %rax
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
