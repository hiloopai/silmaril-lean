/* Process entry and the single system-call gate of sha256sum-min.

   _start receives the Linux x86-64 initial stack (argc, argv[], 0, envp[], 0,
   auxv) and passes its address to cmain, which never returns.

   sc3 is the only `syscall` instruction in the binary: every kernel request
   goes through it, so a proof needs one syscall rule, applied at one address. */
	.section .text._start,"ax",@progbits
	.globl _start
	.type _start,@function
_start:
	xorl	%ebp, %ebp
	movq	%rsp, %rdi
	andq	$-16, %rsp
	call	cmain
	ud2
	.size _start, .-_start

	.section .text.sc3,"ax",@progbits
	.globl sc3
	.type sc3,@function
/* long sc3(long nr, long a0, long a1, long a2) */
sc3:
	movq	%rdi, %rax
	movq	%rsi, %rdi
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	syscall
	ret
	.size sc3, .-sc3

	.section .note.GNU-stack,"",@progbits
