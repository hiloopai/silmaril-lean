/* Process entry and the single system-call gate shared by every ladder rung.

   _start receives the Linux x86-64 initial stack (argc, argv[], 0, envp[], 0,
   auxv), passes its address to `int cmain(long *sp)`, then exits with the
   returned status through sc3.  `sc3` holds the only `syscall` instruction in
   every ladder binary, so a proof needs one syscall rule at one address
   (the same discipline as silmaril-lean apps/sha256sum-min/src/start.S). */
	.section .text._start,"ax",@progbits
	.globl _start
	.type _start,@function
_start:
	xorl	%ebp, %ebp
	movq	%rsp, %rdi
	andq	$-16, %rsp
	call	cmain
	movslq	%eax, %rsi
	movl	$231, %edi		/* exit_group */
	call	sc3
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
