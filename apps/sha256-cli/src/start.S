/* Process entry. Linux enters _start with %rsp 16-byte aligned (psABI 3.4.1);
 * the call leaves %rsp = 8 (mod 16) at cmain, as for any SysV function.
 * cmain never returns (it ends in exit), so the ud2 is unreachable. */
	.text
	.globl _start
	.type _start,@function
_start:
	call cmain
	ud2
	.size _start, . - _start
	.section .note.GNU-stack,"",@progbits
