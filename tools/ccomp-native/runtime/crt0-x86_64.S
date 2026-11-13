.intel_syntax noprefix
.text
.globl _start
.type _start, @function
_start:
  xor ebp, ebp
  mov rdi, QWORD PTR [rsp]
  lea rsi, [rsp + 8]
  lea rdx, [rsi + rdi * 8 + 8]
  and rsp, -16
  call main
  mov edi, eax
  mov eax, 231
  syscall
  ud2
.size _start, . - _start
.section .note.GNU-stack,"",@progbits
