# getrandom(rsp, 8, 0); exit(its return value). The buffer is the entry stack
# pointer (argc and the argv[0] pointer are overwritten, harmlessly).
    .text
    .globl _start
_start:
    mov %rsp, %rdi       # 48 89 e7         buf = entry stack pointer
    mov $8, %esi         # be 08 00 00 00   8 bytes
    mov $0, %edx         # ba 00 00 00 00   flags 0
    mov $318, %eax       # b8 3e 01 00 00   getrandom
    syscall
    mov %rax, %rdi       # 48 89 c7         status = return value
    mov $60, %eax        # b8 3c 00 00 00   exit
    syscall
