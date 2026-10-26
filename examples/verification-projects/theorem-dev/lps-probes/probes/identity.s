# getpid, gettid, set_tid_address(NULL), getuid, geteuid; exit with
# (tid - pid) + (set_tid_address - pid) + (euid - uid) + 0: status 0 when the
# identities agree. `add $0, %rdi` is the mutation slot.
    .text
    .globl _start
_start:
    mov $39, %eax        # b8 27 00 00 00   getpid
    syscall              # 0f 05
    mov %rax, %rbx       # 48 89 c3         rbx = pid
    mov $186, %eax       # b8 ba 00 00 00   gettid
    syscall
    sub %rbx, %rax       # 48 29 d8         tid - pid
    mov %rax, %r12       # 49 89 c4
    mov $218, %eax       # b8 da 00 00 00   set_tid_address
    mov $0, %edi         # bf 00 00 00 00   NULL
    syscall
    sub %rbx, %rax       # 48 29 d8         set_tid_address - pid
    add %rax, %r12       # 49 01 c4
    mov $102, %eax       # b8 66 00 00 00   getuid
    syscall
    mov %rax, %rbx       # 48 89 c3         rbx = uid
    mov $107, %eax       # b8 6b 00 00 00   geteuid
    syscall
    sub %rbx, %rax       # 48 29 d8         euid - uid
    add %r12, %rax       # 4c 01 e0
    mov %rax, %rdi       # 48 89 c7
    add $0, %rdi         # 48 83 c7 00      mutation slot
    mov $60, %eax        # b8 3c 00 00 00   exit
    syscall
