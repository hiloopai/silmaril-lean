/* Differential-test harness for the int-ext lane (gen_int_ext_vectors.py).

   Each input line is
     code-hex  r0 .. r15  rflags  m0 .. m7
   (hex). The harness copies the instruction bytes into an executable page,
   followed by an indirect jump back, loads the sixteen general-purpose
   registers (except RSP, which stays the harness stack pointer and is
   reported) and RFLAGS, executes the instruction, and prints
     r0 .. r15  rflags  m0 .. m7  pushed  rsp0
   where m0..m7 are the eight words of the data area at DATA (mapped at a fixed
   address so that memory operands can be built from register values),
   `pushed` is the word at the final RSP and `rsp0` is RSP when the instruction
   started (gen_int_vectors.py). */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define DATA_PAGE 0x10000000UL
#define DATA (DATA_PAGE + 0x800)

uint64_t in_regs[17], out_regs[17], saved_rsp, code_ptr, out_pushed;

extern void run_case(void);
extern char back_label[];

__asm__(
    ".text\n"
    ".globl run_case\n"
    "run_case:\n"
    "  push %rbx\n push %rbp\n push %r12\n push %r13\n push %r14\n push %r15\n"
    "  sub $64, %rsp\n"
    "  mov %rsp, saved_rsp(%rip)\n"
    "  pushq in_regs+128(%rip)\n"
    "  popfq\n"
    "  mov in_regs+0(%rip), %rax\n"
    "  mov in_regs+8(%rip), %rcx\n"
    "  mov in_regs+16(%rip), %rdx\n"
    "  mov in_regs+24(%rip), %rbx\n"
    "  mov in_regs+40(%rip), %rbp\n"
    "  mov in_regs+48(%rip), %rsi\n"
    "  mov in_regs+56(%rip), %rdi\n"
    "  mov in_regs+64(%rip), %r8\n"
    "  mov in_regs+72(%rip), %r9\n"
    "  mov in_regs+80(%rip), %r10\n"
    "  mov in_regs+88(%rip), %r11\n"
    "  mov in_regs+96(%rip), %r12\n"
    "  mov in_regs+104(%rip), %r13\n"
    "  mov in_regs+112(%rip), %r14\n"
    "  mov in_regs+120(%rip), %r15\n"
    "  jmp *code_ptr(%rip)\n"
    ".globl back_label\n"
    "back_label:\n"
    "  mov %rax, out_regs+0(%rip)\n"
    "  mov %rcx, out_regs+8(%rip)\n"
    "  mov %rdx, out_regs+16(%rip)\n"
    "  mov %rbx, out_regs+24(%rip)\n"
    "  mov %rsp, out_regs+32(%rip)\n"
    "  mov %rbp, out_regs+40(%rip)\n"
    "  mov %rsi, out_regs+48(%rip)\n"
    "  mov %rdi, out_regs+56(%rip)\n"
    "  mov %r8, out_regs+64(%rip)\n"
    "  mov %r9, out_regs+72(%rip)\n"
    "  mov %r10, out_regs+80(%rip)\n"
    "  mov %r11, out_regs+88(%rip)\n"
    "  mov %r12, out_regs+96(%rip)\n"
    "  mov %r13, out_regs+104(%rip)\n"
    "  mov %r14, out_regs+112(%rip)\n"
    "  mov %r15, out_regs+120(%rip)\n"
    "  pushfq\n"
    "  popq out_regs+128(%rip)\n"
    "  mov (%rsp), %rax\n"
    "  mov %rax, out_pushed(%rip)\n"
    "  mov saved_rsp(%rip), %rsp\n"
    "  add $64, %rsp\n"
    "  pop %r15\n pop %r14\n pop %r13\n pop %r12\n pop %rbp\n pop %rbx\n"
    "  ret\n");

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return c - 'A' + 10;
}

int main(void) {
  uint8_t *code = mmap(NULL, 4096, PROT_READ | PROT_WRITE | PROT_EXEC,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  uint8_t *data = mmap((void *)DATA_PAGE, 4096, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
  if (code == MAP_FAILED || data != (uint8_t *)DATA_PAGE) {
    fprintf(stderr, "mmap failed\n");
    return 1;
  }
  char hex[64];
  while (scanf("%63s", hex) == 1) {
    size_t n = strlen(hex) / 2;
    for (size_t i = 0; i < n; i++)
      code[i] = (uint8_t)(hexval(hex[2 * i]) * 16 + hexval(hex[2 * i + 1]));
    /* jmp *0(%rip); .quad back_label */
    code[n] = 0xFF; code[n + 1] = 0x25;
    code[n + 2] = code[n + 3] = code[n + 4] = code[n + 5] = 0;
    uint64_t back = (uint64_t)back_label;
    memcpy(code + n + 6, &back, 8);
    __builtin___clear_cache((char *)code, (char *)code + n + 14);
    for (int i = 0; i < 17; i++)
      if (scanf("%lx", &in_regs[i]) != 1) return 1;
    uint64_t *mem = (uint64_t *)DATA;
    for (int i = 0; i < 8; i++)
      if (scanf("%lx", &mem[i]) != 1) return 1;
    code_ptr = (uint64_t)code;
    run_case();
    for (int i = 0; i < 17; i++) printf("%lx ", out_regs[i]);
    for (int i = 0; i < 8; i++) printf("%lx ", mem[i]);
    printf("%lx %lx\n", out_pushed, saved_rsp);
  }
  return 0;
}
