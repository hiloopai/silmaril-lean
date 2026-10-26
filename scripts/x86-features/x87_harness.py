"""Native x87 execution harness for gen_x87_vectors.py.

Each instruction form is assembled as raw bytes (`.byte`, so the bytes are
exactly the SDM encoding and no assembler mnemonic convention intervenes) into
a function

    frstor (in)          ; load control, status, tag word and ST(0..7)
    mov rax, io.rax_in   ; and RFLAGS
    push io.fl_in; popfq
    <instruction>        ; memory operands address [rdi], a 128-byte buffer
    fnsave (out)         ; non-waiting: records the state even when an
                         ; unmasked exception is pending
    pushfq; pop io.fl_out
    mov io.rax_out, rax

FRSTOR and FNSAVE use the 108-byte 32-bit protected-mode image (SDM Vol. 1,
Figure 8-10): FCW, FSW and FTW at offsets 0, 4, 8, then ST(0)..ST(7) from
offset 28. An unmasked exception is deferred to the next waiting x87
instruction, so it does not trap inside the harness; an instruction that
itself waits on a pending exception raises SIGFPE, which the harness reports
as `fault`.
"""

import os
import struct
import subprocess
import tempfile

HARNESS_C = r"""
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
struct io { uint64_t rax_in, fl_in, rax_out, fl_out; };
typedef void (*fn)(unsigned char *mem, unsigned char *in, unsigned char *out, struct io *io);
extern fn table[];
static sigjmp_buf jb;
static void onfpe(int s) { (void)s; siglongjmp(jb, 1); }
static void hexbytes(const char *s, unsigned char *out, int max) {
  int n = 0;
  while (s[0] && s[1] && n < max) { unsigned v; sscanf(s, "%2x", &v); out[n++] = v; s += 2; }
}
int main(void) {
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = onfpe;
  sa.sa_flags = SA_NODEFER;
  sigaction(SIGFPE, &sa, 0);
  static char line[8192], imgs[1024], mems[1024];
  static unsigned char in[112] __attribute__((aligned(16))), out[112] __attribute__((aligned(16)));
  static unsigned char mem[128] __attribute__((aligned(16)));
  while (fgets(line, sizeof line, stdin)) {
    int idx, memlen;
    unsigned long long rax, fl;
    if (sscanf(line, "%d %1023s %d %1023s %llx %llx", &idx, imgs, &memlen, mems, &rax, &fl) != 6)
      break;
    memset(in, 0, sizeof in); memset(out, 0, sizeof out); memset(mem, 0, sizeof mem);
    hexbytes(imgs, in, 108);
    hexbytes(mems, mem, 128);
    struct io io = { rax, fl, 0, 0 };
    if (sigsetjmp(jb, 1) == 0) {
      table[idx](mem, in, out, &io);
      printf("ok ");
      for (int i = 0; i < 108; i++) printf("%02x", out[i]);
      printf(" ");
      for (int i = 0; i < memlen; i++) printf("%02x", mem[i]);
      if (memlen == 0) printf("00");
      printf(" %llx %llx\n", (unsigned long long)io.rax_out, (unsigned long long)io.fl_out);
    } else {
      __asm__ volatile("fninit");
      printf("fault\n");
    }
  }
  return 0;
}
"""


def build(forms, tmp=None):
    """Build the harness for a list of byte sequences; returns the executable."""
    tmp = tmp or tempfile.mkdtemp()
    asm = [".text"]
    for i, bs in enumerate(forms):
        asm += [f".globl f_{i}", f"f_{i}:", "  frstor (%rsi)", "  mov 0(%rcx), %rax",
                "  pushq 8(%rcx)", "  popfq", "  .byte " + ",".join("0x%02x" % b for b in bs),
                "  fnsave (%rdx)", "  pushfq", "  popq 24(%rcx)", "  mov %rax, 16(%rcx)",
                "  ret"]
    asm += [".data", ".globl table", "table:"] + [f"  .quad f_{i}" for i in range(len(forms))]
    asm += ['.section .note.GNU-stack,"",@progbits']
    with open(os.path.join(tmp, "forms.s"), "w") as f:
        f.write("\n".join(asm) + "\n")
    with open(os.path.join(tmp, "h.c"), "w") as f:
        f.write(HARNESS_C)
    exe = os.path.join(tmp, "h")
    subprocess.run(["gcc", "-O1", "-o", exe, os.path.join(tmp, "h.c"),
                    os.path.join(tmp, "forms.s")], check=True)
    return exe


def image(cw, sw, tw, regs):
    """The 108-byte FRSTOR image; `regs` are ST(0)..ST(7)."""
    b = struct.pack("<III", cw | 0xFFFF0000, sw | 0xFFFF0000, tw | 0xFFFF0000) + bytes(16)
    for r in regs:
        b += r.to_bytes(10, "little")
    return b


def parse_image(h):
    b = bytes.fromhex(h)
    cw, sw, tw = (int.from_bytes(b[o:o + 2], "little") for o in (0, 4, 8))
    regs = [int.from_bytes(b[28 + 10 * i:38 + 10 * i], "little") for i in range(8)]
    return cw, sw, tw, regs


def run(exe, cases):
    """cases: (form index, cw, sw, tw, regs, mem bytes, memlen, rax, rflags).
    Returns, per case, None for a fault or (cw, sw, tw, regs, mem, rax, rflags)."""
    text = "".join("%d %s %d %s %x %x\n" % (
        c[0], image(*c[1:5]).hex(), c[6], (c[5].hex() or "00"), c[7], c[8]) for c in cases)
    res = subprocess.run([exe], input=text, capture_output=True, text=True, check=True).stdout
    out = []
    for line in res.splitlines():
        p = line.split()
        if p[0] == "fault":
            out.append(None)
        else:
            cw, sw, tw, regs = parse_image(p[1])
            out.append((cw, sw, tw, regs, bytes.fromhex(p[2]), int(p[3], 16), int(p[4], 16)))
    assert len(out) == len(cases), (len(out), len(cases))
    return out
