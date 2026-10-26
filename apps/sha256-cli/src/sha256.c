/* sha256: a freestanding x86-64 Linux filter.
 *
 * Reads all of stdin with raw read(2), hashes it with sha256_compress (the
 * xcompile/wrappers/xc_sha256.c function, linked as the pinned clang 18.1.3
 * -O2 object code, see sha256_compress_clang_o2.S), and writes the 64
 * lowercase hex digits of the SHA-256 digest and "\n" with raw write(2).
 *
 * Exit status: 0 on success; 1 as soon as read returns an error or write
 * returns an error or accepts no byte. No call is retried, so the program is
 * correct against the full Process.Syscall model (a failed read may consume
 * input there), and it never runs again after a refusal.
 *
 * Written for the proof: no libc, no stack buffers, globals at fixed
 * addresses, one byte per store, a lookup table for the hex digits. */
#include <stdint.h>

extern void sha256_compress(uint32_t state[8], const uint8_t block[64]);

static uint32_t H[8];
static union { uint8_t b[64]; uint64_t q[8]; } blk;
static uint8_t out[65];
static const char hexd[16] = "0123456789abcdef";

static inline long sys3(long nr, long fd, const void *p, unsigned long n) {
    long r;
    __asm__ volatile ("syscall"
                      : "=a"(r)
                      : "a"(nr), "D"(fd), "S"(p), "d"(n)
                      : "rcx", "r11", "memory");
    return r;
}

__attribute__((noreturn)) static inline void sys_exit(long status) {
    __asm__ volatile ("syscall" : : "a"(60L), "D"(status) : "rcx", "r11", "memory");
    __builtin_unreachable();
}

__attribute__((noreturn, used)) void cmain(void) {
    H[0] = 0x6a09e667; H[1] = 0xbb67ae85; H[2] = 0x3c6ef372; H[3] = 0xa54ff53a;
    H[4] = 0x510e527f; H[5] = 0x9b05688c; H[6] = 0x1f83d9ab; H[7] = 0x5be0cd19;

    uint64_t total = 0;
    unsigned long fill = 0;
    for (;;) {
        long n = sys3(0, 0, blk.b + fill, 64 - fill);
        if (n == 0)
            break;
        if (n < 0)
            sys_exit(1);
        fill += n;
        total += n;
        if (fill == 64) {
            sha256_compress(H, blk.b);
            fill = 0;
        }
    }

    blk.b[fill++] = 0x80;
    if (fill > 56) {
        while (fill < 64)
            blk.b[fill++] = 0;
        sha256_compress(H, blk.b);
        fill = 0;
    }
    while (fill < 56)
        blk.b[fill++] = 0;
    blk.q[7] = __builtin_bswap64(total << 3);
    sha256_compress(H, blk.b);

    const uint8_t *hb = (const uint8_t *)H;
    for (unsigned long i = 0; i < 32; i++) {
        unsigned b = hb[i ^ 3];
        out[2 * i] = hexd[b >> 4];
        out[2 * i + 1] = hexd[b & 15];
    }
    out[64] = '\n';

    unsigned long off = 0;
    while (off < 65) {
        long n = sys3(1, 1, out + off, 65 - off);
        if (n <= 0)
            sys_exit(1);
        off += n;
    }
    sys_exit(0);
}
