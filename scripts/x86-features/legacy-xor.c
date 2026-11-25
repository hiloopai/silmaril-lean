#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int main(void) {
    uint64_t dest[2] = {UINT64_C(0xfedcba9876543210), UINT64_C(0x0123456789abcdef)};
    _Alignas(16) uint64_t source[2] = {UINT64_C(0x1122334455667788), UINT64_C(0xffff0000aaaa5555)};
    uint64_t pxor[2], xorps[2];
    __asm__ volatile ("movdqu %1, %%xmm0; movdqu %2, %%xmm1; pxor %%xmm1, %%xmm0; movdqu %%xmm0, %0"
                      : "=m"(pxor) : "m"(dest), "m"(source) : "xmm0", "xmm1");
    __asm__ volatile ("movdqu %1, %%xmm0; xorps %2, %%xmm0; movdqu %%xmm0, %0"
                      : "=m"(xorps) : "m"(dest), "m"(source) : "xmm0");
    printf("PXOR reg:  %016" PRIx64 "%016" PRIx64 "\n", pxor[1], pxor[0]);
    printf("XORPS mem: %016" PRIx64 "%016" PRIx64 "\n", xorps[1], xorps[0]);
    return !(pxor[1] == UINT64_C(0xfedc4567230198ba) && pxor[0] == UINT64_C(0xeffe89dc23324598)
             && pxor[0] == xorps[0] && pxor[1] == xorps[1]);
}
