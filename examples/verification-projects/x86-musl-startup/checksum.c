/* Small integer-only application with genuine musl startup and termination. */
#include <stdint.h>

static volatile uint32_t seed = 1;

__attribute__((noinline))
uint32_t wrapping_checksum(const unsigned char *input, unsigned long length,
                           uint32_t initial) {
    uint32_t result = initial;
    for (unsigned long i = 0; i < length; ++i)
        result = result * UINT32_C(33) + input[i];
    return result;
}

int main(int argc, char **argv) {
    static const unsigned char input[] = {0, 1, 127, 128, 254, 255};
    (void)argv;
    uint32_t result = wrapping_checksum(input, sizeof input, seed);
    return argc == 1 && result == UINT32_C(1297365918) ? 0 : 1;
}
