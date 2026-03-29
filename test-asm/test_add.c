// DEVELOPMENTAL - will be removed
//
// Links against fiat_25519_add from an .asm file and checks it against a+b.
//
// nasm -f elf64 simple_avx_add.asm -o avx.o
// cc test_add.c avx.o -o test_avx && ./test_avx

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern void fiat_25519_add(uint64_t out[5], const uint64_t a[5], const uint64_t b[5]);

static uint64_t rand64(void) {
    return ((uint64_t)rand() << 32 | rand()) & 0x7ffffffffffffULL;
}

int main(void) {
    srand(42);
    int fail = 0;

    for (int t = 0; t < 1000; t++) {
        uint64_t a[5], b[5], out[5];
        for (int i = 0; i < 5; i++) { a[i] = rand64(); b[i] = rand64(); }
        fiat_25519_add(out, a, b);
        for (int i = 0; i < 5; i++) {
            if (out[i] != a[i] + b[i]) {
                if (fail++ < 3)
                    printf("FAIL test %d limb %d: got %llx expected %llx\n",
                           t, i, (unsigned long long)out[i],
                           (unsigned long long)(a[i] + b[i]));
            }
        }
    }

    printf("%s (%d failures)\n", fail ? "FAIL" : "PASS", fail);
    return fail > 0 ? 1 : 0;
}
