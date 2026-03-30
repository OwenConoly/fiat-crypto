#!/bin/bash
# Syncs test files to remote Linux server, builds and tests scalar + AVX asm against C reference.
set -e
REMOTE="aspears@xz.ax"
DIR="fiat-crypto-test-asm"

scp -q test-asm/test_add.c test-asm/simple_scalar_add.asm test-asm/simple_avx_add.asm "$REMOTE:$DIR/" 2>/dev/null || \
  (ssh "$REMOTE" "mkdir -p $DIR" && scp -q test-asm/test_add.c test-asm/simple_scalar_add.asm test-asm/simple_avx_add.asm "$REMOTE:$DIR/")

ssh "$REMOTE" "cd $DIR && \
  nasm -f elf64 simple_scalar_add.asm -o scalar.o && \
  nasm -f elf64 simple_avx_add.asm -o avx.o && \
  echo '--- Scalar ---' && cc test_add.c scalar.o -o test_scalar && ./test_scalar && \
  echo '--- AVX ---' && cc test_add.c avx.o -o test_avx && ./test_avx"
