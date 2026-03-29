#!/bin/sh
if ../src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier 25519 64 '(auto)' '2^255 - 19' add \
  --hints-file simple_avx_add.asm \
  -o /dev/null --output-asm /dev/null 2>/dev/null; then
  echo "PASS"
else
  echo "FAIL"
  exit 1
fi
