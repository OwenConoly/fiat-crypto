; DEVELOPMENTAL - test file for AVX equivalence checking, will be removed
;
; Lane 2 variant: each limb is placed in lane 2 (bits 128-191) of a YMM
; register via vperm2i128, added via vpaddq ymm, and extracted with
; vextracti128 + vmovq.
; Tests that rewrite rules work for YMM-width (256-bit) operations.
;
; Requires symbolic semantics for: vperm2i128, vextracti128, vzeroupper
; (not yet implemented as of March 2026)
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' add \
;     --hints-file test-asm/simple_avx_add_lane2.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	; limb 0: load 64 bits into xmm lane 0, move to ymm lane 2, add, extract
	vmovq	xmm0, [rsi]
	vperm2i128	ymm0, ymm0, ymm0, 0x08	; lower 128 zeroed, upper 128 = old lower
	; ymm0 lanes: [0, 0, limb0, 0]
	vmovq	xmm1, [rdx]
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1		; lane 2 = limb0 + limb0'
	vextracti128	xmm2, ymm0, 1		; xmm2 = upper 128 = [result, 0]
	vmovq	[rdi], xmm2			; store lane 0 of xmm2 = lane 2 of ymm0

	; limb 1
	vmovq	xmm0, [rsi + 8]
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 8]
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm2, ymm0, 1
	vmovq	[rdi + 8], xmm2

	; limb 2
	vmovq	xmm0, [rsi + 16]
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 16]
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm2, ymm0, 1
	vmovq	[rdi + 16], xmm2

	; limb 3
	vmovq	xmm0, [rsi + 24]
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 24]
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm2, ymm0, 1
	vmovq	[rdi + 24], xmm2

	; limb 4
	vmovq	xmm0, [rsi + 32]
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 32]
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm2, ymm0, 1
	vmovq	[rdi + 32], xmm2

	vzeroupper
	ret
