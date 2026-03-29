; DEVELOPMENTAL - test file for AVX equivalence checking, will be removed
;
; Lane 3 variant: each limb is placed in lane 3 (bits 192-255) of a YMM
; register via vpunpcklqdq + vperm2i128, added via vpaddq ymm, and extracted
; with vextracti128 + vpextrq.
; Tests the full chain of slice/set_slice rewrite rules at maximum offset.
;
; Requires symbolic semantics for: vpxor, vpunpcklqdq, vperm2i128,
; vextracti128, vpextrq, vzeroupper
; (not yet implemented as of March 2026)
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' add \
;     --hints-file test-asm/simple_avx_add_lane3.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	vpxor	xmm2, xmm2, xmm2		; xmm2 = zero

	; limb 0: load into xmm lane 0, move to lane 1, then to ymm upper half
	vmovq	xmm0, [rsi]
	vpunpcklqdq	xmm0, xmm2, xmm0	; xmm0 = [0, limb0]
	vperm2i128	ymm0, ymm0, ymm0, 0x08	; ymm0 = [0, 0, 0, limb0]
	vmovq	xmm1, [rdx]
	vpunpcklqdq	xmm1, xmm2, xmm1
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1		; lane 3 = limb0 + limb0'
	vextracti128	xmm3, ymm0, 1		; xmm3 = [0, result]
	vpextrq	[rdi], xmm3, 1			; store lane 1 of xmm3 = lane 3 of ymm0

	; limb 1
	vmovq	xmm0, [rsi + 8]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 8]
	vpunpcklqdq	xmm1, xmm2, xmm1
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm3, ymm0, 1
	vpextrq	[rdi + 8], xmm3, 1

	; limb 2
	vmovq	xmm0, [rsi + 16]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 16]
	vpunpcklqdq	xmm1, xmm2, xmm1
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm3, ymm0, 1
	vpextrq	[rdi + 16], xmm3, 1

	; limb 3
	vmovq	xmm0, [rsi + 24]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 24]
	vpunpcklqdq	xmm1, xmm2, xmm1
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm3, ymm0, 1
	vpextrq	[rdi + 24], xmm3, 1

	; limb 4
	vmovq	xmm0, [rsi + 32]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vperm2i128	ymm0, ymm0, ymm0, 0x08
	vmovq	xmm1, [rdx + 32]
	vpunpcklqdq	xmm1, xmm2, xmm1
	vperm2i128	ymm1, ymm1, ymm1, 0x08
	vpaddq	ymm0, ymm0, ymm1
	vextracti128	xmm3, ymm0, 1
	vpextrq	[rdi + 32], xmm3, 1

	vzeroupper
	ret
