; DEVELOPMENTAL - test file for AVX equivalence checking, will be removed
;
; Lane 1 variant: each limb is placed in lane 1 (upper 64 bits) of an XMM
; register, added via vpaddq, and extracted from lane 1 with vpextrq.
; Tests that slice/set_slice rewrite rules work for non-zero lane offsets.
;
; Requires symbolic semantics for: vpxor, vpunpcklqdq, vpextrq
; (not yet implemented as of March 2026)
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' add \
;     --hints-file test-asm/simple_avx_add_lane1.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	vpxor	xmm2, xmm2, xmm2		; xmm2 = [0, 0] (zero register)

	; limb 0: load into lane 0, move to lane 1, add, extract lane 1
	vmovq	xmm0, [rsi]
	vmovq	xmm1, [rdx]
	vpunpcklqdq	xmm0, xmm2, xmm0	; xmm0 = [0, limb0]
	vpunpcklqdq	xmm1, xmm2, xmm1	; xmm1 = [0, limb0']
	vpaddq	xmm0, xmm0, xmm1		; xmm0 = [0, limb0+limb0']
	vpextrq	[rdi], xmm0, 1			; store lane 1

	; limb 1
	vmovq	xmm0, [rsi + 8]
	vmovq	xmm1, [rdx + 8]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vpunpcklqdq	xmm1, xmm2, xmm1
	vpaddq	xmm0, xmm0, xmm1
	vpextrq	[rdi + 8], xmm0, 1

	; limb 2
	vmovq	xmm0, [rsi + 16]
	vmovq	xmm1, [rdx + 16]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vpunpcklqdq	xmm1, xmm2, xmm1
	vpaddq	xmm0, xmm0, xmm1
	vpextrq	[rdi + 16], xmm0, 1

	; limb 3
	vmovq	xmm0, [rsi + 24]
	vmovq	xmm1, [rdx + 24]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vpunpcklqdq	xmm1, xmm2, xmm1
	vpaddq	xmm0, xmm0, xmm1
	vpextrq	[rdi + 24], xmm0, 1

	; limb 4
	vmovq	xmm0, [rsi + 32]
	vmovq	xmm1, [rdx + 32]
	vpunpcklqdq	xmm0, xmm2, xmm0
	vpunpcklqdq	xmm1, xmm2, xmm1
	vpaddq	xmm0, xmm0, xmm1
	vpextrq	[rdi + 32], xmm0, 1

	ret
