; DEVELOPMENTAL - test file for AVX equivalence checking, will be removed
;
; Wrapped batched AVX2 field addition for curve25519.
; This wraps an ISPC-compiled batched_field_add (which processes 4 field
; elements at once using gather/scatter) into a single-element interface
; matching fiat_25519_add(out, arg1, arg2).
;
; Strategy:
;   1. Copy arg1/arg2 into slot 0 of stack-allocated input arrays
;   2. Run the batched AVX2 body (vpgatherdq to load, vpaddq to add,
;      shuffle/permute to transpose back)
;   3. Copy result slot 0 to the output pointer
;
; This is a future goal - requires many more opcodes than simple_avx_add.asm
; (vpgatherdq, vpinsrd, vpunpcklqdq, vperm2i128, vextracti128, vpextrq, etc.)

SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	push	rbp
	push	rbx
	sub	rsp, 488
	;; rdi=out, rsi=arg1, rdx=arg2
	mov	rbx, rdi		;; save actual output pointer
	;; Copy arg1 into in1[slot0] at [rsp+0]
	mov	rax, [rsi + 0]
	mov	[rsp + 0], rax
	mov	rax, [rsi + 8]
	mov	[rsp + 8], rax
	mov	rax, [rsi + 16]
	mov	[rsp + 16], rax
	mov	rax, [rsi + 24]
	mov	[rsp + 24], rax
	mov	rax, [rsi + 32]
	mov	[rsp + 32], rax
	;; Copy arg2 into in2[slot0] at [rsp+160]
	mov	rax, [rdx + 0]
	mov	[rsp + 160], rax
	mov	rax, [rdx + 8]
	mov	[rsp + 168], rax
	mov	rax, [rdx + 16]
	mov	[rsp + 176], rax
	mov	rax, [rdx + 24]
	mov	[rsp + 184], rax
	mov	rax, [rdx + 32]
	mov	[rsp + 192], rax
	;; Point rdi/rsi/rdx at stack buffers
	lea	rdi, [rsp + 320]	;; result buffer (4 elems * 40 bytes)
	lea	rsi, [rsp + 0]		;; in1
	lea	rdx, [rsp + 160]	;; in2

	;; === inline batched_field_add body ===

	;; xmm2 = [0, 40, 80, 120]  (limb0 byte offsets into each element)
	xor	eax, eax
	vmovd	xmm2, eax
	mov	eax, 40
	vpinsrd	xmm2, xmm2, eax, 1
	mov	eax, 80
	vpinsrd	xmm2, xmm2, eax, 2
	mov	eax, 120
	vpinsrd	xmm2, xmm2, eax, 3

	vpxor	xmm0, xmm0, xmm0
	vpcmpeqd	ymm1, ymm1, ymm1
	vpgatherdq	ymm0, [rsi + xmm2], ymm1
	vpxor	xmm1, xmm1, xmm1
	vpcmpeqd	ymm3, ymm3, ymm3
	vpgatherdq	ymm1, [rdx + xmm2], ymm3

	;; xmm3 = [8, 48, 88, 128]  (limb1 byte offsets)
	mov	eax, 8
	vmovd	xmm3, eax
	mov	eax, 48
	vpinsrd	xmm3, xmm3, eax, 1
	mov	eax, 88
	vpinsrd	xmm3, xmm3, eax, 2
	mov	eax, 128
	vpinsrd	xmm3, xmm3, eax, 3

	vpxor	xmm2, xmm2, xmm2
	vpcmpeqd	ymm4, ymm4, ymm4
	vpgatherdq	ymm2, [rsi + xmm3], ymm4
	vpxor	xmm4, xmm4, xmm4
	vpcmpeqd	ymm5, ymm5, ymm5
	vpgatherdq	ymm4, [rdx + xmm3], ymm5

	;; xmm3 = [16, 56, 96, 136]  (limb2 byte offsets)
	mov	eax, 16
	vmovd	xmm3, eax
	mov	eax, 56
	vpinsrd	xmm3, xmm3, eax, 1
	mov	eax, 96
	vpinsrd	xmm3, xmm3, eax, 2
	mov	eax, 136
	vpinsrd	xmm3, xmm3, eax, 3

	vpxor	xmm5, xmm5, xmm5
	vpcmpeqd	ymm6, ymm6, ymm6
	vpgatherdq	ymm5, [rsi + xmm3], ymm6
	vpxor	xmm6, xmm6, xmm6
	vpcmpeqd	ymm7, ymm7, ymm7
	vpgatherdq	ymm6, [rdx + xmm3], ymm7

	;; xmm3 = [24, 64, 104, 144]  (limb3 byte offsets)
	mov	eax, 24
	vmovd	xmm3, eax
	mov	eax, 64
	vpinsrd	xmm3, xmm3, eax, 1
	mov	eax, 104
	vpinsrd	xmm3, xmm3, eax, 2
	mov	eax, 144
	vpinsrd	xmm3, xmm3, eax, 3

	vpxor	xmm7, xmm7, xmm7
	vpcmpeqd	ymm8, ymm8, ymm8
	vpgatherdq	ymm7, [rsi + xmm3], ymm8
	vpxor	xmm8, xmm8, xmm8
	vpcmpeqd	ymm9, ymm9, ymm9
	vpgatherdq	ymm8, [rdx + xmm3], ymm9

	;; xmm3 = [32, 72, 112, 152]  (limb4 byte offsets)
	mov	eax, 32
	vmovd	xmm3, eax
	mov	eax, 72
	vpinsrd	xmm3, xmm3, eax, 1
	mov	eax, 112
	vpinsrd	xmm3, xmm3, eax, 2
	mov	eax, 152
	vpinsrd	xmm3, xmm3, eax, 3

	vpxor	xmm9, xmm9, xmm9
	vpcmpeqd	ymm10, ymm10, ymm10
	vpgatherdq	ymm9, [rsi + xmm3], ymm10
	vpcmpeqd	ymm10, ymm10, ymm10
	vpxor	xmm11, xmm11, xmm11
	vpgatherdq	ymm11, [rdx + xmm3], ymm10

	;; Add the 5 limbs across all 4 lanes
	vpaddq	ymm0, ymm0, ymm1	;; ymm0 = limb0 sums
	vpaddq	ymm1, ymm2, ymm4	;; ymm1 = limb1 sums
	vpaddq	ymm2, ymm5, ymm6	;; ymm2 = limb2 sums
	vpaddq	ymm3, ymm7, ymm8	;; ymm3 = limb3 sums
	vpaddq	ymm4, ymm9, ymm11	;; ymm4 = limb4 sums

	;; Transpose SoA->AoS and store to result buffer
	vpunpcklqdq	xmm13, xmm0, xmm1
	vmovdqu	[rdi], xmm13
	vpextrq	[rdi + 40], xmm0, 1
	vextracti128	xmm12, ymm0, 1
	vmovq	[rdi + 80], xmm12
	vpextrq	[rdi + 120], xmm12, 1
	vpunpckhqdq	xmm12, xmm1, xmm13
	vmovdqu	[rdi + 48], xmm12
	vpunpcklqdq	ymm12, ymm1, ymm2
	vpunpcklqdq	ymm13, ymm3, ymm4
	vperm2i128	ymm12, ymm12, ymm13, 49
	vmovdqu	[rdi + 88], ymm12
	vpunpckhqdq	ymm12, ymm1, ymm2
	vpunpckhqdq	ymm13, ymm3, ymm4
	vperm2i128	ymm12, ymm12, ymm13, 49
	vmovdqu	[rdi + 128], ymm12
	vmovq	[rdi + 16], xmm2
	vpunpcklqdq	xmm12, xmm3, xmm4
	vmovdqu	[rdi + 24], xmm12
	vpunpckhqdq	xmm12, xmm3, xmm4
	vmovdqu	[rdi + 64], xmm12
	vzeroupper
	;; === end inline body ===

	;; Copy result[0] (first 40 bytes of result buffer) to actual output
	mov	rax, [rsp + 320]
	mov	[rbx + 0], rax
	mov	rax, [rsp + 328]
	mov	[rbx + 8], rax
	mov	rax, [rsp + 336]
	mov	[rbx + 16], rax
	mov	rax, [rsp + 344]
	mov	[rbx + 24], rax
	mov	rax, [rsp + 352]
	mov	[rbx + 32], rax

	add	rsp, 488
	pop	rbx
	pop	rbp
	ret
