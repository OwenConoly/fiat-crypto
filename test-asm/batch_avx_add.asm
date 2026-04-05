SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	vmovdqu ymm0, [rsi]
	vpaddq ymm0, ymm0, [rdx]
	vmovdqu [rdi], ymm0
	vmovdqu ymm1, [rsi + 32]
	vpaddq ymm1, ymm1, [rdx + 32]
	vmovdqu [rdi + 32], ymm1
	vmovdqu ymm2, [rsi + 64]
	vpaddq ymm2, ymm2, [rdx + 64]
	vmovdqu [rdi + 64], ymm2
	vmovdqu ymm3, [rsi + 96]
	vpaddq ymm3, ymm3, [rdx + 96]
	vmovdqu [rdi + 96], ymm3
	vmovdqu ymm4, [rsi + 128]
	vpaddq ymm4, ymm4, [rdx + 128]
	vmovdqu [rdi + 128], ymm4
	vzeroupper
	ret
