; DEVELOPMENTAL - test file for equivalence checking, will be removed
;
; Scalar field addition for curve25519 (unsaturated solinas, 5 limbs x 64-bit).
; Loads each limb individually, adds with scalar add, stores back.
; This is the baseline that the existing equivalence checker handles correctly.

SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	mov rax, [rsi]
	add rax, [rdx]
	mov [rdi], rax
	mov rax, [rsi + 8]
	add rax, [rdx + 8]
	mov [rdi + 8], rax
	mov rax, [rsi + 16]
	add rax, [rdx + 16]
	mov [rdi + 16], rax
	mov rax, [rsi + 24]
	add rax, [rdx + 24]
	mov [rdi + 24], rax
	mov rax, [rsi + 32]
	add rax, [rdx + 32]
	mov [rdi + 32], rax
	ret
