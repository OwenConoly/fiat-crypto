/* Autogenerated: src/ExtractionOCaml/bedrock2_unsaturated_solinas --lang=bedrock2 --no-wide-int --widen-carry --widen-bytes --split-multiret 25519 5 '2^255 - 19' 64 carry_mul carry_square carry add sub opp from_bytes carry_scmul121666 */
/* curve description: 25519 */
/* requested operations: carry_mul, carry_square, carry, add, sub, opp, from_bytes, carry_scmul121666 */
/* n = 5 (from "5") */
/* s-c = 2^255 - [(1, 19)] (from "2^255 - 19") */
/* machine_wordsize = 64 (from "64") */

/* Computed values: */
/* carry_chain = [0, 1, 2, 3, 4, 0, 1] */



/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 *   in1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
void fiat_25519_carry_mul(uintptr_t in0, uintptr_t in1, uintptr_t out0) {
  uintptr_t x4, x3, x2, x1, x9, x8, x7, x6, x0, x5, x16, x22, x61, x23, x62, x17, x60, x26, x65, x27, x66, x63, x64, x28, x69, x29, x70, x67, x68, x58, x73, x59, x74, x71, x75, x72, x30, x32, x79, x33, x80, x31, x78, x36, x83, x37, x84, x81, x82, x42, x87, x43, x88, x85, x86, x50, x91, x51, x92, x89, x10, x34, x95, x35, x96, x11, x94, x38, x99, x39, x100, x97, x98, x44, x103, x45, x104, x101, x102, x52, x107, x53, x108, x105, x12, x18, x111, x19, x112, x13, x110, x40, x115, x41, x116, x113, x114, x46, x119, x47, x120, x117, x118, x54, x123, x55, x124, x121, x14, x20, x127, x21, x128, x15, x126, x24, x131, x25, x132, x129, x130, x48, x135, x49, x136, x133, x134, x56, x139, x57, x140, x137, x138, x76, x143, x141, x144, x142, x122, x145, x148, x125, x149, x147, x106, x150, x153, x109, x154, x152, x90, x155, x158, x93, x159, x157, x160, x77, x162, x163, x164, x146, x166, x167, x151, x165, x168, x169, x156, x161, x170, x171, x172, x173, x174;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  /*skip*/
  x5 = *(uintptr_t*)((in1)+((uintptr_t)0ULL));
  x6 = *(uintptr_t*)((in1)+((uintptr_t)8ULL));
  x7 = *(uintptr_t*)((in1)+((uintptr_t)16ULL));
  x8 = *(uintptr_t*)((in1)+((uintptr_t)24ULL));
  x9 = *(uintptr_t*)((in1)+((uintptr_t)32ULL));
  /*skip*/
  /*skip*/
  x10 = (x4)*((x9)*((uintptr_t)19ULL));
  x11 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x9)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x4)*((x9)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x12 = (x4)*((x8)*((uintptr_t)19ULL));
  x13 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x8)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x4)*((x8)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x14 = (x4)*((x7)*((uintptr_t)19ULL));
  x15 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x7)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x4)*((x7)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x16 = (x4)*((x6)*((uintptr_t)19ULL));
  x17 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*((x6)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x4)*((x6)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x18 = (x3)*((x9)*((uintptr_t)19ULL));
  x19 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*((x9)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x3)*((x9)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x20 = (x3)*((x8)*((uintptr_t)19ULL));
  x21 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*((x8)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x3)*((x8)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x22 = (x3)*((x7)*((uintptr_t)19ULL));
  x23 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*((x7)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x3)*((x7)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x24 = (x2)*((x9)*((uintptr_t)19ULL));
  x25 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*((x9)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x2)*((x9)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x26 = (x2)*((x8)*((uintptr_t)19ULL));
  x27 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*((x8)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x2)*((x8)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x28 = (x1)*((x9)*((uintptr_t)19ULL));
  x29 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*((x9)*((uintptr_t)19ULL)))>>32 : ((__uint128_t)(x1)*((x9)*((uintptr_t)19ULL)))>>64 /* TODO this has not been tested */;
  x30 = (x4)*(x5);
  x31 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*(x5))>>32 : ((__uint128_t)(x4)*(x5))>>64 /* TODO this has not been tested */;
  x32 = (x3)*(x6);
  x33 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x6))>>32 : ((__uint128_t)(x3)*(x6))>>64 /* TODO this has not been tested */;
  x34 = (x3)*(x5);
  x35 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x5))>>32 : ((__uint128_t)(x3)*(x5))>>64 /* TODO this has not been tested */;
  x36 = (x2)*(x7);
  x37 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x7))>>32 : ((__uint128_t)(x2)*(x7))>>64 /* TODO this has not been tested */;
  x38 = (x2)*(x6);
  x39 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x6))>>32 : ((__uint128_t)(x2)*(x6))>>64 /* TODO this has not been tested */;
  x40 = (x2)*(x5);
  x41 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x5))>>32 : ((__uint128_t)(x2)*(x5))>>64 /* TODO this has not been tested */;
  x42 = (x1)*(x8);
  x43 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x8))>>32 : ((__uint128_t)(x1)*(x8))>>64 /* TODO this has not been tested */;
  x44 = (x1)*(x7);
  x45 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x7))>>32 : ((__uint128_t)(x1)*(x7))>>64 /* TODO this has not been tested */;
  x46 = (x1)*(x6);
  x47 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x6))>>32 : ((__uint128_t)(x1)*(x6))>>64 /* TODO this has not been tested */;
  x48 = (x1)*(x5);
  x49 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x5))>>32 : ((__uint128_t)(x1)*(x5))>>64 /* TODO this has not been tested */;
  x50 = (x0)*(x9);
  x51 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x9))>>32 : ((__uint128_t)(x0)*(x9))>>64 /* TODO this has not been tested */;
  x52 = (x0)*(x8);
  x53 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x8))>>32 : ((__uint128_t)(x0)*(x8))>>64 /* TODO this has not been tested */;
  x54 = (x0)*(x7);
  x55 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x7))>>32 : ((__uint128_t)(x0)*(x7))>>64 /* TODO this has not been tested */;
  x56 = (x0)*(x6);
  x57 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x6))>>32 : ((__uint128_t)(x0)*(x6))>>64 /* TODO this has not been tested */;
  x58 = (x0)*(x5);
  x59 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x5))>>32 : ((__uint128_t)(x0)*(x5))>>64 /* TODO this has not been tested */;
  x60 = (x22)+(x16);
  x61 = (x60)<(x22);
  x62 = (x61)+(x23);
  x63 = (x62)+(x17);
  x64 = (x26)+(x60);
  x65 = (x64)<(x26);
  x66 = (x65)+(x27);
  x67 = (x66)+(x63);
  x68 = (x28)+(x64);
  x69 = (x68)<(x28);
  x70 = (x69)+(x29);
  x71 = (x70)+(x67);
  x72 = (x58)+(x68);
  x73 = (x72)<(x58);
  x74 = (x73)+(x59);
  x75 = (x74)+(x71);
  x76 = ((x72)>>((uintptr_t)51ULL))|((x75)<<((uintptr_t)13ULL));
  x77 = (x72)&((uintptr_t)2251799813685247ULL);
  x78 = (x32)+(x30);
  x79 = (x78)<(x32);
  x80 = (x79)+(x33);
  x81 = (x80)+(x31);
  x82 = (x36)+(x78);
  x83 = (x82)<(x36);
  x84 = (x83)+(x37);
  x85 = (x84)+(x81);
  x86 = (x42)+(x82);
  x87 = (x86)<(x42);
  x88 = (x87)+(x43);
  x89 = (x88)+(x85);
  x90 = (x50)+(x86);
  x91 = (x90)<(x50);
  x92 = (x91)+(x51);
  x93 = (x92)+(x89);
  x94 = (x34)+(x10);
  x95 = (x94)<(x34);
  x96 = (x95)+(x35);
  x97 = (x96)+(x11);
  x98 = (x38)+(x94);
  x99 = (x98)<(x38);
  x100 = (x99)+(x39);
  x101 = (x100)+(x97);
  x102 = (x44)+(x98);
  x103 = (x102)<(x44);
  x104 = (x103)+(x45);
  x105 = (x104)+(x101);
  x106 = (x52)+(x102);
  x107 = (x106)<(x52);
  x108 = (x107)+(x53);
  x109 = (x108)+(x105);
  x110 = (x18)+(x12);
  x111 = (x110)<(x18);
  x112 = (x111)+(x19);
  x113 = (x112)+(x13);
  x114 = (x40)+(x110);
  x115 = (x114)<(x40);
  x116 = (x115)+(x41);
  x117 = (x116)+(x113);
  x118 = (x46)+(x114);
  x119 = (x118)<(x46);
  x120 = (x119)+(x47);
  x121 = (x120)+(x117);
  x122 = (x54)+(x118);
  x123 = (x122)<(x54);
  x124 = (x123)+(x55);
  x125 = (x124)+(x121);
  x126 = (x20)+(x14);
  x127 = (x126)<(x20);
  x128 = (x127)+(x21);
  x129 = (x128)+(x15);
  x130 = (x24)+(x126);
  x131 = (x130)<(x24);
  x132 = (x131)+(x25);
  x133 = (x132)+(x129);
  x134 = (x48)+(x130);
  x135 = (x134)<(x48);
  x136 = (x135)+(x49);
  x137 = (x136)+(x133);
  x138 = (x56)+(x134);
  x139 = (x138)<(x56);
  x140 = (x139)+(x57);
  x141 = (x140)+(x137);
  x142 = (x76)+(x138);
  x143 = (x142)<(x76);
  x144 = (x143)+(x141);
  x145 = ((x142)>>((uintptr_t)51ULL))|((x144)<<((uintptr_t)13ULL));
  x146 = (x142)&((uintptr_t)2251799813685247ULL);
  x147 = (x145)+(x122);
  x148 = (x147)<(x145);
  x149 = (x148)+(x125);
  x150 = ((x147)>>((uintptr_t)51ULL))|((x149)<<((uintptr_t)13ULL));
  x151 = (x147)&((uintptr_t)2251799813685247ULL);
  x152 = (x150)+(x106);
  x153 = (x152)<(x150);
  x154 = (x153)+(x109);
  x155 = ((x152)>>((uintptr_t)51ULL))|((x154)<<((uintptr_t)13ULL));
  x156 = (x152)&((uintptr_t)2251799813685247ULL);
  x157 = (x155)+(x90);
  x158 = (x157)<(x155);
  x159 = (x158)+(x93);
  x160 = ((x157)>>((uintptr_t)51ULL))|((x159)<<((uintptr_t)13ULL));
  x161 = (x157)&((uintptr_t)2251799813685247ULL);
  x162 = (x160)*((uintptr_t)19ULL);
  x163 = (x77)+(x162);
  x164 = (x163)>>((uintptr_t)51ULL);
  x165 = (x163)&((uintptr_t)2251799813685247ULL);
  x166 = (x164)+(x146);
  x167 = (x166)>>((uintptr_t)51ULL);
  x168 = (x166)&((uintptr_t)2251799813685247ULL);
  x169 = (x167)+(x151);
  x170 = x165;
  x171 = x168;
  x172 = x169;
  x173 = x156;
  x174 = x161;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x170;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x171;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x172;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x173;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x174;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
void fiat_25519_carry_square(uintptr_t in0, uintptr_t out0) {
  uintptr_t x4, x5, x3, x8, x9, x2, x6, x1, x7, x10, x11, x12, x0, x21, x25, x44, x26, x45, x22, x43, x41, x48, x42, x49, x46, x50, x47, x23, x27, x54, x28, x55, x24, x53, x33, x58, x34, x59, x56, x13, x29, x62, x30, x63, x14, x61, x35, x66, x36, x67, x64, x15, x31, x70, x32, x71, x16, x69, x37, x74, x38, x75, x72, x17, x19, x78, x20, x79, x18, x77, x39, x82, x40, x83, x80, x81, x51, x86, x84, x87, x85, x73, x88, x91, x76, x92, x90, x65, x93, x96, x68, x97, x95, x57, x98, x101, x60, x102, x100, x103, x52, x105, x106, x107, x89, x109, x110, x94, x108, x111, x112, x99, x104, x113, x114, x115, x116, x117;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  /*skip*/
  /*skip*/
  x5 = (x4)*((uintptr_t)19ULL);
  x6 = (x5)*((uintptr_t)2ULL);
  x7 = (x4)*((uintptr_t)2ULL);
  x8 = (x3)*((uintptr_t)19ULL);
  x9 = (x8)*((uintptr_t)2ULL);
  x10 = (x3)*((uintptr_t)2ULL);
  x11 = (x2)*((uintptr_t)2ULL);
  x12 = (x1)*((uintptr_t)2ULL);
  x13 = (x4)*(x5);
  x14 = sizeof(intptr_t) == 4 ? ((uint64_t)(x4)*(x5))>>32 : ((__uint128_t)(x4)*(x5))>>64 /* TODO this has not been tested */;
  x15 = (x3)*(x6);
  x16 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x6))>>32 : ((__uint128_t)(x3)*(x6))>>64 /* TODO this has not been tested */;
  x17 = (x3)*(x8);
  x18 = sizeof(intptr_t) == 4 ? ((uint64_t)(x3)*(x8))>>32 : ((__uint128_t)(x3)*(x8))>>64 /* TODO this has not been tested */;
  x19 = (x2)*(x6);
  x20 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x6))>>32 : ((__uint128_t)(x2)*(x6))>>64 /* TODO this has not been tested */;
  x21 = (x2)*(x9);
  x22 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x9))>>32 : ((__uint128_t)(x2)*(x9))>>64 /* TODO this has not been tested */;
  x23 = (x2)*(x2);
  x24 = sizeof(intptr_t) == 4 ? ((uint64_t)(x2)*(x2))>>32 : ((__uint128_t)(x2)*(x2))>>64 /* TODO this has not been tested */;
  x25 = (x1)*(x6);
  x26 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x6))>>32 : ((__uint128_t)(x1)*(x6))>>64 /* TODO this has not been tested */;
  x27 = (x1)*(x10);
  x28 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x10))>>32 : ((__uint128_t)(x1)*(x10))>>64 /* TODO this has not been tested */;
  x29 = (x1)*(x11);
  x30 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x11))>>32 : ((__uint128_t)(x1)*(x11))>>64 /* TODO this has not been tested */;
  x31 = (x1)*(x1);
  x32 = sizeof(intptr_t) == 4 ? ((uint64_t)(x1)*(x1))>>32 : ((__uint128_t)(x1)*(x1))>>64 /* TODO this has not been tested */;
  x33 = (x0)*(x7);
  x34 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x7))>>32 : ((__uint128_t)(x0)*(x7))>>64 /* TODO this has not been tested */;
  x35 = (x0)*(x10);
  x36 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x10))>>32 : ((__uint128_t)(x0)*(x10))>>64 /* TODO this has not been tested */;
  x37 = (x0)*(x11);
  x38 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x11))>>32 : ((__uint128_t)(x0)*(x11))>>64 /* TODO this has not been tested */;
  x39 = (x0)*(x12);
  x40 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x12))>>32 : ((__uint128_t)(x0)*(x12))>>64 /* TODO this has not been tested */;
  x41 = (x0)*(x0);
  x42 = sizeof(intptr_t) == 4 ? ((uint64_t)(x0)*(x0))>>32 : ((__uint128_t)(x0)*(x0))>>64 /* TODO this has not been tested */;
  x43 = (x25)+(x21);
  x44 = (x43)<(x25);
  x45 = (x44)+(x26);
  x46 = (x45)+(x22);
  x47 = (x41)+(x43);
  x48 = (x47)<(x41);
  x49 = (x48)+(x42);
  x50 = (x49)+(x46);
  x51 = ((x47)>>((uintptr_t)51ULL))|((x50)<<((uintptr_t)13ULL));
  x52 = (x47)&((uintptr_t)2251799813685247ULL);
  x53 = (x27)+(x23);
  x54 = (x53)<(x27);
  x55 = (x54)+(x28);
  x56 = (x55)+(x24);
  x57 = (x33)+(x53);
  x58 = (x57)<(x33);
  x59 = (x58)+(x34);
  x60 = (x59)+(x56);
  x61 = (x29)+(x13);
  x62 = (x61)<(x29);
  x63 = (x62)+(x30);
  x64 = (x63)+(x14);
  x65 = (x35)+(x61);
  x66 = (x65)<(x35);
  x67 = (x66)+(x36);
  x68 = (x67)+(x64);
  x69 = (x31)+(x15);
  x70 = (x69)<(x31);
  x71 = (x70)+(x32);
  x72 = (x71)+(x16);
  x73 = (x37)+(x69);
  x74 = (x73)<(x37);
  x75 = (x74)+(x38);
  x76 = (x75)+(x72);
  x77 = (x19)+(x17);
  x78 = (x77)<(x19);
  x79 = (x78)+(x20);
  x80 = (x79)+(x18);
  x81 = (x39)+(x77);
  x82 = (x81)<(x39);
  x83 = (x82)+(x40);
  x84 = (x83)+(x80);
  x85 = (x51)+(x81);
  x86 = (x85)<(x51);
  x87 = (x86)+(x84);
  x88 = ((x85)>>((uintptr_t)51ULL))|((x87)<<((uintptr_t)13ULL));
  x89 = (x85)&((uintptr_t)2251799813685247ULL);
  x90 = (x88)+(x73);
  x91 = (x90)<(x88);
  x92 = (x91)+(x76);
  x93 = ((x90)>>((uintptr_t)51ULL))|((x92)<<((uintptr_t)13ULL));
  x94 = (x90)&((uintptr_t)2251799813685247ULL);
  x95 = (x93)+(x65);
  x96 = (x95)<(x93);
  x97 = (x96)+(x68);
  x98 = ((x95)>>((uintptr_t)51ULL))|((x97)<<((uintptr_t)13ULL));
  x99 = (x95)&((uintptr_t)2251799813685247ULL);
  x100 = (x98)+(x57);
  x101 = (x100)<(x98);
  x102 = (x101)+(x60);
  x103 = ((x100)>>((uintptr_t)51ULL))|((x102)<<((uintptr_t)13ULL));
  x104 = (x100)&((uintptr_t)2251799813685247ULL);
  x105 = (x103)*((uintptr_t)19ULL);
  x106 = (x52)+(x105);
  x107 = (x106)>>((uintptr_t)51ULL);
  x108 = (x106)&((uintptr_t)2251799813685247ULL);
  x109 = (x107)+(x89);
  x110 = (x109)>>((uintptr_t)51ULL);
  x111 = (x109)&((uintptr_t)2251799813685247ULL);
  x112 = (x110)+(x94);
  x113 = x108;
  x114 = x111;
  x115 = x112;
  x116 = x99;
  x117 = x104;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x113;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x114;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x115;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x116;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x117;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
void fiat_25519_carry(uintptr_t in0, uintptr_t out0) {
  uintptr_t x0, x1, x2, x3, x4, x5, x6, x10, x11, x7, x8, x9, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  /*skip*/
  /*skip*/
  x5 = x0;
  x6 = ((x5)>>((uintptr_t)51ULL))+(x1);
  x7 = ((x6)>>((uintptr_t)51ULL))+(x2);
  x8 = ((x7)>>((uintptr_t)51ULL))+(x3);
  x9 = ((x8)>>((uintptr_t)51ULL))+(x4);
  x10 = ((x5)&((uintptr_t)2251799813685247ULL))+(((x9)>>((uintptr_t)51ULL))*((uintptr_t)19ULL));
  x11 = ((x10)>>((uintptr_t)51ULL))+((x6)&((uintptr_t)2251799813685247ULL));
  x12 = (x10)&((uintptr_t)2251799813685247ULL);
  x13 = (x11)&((uintptr_t)2251799813685247ULL);
  x14 = ((x11)>>((uintptr_t)51ULL))+((x7)&((uintptr_t)2251799813685247ULL));
  x15 = (x8)&((uintptr_t)2251799813685247ULL);
  x16 = (x9)&((uintptr_t)2251799813685247ULL);
  x17 = x12;
  x18 = x13;
  x19 = x14;
  x20 = x15;
  x21 = x16;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x17;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x18;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x19;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x20;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x21;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 *   in1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 */
void fiat_25519_add(uintptr_t in0, uintptr_t in1, uintptr_t out0) {
  uintptr_t x0, x5, x1, x6, x2, x7, x3, x8, x4, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  /*skip*/
  x5 = *(uintptr_t*)((in1)+((uintptr_t)0ULL));
  x6 = *(uintptr_t*)((in1)+((uintptr_t)8ULL));
  x7 = *(uintptr_t*)((in1)+((uintptr_t)16ULL));
  x8 = *(uintptr_t*)((in1)+((uintptr_t)24ULL));
  x9 = *(uintptr_t*)((in1)+((uintptr_t)32ULL));
  /*skip*/
  /*skip*/
  x10 = (x0)+(x5);
  x11 = (x1)+(x6);
  x12 = (x2)+(x7);
  x13 = (x3)+(x8);
  x14 = (x4)+(x9);
  x15 = x10;
  x16 = x11;
  x17 = x12;
  x18 = x13;
  x19 = x14;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x15;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x16;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x17;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x18;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x19;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 *   in1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 */
void fiat_25519_sub(uintptr_t in0, uintptr_t in1, uintptr_t out0) {
  uintptr_t x0, x5, x1, x6, x2, x7, x3, x8, x4, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  /*skip*/
  x5 = *(uintptr_t*)((in1)+((uintptr_t)0ULL));
  x6 = *(uintptr_t*)((in1)+((uintptr_t)8ULL));
  x7 = *(uintptr_t*)((in1)+((uintptr_t)16ULL));
  x8 = *(uintptr_t*)((in1)+((uintptr_t)24ULL));
  x9 = *(uintptr_t*)((in1)+((uintptr_t)32ULL));
  /*skip*/
  /*skip*/
  x10 = (((uintptr_t)4503599627370458ULL)+(x0))-(x5);
  x11 = (((uintptr_t)4503599627370494ULL)+(x1))-(x6);
  x12 = (((uintptr_t)4503599627370494ULL)+(x2))-(x7);
  x13 = (((uintptr_t)4503599627370494ULL)+(x3))-(x8);
  x14 = (((uintptr_t)4503599627370494ULL)+(x4))-(x9);
  x15 = x10;
  x16 = x11;
  x17 = x12;
  x18 = x13;
  x19 = x14;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x15;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x16;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x17;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x18;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x19;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 */
void fiat_25519_opp(uintptr_t in0, uintptr_t out0) {
  uintptr_t x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  /*skip*/
  /*skip*/
  x5 = ((uintptr_t)4503599627370458ULL)-(x0);
  x6 = ((uintptr_t)4503599627370494ULL)-(x1);
  x7 = ((uintptr_t)4503599627370494ULL)-(x2);
  x8 = ((uintptr_t)4503599627370494ULL)-(x3);
  x9 = ((uintptr_t)4503599627370494ULL)-(x4);
  x10 = x5;
  x11 = x6;
  x12 = x7;
  x13 = x8;
  x14 = x9;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x10;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x11;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x12;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x13;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x14;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x7f]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
void fiat_25519_from_bytes(uintptr_t in0, uintptr_t out0) {
  uintptr_t x31, x30, x29, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19, x18, x17, x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0, x63, x62, x61, x60, x59, x58, x57, x64, x37, x36, x35, x34, x33, x32, x43, x42, x41, x40, x39, x38, x50, x49, x48, x47, x46, x45, x44, x56, x55, x54, x53, x52, x51, x65, x70, x71, x72, x69, x74, x75, x68, x77, x78, x67, x66, x73, x76, x79, x80, x81, x82, x83, x84, x85;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  x5 = *(uintptr_t*)((in0)+((uintptr_t)40ULL));
  x6 = *(uintptr_t*)((in0)+((uintptr_t)48ULL));
  x7 = *(uintptr_t*)((in0)+((uintptr_t)56ULL));
  x8 = *(uintptr_t*)((in0)+((uintptr_t)64ULL));
  x9 = *(uintptr_t*)((in0)+((uintptr_t)72ULL));
  x10 = *(uintptr_t*)((in0)+((uintptr_t)80ULL));
  x11 = *(uintptr_t*)((in0)+((uintptr_t)88ULL));
  x12 = *(uintptr_t*)((in0)+((uintptr_t)96ULL));
  x13 = *(uintptr_t*)((in0)+((uintptr_t)104ULL));
  x14 = *(uintptr_t*)((in0)+((uintptr_t)112ULL));
  x15 = *(uintptr_t*)((in0)+((uintptr_t)120ULL));
  x16 = *(uintptr_t*)((in0)+((uintptr_t)128ULL));
  x17 = *(uintptr_t*)((in0)+((uintptr_t)136ULL));
  x18 = *(uintptr_t*)((in0)+((uintptr_t)144ULL));
  x19 = *(uintptr_t*)((in0)+((uintptr_t)152ULL));
  x20 = *(uintptr_t*)((in0)+((uintptr_t)160ULL));
  x21 = *(uintptr_t*)((in0)+((uintptr_t)168ULL));
  x22 = *(uintptr_t*)((in0)+((uintptr_t)176ULL));
  x23 = *(uintptr_t*)((in0)+((uintptr_t)184ULL));
  x24 = *(uintptr_t*)((in0)+((uintptr_t)192ULL));
  x25 = *(uintptr_t*)((in0)+((uintptr_t)200ULL));
  x26 = *(uintptr_t*)((in0)+((uintptr_t)208ULL));
  x27 = *(uintptr_t*)((in0)+((uintptr_t)216ULL));
  x28 = *(uintptr_t*)((in0)+((uintptr_t)224ULL));
  x29 = *(uintptr_t*)((in0)+((uintptr_t)232ULL));
  x30 = *(uintptr_t*)((in0)+((uintptr_t)240ULL));
  x31 = *(uintptr_t*)((in0)+((uintptr_t)248ULL));
  /*skip*/
  /*skip*/
  x32 = (x31)<<((uintptr_t)44ULL);
  x33 = (x30)<<((uintptr_t)36ULL);
  x34 = (x29)<<((uintptr_t)28ULL);
  x35 = (x28)<<((uintptr_t)20ULL);
  x36 = (x27)<<((uintptr_t)12ULL);
  x37 = (x26)<<((uintptr_t)4ULL);
  x38 = (x25)<<((uintptr_t)47ULL);
  x39 = (x24)<<((uintptr_t)39ULL);
  x40 = (x23)<<((uintptr_t)31ULL);
  x41 = (x22)<<((uintptr_t)23ULL);
  x42 = (x21)<<((uintptr_t)15ULL);
  x43 = (x20)<<((uintptr_t)7ULL);
  x44 = (x19)<<((uintptr_t)50ULL);
  x45 = (x18)<<((uintptr_t)42ULL);
  x46 = (x17)<<((uintptr_t)34ULL);
  x47 = (x16)<<((uintptr_t)26ULL);
  x48 = (x15)<<((uintptr_t)18ULL);
  x49 = (x14)<<((uintptr_t)10ULL);
  x50 = (x13)<<((uintptr_t)2ULL);
  x51 = (x12)<<((uintptr_t)45ULL);
  x52 = (x11)<<((uintptr_t)37ULL);
  x53 = (x10)<<((uintptr_t)29ULL);
  x54 = (x9)<<((uintptr_t)21ULL);
  x55 = (x8)<<((uintptr_t)13ULL);
  x56 = (x7)<<((uintptr_t)5ULL);
  x57 = (x6)<<((uintptr_t)48ULL);
  x58 = (x5)<<((uintptr_t)40ULL);
  x59 = (x4)<<((uintptr_t)32ULL);
  x60 = (x3)<<((uintptr_t)24ULL);
  x61 = (x2)<<((uintptr_t)16ULL);
  x62 = (x1)<<((uintptr_t)8ULL);
  x63 = x0;
  x64 = (x63)+((x62)+((x61)+((x60)+((x59)+((x58)+(x57))))));
  x65 = (x64)>>((uintptr_t)51ULL);
  x66 = (x64)&((uintptr_t)2251799813685247ULL);
  x67 = (x37)+((x36)+((x35)+((x34)+((x33)+(x32)))));
  x68 = (x43)+((x42)+((x41)+((x40)+((x39)+(x38)))));
  x69 = (x50)+((x49)+((x48)+((x47)+((x46)+((x45)+(x44))))));
  x70 = (x56)+((x55)+((x54)+((x53)+((x52)+(x51)))));
  x71 = (x65)+(x70);
  x72 = (x71)>>((uintptr_t)51ULL);
  x73 = (x71)&((uintptr_t)2251799813685247ULL);
  x74 = (x72)+(x69);
  x75 = (x74)>>((uintptr_t)51ULL);
  x76 = (x74)&((uintptr_t)2251799813685247ULL);
  x77 = (x75)+(x68);
  x78 = (x77)>>((uintptr_t)51ULL);
  x79 = (x77)&((uintptr_t)2251799813685247ULL);
  x80 = (x78)+(x67);
  x81 = x66;
  x82 = x73;
  x83 = x76;
  x84 = x79;
  x85 = x80;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x81;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x82;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x83;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x84;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x85;
  /*skip*/
  return;
}


/*
 * Input Bounds:
 *   in0: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out0: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
void fiat_25519_carry_scmul_121666(uintptr_t in0, uintptr_t out0) {
  uintptr_t x4, x3, x2, x1, x0, x14, x13, x11, x15, x18, x12, x19, x17, x9, x20, x23, x10, x24, x22, x7, x25, x28, x8, x29, x27, x5, x30, x33, x6, x34, x32, x35, x16, x37, x38, x39, x21, x41, x42, x26, x40, x43, x44, x31, x36, x45, x46, x47, x48, x49;
  x0 = *(uintptr_t*)((in0)+((uintptr_t)0ULL));
  x1 = *(uintptr_t*)((in0)+((uintptr_t)8ULL));
  x2 = *(uintptr_t*)((in0)+((uintptr_t)16ULL));
  x3 = *(uintptr_t*)((in0)+((uintptr_t)24ULL));
  x4 = *(uintptr_t*)((in0)+((uintptr_t)32ULL));
  /*skip*/
  /*skip*/
  x5 = ((uintptr_t)121666ULL)*(x4);
  x6 = sizeof(intptr_t) == 4 ? ((uint64_t)((uintptr_t)121666ULL)*(x4))>>32 : ((__uint128_t)((uintptr_t)121666ULL)*(x4))>>64 /* TODO this has not been tested */;
  x7 = ((uintptr_t)121666ULL)*(x3);
  x8 = sizeof(intptr_t) == 4 ? ((uint64_t)((uintptr_t)121666ULL)*(x3))>>32 : ((__uint128_t)((uintptr_t)121666ULL)*(x3))>>64 /* TODO this has not been tested */;
  x9 = ((uintptr_t)121666ULL)*(x2);
  x10 = sizeof(intptr_t) == 4 ? ((uint64_t)((uintptr_t)121666ULL)*(x2))>>32 : ((__uint128_t)((uintptr_t)121666ULL)*(x2))>>64 /* TODO this has not been tested */;
  x11 = ((uintptr_t)121666ULL)*(x1);
  x12 = sizeof(intptr_t) == 4 ? ((uint64_t)((uintptr_t)121666ULL)*(x1))>>32 : ((__uint128_t)((uintptr_t)121666ULL)*(x1))>>64 /* TODO this has not been tested */;
  x13 = ((uintptr_t)121666ULL)*(x0);
  x14 = sizeof(intptr_t) == 4 ? ((uint64_t)((uintptr_t)121666ULL)*(x0))>>32 : ((__uint128_t)((uintptr_t)121666ULL)*(x0))>>64 /* TODO this has not been tested */;
  x15 = ((x13)>>((uintptr_t)51ULL))|((x14)<<((uintptr_t)13ULL));
  x16 = (x13)&((uintptr_t)2251799813685247ULL);
  x17 = (x15)+(x11);
  x18 = (x17)<(x15);
  x19 = (x18)+(x12);
  x20 = ((x17)>>((uintptr_t)51ULL))|((x19)<<((uintptr_t)13ULL));
  x21 = (x17)&((uintptr_t)2251799813685247ULL);
  x22 = (x20)+(x9);
  x23 = (x22)<(x20);
  x24 = (x23)+(x10);
  x25 = ((x22)>>((uintptr_t)51ULL))|((x24)<<((uintptr_t)13ULL));
  x26 = (x22)&((uintptr_t)2251799813685247ULL);
  x27 = (x25)+(x7);
  x28 = (x27)<(x25);
  x29 = (x28)+(x8);
  x30 = ((x27)>>((uintptr_t)51ULL))|((x29)<<((uintptr_t)13ULL));
  x31 = (x27)&((uintptr_t)2251799813685247ULL);
  x32 = (x30)+(x5);
  x33 = (x32)<(x30);
  x34 = (x33)+(x6);
  x35 = ((x32)>>((uintptr_t)51ULL))|((x34)<<((uintptr_t)13ULL));
  x36 = (x32)&((uintptr_t)2251799813685247ULL);
  x37 = (x35)*((uintptr_t)19ULL);
  x38 = (x16)+(x37);
  x39 = (x38)>>((uintptr_t)51ULL);
  x40 = (x38)&((uintptr_t)2251799813685247ULL);
  x41 = (x39)+(x21);
  x42 = (x41)>>((uintptr_t)51ULL);
  x43 = (x41)&((uintptr_t)2251799813685247ULL);
  x44 = (x42)+(x26);
  x45 = x40;
  x46 = x43;
  x47 = x44;
  x48 = x31;
  x49 = x36;
  /*skip*/
  *(uintptr_t*)((out0)+((uintptr_t)0ULL)) = x45;
  *(uintptr_t*)((out0)+((uintptr_t)8ULL)) = x46;
  *(uintptr_t*)((out0)+((uintptr_t)16ULL)) = x47;
  *(uintptr_t*)((out0)+((uintptr_t)24ULL)) = x48;
  *(uintptr_t*)((out0)+((uintptr_t)32ULL)) = x49;
  /*skip*/
  return;
}

