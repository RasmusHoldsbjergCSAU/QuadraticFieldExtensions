#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned char fiat_uint1;
typedef signed char fiat_int1;
typedef signed __int128 fiat_int128;
typedef unsigned __int128 fiat_uint128;


/*
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xffffffffffffffff]
 *   arg3: [0x0 ~> 0xffffffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffffffffffff]
 */
static void fiat_cmovznz_u64(uint64_t* out1, fiat_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  uint64_t x1;
  uint64_t x2;
  x1 = ((fiat_int1)(0x0 - (!(!arg1))) & UINT64_C(0xffffffffffffffff));
  x2 = ((x1 & arg3) | ((~x1) & arg2));
  *out1 = x2;
}


/*
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xffffffffffffffff]
 *   arg3: [0x0 ~> 0xffffffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_subborrowx_u64(uint64_t* out1, fiat_uint1* out2, fiat_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  fiat_int128 x1;
  uint64_t x2;
  fiat_uint1 x3;
  x1 = ((arg2 - (fiat_int128)arg1) - arg3);
  x2 = (uint64_t)(x1 & UINT64_C(0xffffffffffffffff));
  x3 = (fiat_uint1)(0x0 - (fiat_int1)(x1 >> 64));
  *out1 = x2;
  *out2 = x3;
}

/*
 * Input Bounds:
 *   arg1: [0x0 ~> 0x1]
 *   arg2: [0x0 ~> 0xffffffffffffffff]
 *   arg3: [0x0 ~> 0xffffffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffffffffffff]
 *   out2: [0x0 ~> 0x1]
 */
static void fiat_addcarryx_u64(uint64_t* out1, fiat_uint1* out2, fiat_uint1 arg1, uint64_t arg2, uint64_t arg3) {
  fiat_uint128 x1;
  uint64_t x2;
  fiat_uint1 x3;
  x1 = ((arg1 + (fiat_uint128)arg2) + arg3);
  x2 = (uint64_t)(x1 & UINT64_C(0xffffffffffffffff));
  x3 = (fiat_uint1)(x1 >> 64);
  *out1 = x2;
  *out2 = x3;
}


/*
 * Input Bounds:
 *   arg1: [0x0 ~> 0xffffffffffffffff]
 *   arg2: [0x0 ~> 0xffffffffffffffff]
 * Output Bounds:
 *   out1: [0x0 ~> 0xffffffffffffffff]
 *   out2: [0x0 ~> 0xffffffffffffffff]
 */
static void fiat_mulx_u64(uint64_t* out1, uint64_t* out2, uint64_t arg1, uint64_t arg2) {
  fiat_uint128 x1;
  uint64_t x2;
  uint64_t x3;
  x1 = ((fiat_uint128)arg1 * arg2);
  x2 = (uint64_t)(x1 & UINT64_C(0xffffffffffffffff));
  x3 = (uint64_t)(x1 >> 64);
  *out1 = x2;
  *out2 = x3;
}




/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg4: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   out2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
static void fiat_mulFp2_(uint64_t out1[2], uint64_t out2[2], const uint64_t arg1[2], const uint64_t arg2[2], const uint64_t arg3[2], const uint64_t arg4[2]) {
  uint64_t x1;
  uint64_t x2;
  uint64_t x3;
  uint64_t x4;
  uint64_t x5;
  uint64_t x6;
  uint64_t x7;
  fiat_uint1 x8;
  uint64_t x9;
  uint64_t x10;
  uint64_t x11;
  uint64_t x12;
  uint64_t x13;
  uint64_t x14;
  fiat_uint1 x15;
  uint64_t x16;
  uint64_t x17;
  fiat_uint1 x18;
  uint64_t x19;
  fiat_uint1 x20;
  uint64_t x21;
  fiat_uint1 x22;
  uint64_t x23;
  uint64_t x24;
  uint64_t x25;
  uint64_t x26;
  uint64_t x27;
  fiat_uint1 x28;
  uint64_t x29;
  uint64_t x30;
  fiat_uint1 x31;
  uint64_t x32;
  fiat_uint1 x33;
  uint64_t x34;
  fiat_uint1 x35;
  uint64_t x36;
  uint64_t x37;
  uint64_t x38;
  uint64_t x39;
  uint64_t x40;
  fiat_uint1 x41;
  uint64_t x42;
  uint64_t x43;
  fiat_uint1 x44;
  uint64_t x45;
  fiat_uint1 x46;
  uint64_t x47;
  fiat_uint1 x48;
  uint64_t x49;
  uint64_t x50;
  fiat_uint1 x51;
  uint64_t x52;
  fiat_uint1 x53;
  uint64_t x54;
  fiat_uint1 x55;
  uint64_t x56;
  uint64_t x57;
  uint64_t x58;
  uint64_t x59;
  uint64_t x60;
  uint64_t x61;
  uint64_t x62;
  uint64_t x63;
  uint64_t x64;
  fiat_uint1 x65;
  uint64_t x66;
  uint64_t x67;
  uint64_t x68;
  uint64_t x69;
  uint64_t x70;
  uint64_t x71;
  fiat_uint1 x72;
  uint64_t x73;
  uint64_t x74;
  fiat_uint1 x75;
  uint64_t x76;
  fiat_uint1 x77;
  uint64_t x78;
  fiat_uint1 x79;
  uint64_t x80;
  uint64_t x81;
  uint64_t x82;
  uint64_t x83;
  uint64_t x84;
  fiat_uint1 x85;
  uint64_t x86;
  uint64_t x87;
  fiat_uint1 x88;
  uint64_t x89;
  fiat_uint1 x90;
  uint64_t x91;
  fiat_uint1 x92;
  uint64_t x93;
  uint64_t x94;
  uint64_t x95;
  uint64_t x96;
  uint64_t x97;
  fiat_uint1 x98;
  uint64_t x99;
  uint64_t x100;
  fiat_uint1 x101;
  uint64_t x102;
  fiat_uint1 x103;
  uint64_t x104;
  fiat_uint1 x105;
  uint64_t x106;
  uint64_t x107;
  fiat_uint1 x108;
  uint64_t x109;
  fiat_uint1 x110;
  uint64_t x111;
  fiat_uint1 x112;
  uint64_t x113;
  uint64_t x114;
  uint64_t x115;
  fiat_uint1 x116;
  uint64_t x117;
  fiat_uint1 x118;
  uint64_t x119;
  fiat_uint1 x120;
  uint64_t x121;
  fiat_uint1 x122;
  uint64_t x123;
  fiat_uint1 x124;
  uint64_t x125;
  uint64_t x126;
  uint64_t x127;
  fiat_uint1 x128;
  uint64_t x129;
  fiat_uint1 x130;
  uint64_t x131;
  fiat_uint1 x132;
  uint64_t x133;
  fiat_uint1 x134;
  uint64_t x135;
  fiat_uint1 x136;
  uint64_t x137;
  uint64_t x138;
  uint64_t x139;
  uint64_t x140;
  uint64_t x141;
  uint64_t x142;
  uint64_t x143;
  fiat_uint1 x144;
  uint64_t x145;
  uint64_t x146;
  uint64_t x147;
  uint64_t x148;
  uint64_t x149;
  uint64_t x150;
  fiat_uint1 x151;
  uint64_t x152;
  uint64_t x153;
  fiat_uint1 x154;
  uint64_t x155;
  fiat_uint1 x156;
  uint64_t x157;
  fiat_uint1 x158;
  uint64_t x159;
  uint64_t x160;
  uint64_t x161;
  uint64_t x162;
  uint64_t x163;
  fiat_uint1 x164;
  uint64_t x165;
  uint64_t x166;
  fiat_uint1 x167;
  uint64_t x168;
  fiat_uint1 x169;
  uint64_t x170;
  fiat_uint1 x171;
  uint64_t x172;
  uint64_t x173;
  uint64_t x174;
  uint64_t x175;
  uint64_t x176;
  fiat_uint1 x177;
  uint64_t x178;
  uint64_t x179;
  fiat_uint1 x180;
  uint64_t x181;
  fiat_uint1 x182;
  uint64_t x183;
  fiat_uint1 x184;
  uint64_t x185;
  uint64_t x186;
  fiat_uint1 x187;
  uint64_t x188;
  fiat_uint1 x189;
  uint64_t x190;
  fiat_uint1 x191;
  uint64_t x192;
  uint64_t x193;
  uint64_t x194;
  fiat_uint1 x195;
  uint64_t x196;
  fiat_uint1 x197;
  uint64_t x198;
  uint64_t x199;
  fiat_uint1 x200;
  uint64_t x201;
  fiat_uint1 x202;
  uint64_t x203;
  fiat_uint1 x204;
  uint64_t x205;
  fiat_uint1 x206;
  uint64_t x207;
  uint64_t x208;
  fiat_uint1 x209;
  uint64_t x210;
  fiat_uint1 x211;
  uint64_t x212;
  fiat_uint1 x213;
  uint64_t x214;
  fiat_uint1 x215;
  uint64_t x216;
  uint64_t x217;
  fiat_uint1 x218;
  uint64_t x219;
  fiat_uint1 x220;
  x1 = (arg1[1]);
  x2 = (arg1[0]);
  fiat_mulx_u64(&x3, &x4, x2, (arg3[1]));
  fiat_mulx_u64(&x5, &x6, x2, (arg3[0]));
  fiat_addcarryx_u64(&x7, &x8, 0x0, x6, x3);
  x9 = (x8 + x4);
  fiat_mulx_u64(&x10, &x11, x5, UINT64_C(0x7fffffffffffffff));
  fiat_mulx_u64(&x12, &x13, x5, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x14, &x15, 0x0, x13, x10);
  x16 = (x15 + x11);
  fiat_addcarryx_u64(&x17, &x18, 0x0, x5, x12);
  fiat_addcarryx_u64(&x19, &x20, x18, x7, x14);
  fiat_addcarryx_u64(&x21, &x22, x20, x9, x16);
  fiat_mulx_u64(&x23, &x24, x1, (arg3[1]));
  fiat_mulx_u64(&x25, &x26, x1, (arg3[0]));
  fiat_addcarryx_u64(&x27, &x28, 0x0, x26, x23);
  x29 = (x28 + x24);
  fiat_addcarryx_u64(&x30, &x31, 0x0, x19, x25);
  fiat_addcarryx_u64(&x32, &x33, x31, x21, x27);
  fiat_addcarryx_u64(&x34, &x35, x33, x22, x29);
  fiat_mulx_u64(&x36, &x37, x30, UINT64_C(0x7fffffffffffffff));
  fiat_mulx_u64(&x38, &x39, x30, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x40, &x41, 0x0, x39, x36);
  x42 = (x41 + x37);
  fiat_addcarryx_u64(&x43, &x44, 0x0, x30, x38);
  fiat_addcarryx_u64(&x45, &x46, x44, x32, x40);
  fiat_addcarryx_u64(&x47, &x48, x46, x34, x42);
  x49 = ((uint64_t)x48 + x35);
  fiat_subborrowx_u64(&x50, &x51, 0x0, x45, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x52, &x53, x51, x47, UINT64_C(0x7fffffffffffffff));
  fiat_subborrowx_u64(&x54, &x55, x53, x49, 0x0);
  fiat_cmovznz_u64(&x56, x55, x50, x45);
  fiat_cmovznz_u64(&x57, x55, x52, x47);
  x58 = (arg2[1]);
  x59 = (arg2[0]);
  fiat_mulx_u64(&x60, &x61, x59, (arg4[1]));
  fiat_mulx_u64(&x62, &x63, x59, (arg4[0]));
  fiat_addcarryx_u64(&x64, &x65, 0x0, x63, x60);
  x66 = (x65 + x61);
  fiat_mulx_u64(&x67, &x68, x62, UINT64_C(0x7fffffffffffffff));
  fiat_mulx_u64(&x69, &x70, x62, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x71, &x72, 0x0, x70, x67);
  x73 = (x72 + x68);
  fiat_addcarryx_u64(&x74, &x75, 0x0, x62, x69);
  fiat_addcarryx_u64(&x76, &x77, x75, x64, x71);
  fiat_addcarryx_u64(&x78, &x79, x77, x66, x73);
  fiat_mulx_u64(&x80, &x81, x58, (arg4[1]));
  fiat_mulx_u64(&x82, &x83, x58, (arg4[0]));
  fiat_addcarryx_u64(&x84, &x85, 0x0, x83, x80);
  x86 = (x85 + x81);
  fiat_addcarryx_u64(&x87, &x88, 0x0, x76, x82);
  fiat_addcarryx_u64(&x89, &x90, x88, x78, x84);
  fiat_addcarryx_u64(&x91, &x92, x90, x79, x86);
  fiat_mulx_u64(&x93, &x94, x87, UINT64_C(0x7fffffffffffffff));
  fiat_mulx_u64(&x95, &x96, x87, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x97, &x98, 0x0, x96, x93);
  x99 = (x98 + x94);
  fiat_addcarryx_u64(&x100, &x101, 0x0, x87, x95);
  fiat_addcarryx_u64(&x102, &x103, x101, x89, x97);
  fiat_addcarryx_u64(&x104, &x105, x103, x91, x99);
  x106 = ((uint64_t)x105 + x92);
  fiat_subborrowx_u64(&x107, &x108, 0x0, x102, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x109, &x110, x108, x104, UINT64_C(0x7fffffffffffffff));
  fiat_subborrowx_u64(&x111, &x112, x110, x106, 0x0);
  fiat_cmovznz_u64(&x113, x112, x107, x102);
  fiat_cmovznz_u64(&x114, x112, x109, x104);
  fiat_addcarryx_u64(&x115, &x116, 0x0, (arg1[0]), (arg2[0]));
  fiat_addcarryx_u64(&x117, &x118, x116, (arg1[1]), (arg2[1]));
  fiat_subborrowx_u64(&x119, &x120, 0x0, x115, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x121, &x122, x120, x117, UINT64_C(0x7fffffffffffffff));
  fiat_subborrowx_u64(&x123, &x124, x122, x118, 0x0);
  fiat_cmovznz_u64(&x125, x124, x119, x115);
  fiat_cmovznz_u64(&x126, x124, x121, x117);
  fiat_addcarryx_u64(&x127, &x128, 0x0, (arg3[0]), (arg4[0]));
  fiat_addcarryx_u64(&x129, &x130, x128, (arg3[1]), (arg4[1]));
  fiat_subborrowx_u64(&x131, &x132, 0x0, x127, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x133, &x134, x132, x129, UINT64_C(0x7fffffffffffffff));
  fiat_subborrowx_u64(&x135, &x136, x134, x130, 0x0);
  fiat_cmovznz_u64(&x137, x136, x131, x127);
  fiat_cmovznz_u64(&x138, x136, x133, x129);
  fiat_mulx_u64(&x139, &x140, x125, x138);
  fiat_mulx_u64(&x141, &x142, x125, x137);
  fiat_addcarryx_u64(&x143, &x144, 0x0, x142, x139);
  x145 = (x144 + x140);
  fiat_mulx_u64(&x146, &x147, x141, UINT64_C(0x7fffffffffffffff));
  fiat_mulx_u64(&x148, &x149, x141, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x150, &x151, 0x0, x149, x146);
  x152 = (x151 + x147);
  fiat_addcarryx_u64(&x153, &x154, 0x0, x141, x148);
  fiat_addcarryx_u64(&x155, &x156, x154, x143, x150);
  fiat_addcarryx_u64(&x157, &x158, x156, x145, x152);
  fiat_mulx_u64(&x159, &x160, x126, x138);
  fiat_mulx_u64(&x161, &x162, x126, x137);
  fiat_addcarryx_u64(&x163, &x164, 0x0, x162, x159);
  x165 = (x164 + x160);
  fiat_addcarryx_u64(&x166, &x167, 0x0, x155, x161);
  fiat_addcarryx_u64(&x168, &x169, x167, x157, x163);
  fiat_addcarryx_u64(&x170, &x171, x169, x158, x165);
  fiat_mulx_u64(&x172, &x173, x166, UINT64_C(0x7fffffffffffffff));
  fiat_mulx_u64(&x174, &x175, x166, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x176, &x177, 0x0, x175, x172);
  x178 = (x177 + x173);
  fiat_addcarryx_u64(&x179, &x180, 0x0, x166, x174);
  fiat_addcarryx_u64(&x181, &x182, x180, x168, x176);
  fiat_addcarryx_u64(&x183, &x184, x182, x170, x178);
  x185 = ((uint64_t)x184 + x171);
  fiat_subborrowx_u64(&x186, &x187, 0x0, x181, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x188, &x189, x187, x183, UINT64_C(0x7fffffffffffffff));
  fiat_subborrowx_u64(&x190, &x191, x189, x185, 0x0);
  fiat_cmovznz_u64(&x192, x191, x186, x181);
  fiat_cmovznz_u64(&x193, x191, x188, x183);
  fiat_subborrowx_u64(&x194, &x195, 0x0, x192, x56);
  fiat_subborrowx_u64(&x196, &x197, x195, x193, x57);
  fiat_cmovznz_u64(&x198, x197, 0x0, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x199, &x200, 0x0, x194, x198);
  fiat_addcarryx_u64(&x201, &x202, x200, x196, (x198 & UINT64_C(0x7fffffffffffffff)));
  fiat_subborrowx_u64(&x203, &x204, 0x0, x199, x113);
  fiat_subborrowx_u64(&x205, &x206, x204, x201, x114);
  fiat_cmovznz_u64(&x207, x206, 0x0, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x208, &x209, 0x0, x203, x207);
  fiat_addcarryx_u64(&x210, &x211, x209, x205, (x207 & UINT64_C(0x7fffffffffffffff)));
  fiat_subborrowx_u64(&x212, &x213, 0x0, x56, x113);
  fiat_subborrowx_u64(&x214, &x215, x213, x57, x114);
  fiat_cmovznz_u64(&x216, x215, 0x0, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x217, &x218, 0x0, x212, x216);
  fiat_addcarryx_u64(&x219, &x220, x218, x214, (x216 & UINT64_C(0x7fffffffffffffff)));
  out1[0] = x217;
  out1[1] = x219;
  out2[0] = x208;
  out2[1] = x210;
}


/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg4: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   out2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
static void fiat_addFp2_(uint64_t out1[2], uint64_t out2[2], const uint64_t arg1[2], const uint64_t arg2[2], const uint64_t arg3[2], const uint64_t arg4[2]) {
  uint64_t x1;
  fiat_uint1 x2;
  uint64_t x3;
  fiat_uint1 x4;
  uint64_t x5;
  fiat_uint1 x6;
  uint64_t x7;
  fiat_uint1 x8;
  uint64_t x9;
  fiat_uint1 x10;
  uint64_t x11;
  fiat_uint1 x12;
  uint64_t x13;
  fiat_uint1 x14;
  uint64_t x15;
  fiat_uint1 x16;
  uint64_t x17;
  fiat_uint1 x18;
  uint64_t x19;
  fiat_uint1 x20;
  uint64_t x21;
  uint64_t x22;
  uint64_t x23;
  uint64_t x24;
  fiat_addcarryx_u64(&x1, &x2, 0x0, (arg2[0]), (arg4[0]));
  fiat_addcarryx_u64(&x3, &x4, x2, (arg2[1]), (arg4[1]));
  fiat_subborrowx_u64(&x5, &x6, 0x0, x1, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x7, &x8, x6, x3, UINT64_C(0x7fffffffffffffff));
  fiat_subborrowx_u64(&x9, &x10, x8, x4, 0x0);
  fiat_addcarryx_u64(&x11, &x12, 0x0, (arg1[0]), (arg3[0]));
  fiat_addcarryx_u64(&x13, &x14, x12, (arg1[1]), (arg3[1]));
  fiat_subborrowx_u64(&x15, &x16, 0x0, x11, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x17, &x18, x16, x13, UINT64_C(0x7fffffffffffffff));
  fiat_subborrowx_u64(&x19, &x20, x18, x14, 0x0);
  fiat_cmovznz_u64(&x21, x20, x15, x11);
  fiat_cmovznz_u64(&x22, x20, x17, x13);
  fiat_cmovznz_u64(&x23, x10, x5, x1);
  fiat_cmovznz_u64(&x24, x10, x7, x3);
  out1[0] = x21;
  out1[1] = x22;
  out2[0] = x23;
  out2[1] = x24;
}


/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg4: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   out2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
static void fiat_subFp2_(uint64_t out1[2], uint64_t out2[2], const uint64_t arg1[2], const uint64_t arg2[2], const uint64_t arg3[2], const uint64_t arg4[2]) {
  uint64_t x1;
  uint64_t x2;
  uint64_t x3;
  fiat_uint1 x4;
  uint64_t x5;
  fiat_uint1 x6;
  uint64_t x7;
  uint64_t x8;
  fiat_uint1 x9;
  uint64_t x10;
  fiat_uint1 x11;
  uint64_t x12;
  uint64_t x13;
  uint64_t x14;
  fiat_uint1 x15;
  uint64_t x16;
  fiat_uint1 x17;
  uint64_t x18;
  uint64_t x19;
  fiat_uint1 x20;
  uint64_t x21;
  fiat_uint1 x22;
  x1 = (arg4[1]);
  x2 = (arg4[0]);
  fiat_subborrowx_u64(&x3, &x4, 0x0, (arg2[0]), x2);
  fiat_subborrowx_u64(&x5, &x6, x4, (arg2[1]), x1);
  fiat_cmovznz_u64(&x7, x6, 0x0, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x8, &x9, 0x0, x3, x7);
  fiat_addcarryx_u64(&x10, &x11, x9, x5, (x7 & UINT64_C(0x7fffffffffffffff)));
  x12 = (arg3[1]);
  x13 = (arg3[0]);
  fiat_subborrowx_u64(&x14, &x15, 0x0, (arg1[0]), x13);
  fiat_subborrowx_u64(&x16, &x17, x15, (arg1[1]), x12);
  fiat_cmovznz_u64(&x18, x17, 0x0, UINT64_C(0xffffffffffffffff));
  fiat_addcarryx_u64(&x19, &x20, 0x0, x14, x18);
  fiat_addcarryx_u64(&x21, &x22, x20, x16, (x18 & UINT64_C(0x7fffffffffffffff)));
  out1[0] = x19;
  out1[1] = x21;
  out2[0] = x8;
  out2[1] = x10;
}



void main() {
const uint64_t arg1[2] = {9223372036854775804, 58};
const uint64_t arg2[2] = {10866,4};
const uint64_t arg3[2] = {130866,2};
const uint64_t arg4[2] = {4914,1188};
printf("operands are: \n");
printf("(%lu, %lu) + i(%lu, %lu)", arg1[0], arg1[1], arg2[0], arg2[1]);
printf("\nand \n");
printf("(%lu, %lu) + i(%lu, %lu)", arg3[0], arg3[1], arg4[0], arg4[1]);
printf("\n \n product is: \n");
uint64_t op1[2];
uint64_t op2[2];
fiat_mulFp2_(op1, op2, arg1, arg2, arg3, arg4);
printf("(%lu, %lu) + i(%lu, %lu)", op1[0], op1[1], op2[0], op2[1]);
printf("\n");
printf("\n");
printf("sum is: \n");
uint64_t oa1[2];
uint64_t oa2[2];
fiat_addFp2_(oa1, oa2, arg1, arg2, arg3, arg4);
printf("(%lu, %lu) + i(%lu, %lu)", oa1[0], oa1[1], oa2[0], oa2[1]);
printf("\n");
printf("\n");
printf("difference is: \n");
uint64_t os1[2];
uint64_t os2[2];
fiat_subFp2_(os1, os2, arg1, arg2, arg3, arg4);
printf("(%lu, %lu) + i(%lu, %lu)", os1[0], os1[1], os2[0], os2[1]);
printf("\n");
}

