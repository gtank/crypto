// Copyright (c) 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build amd64

package edwards25519

import "math/bits"

// Field arithmetic in radix 2^51 representation. This code is a port of the
// public domain amd64-51-30k version of ed25519 from SUPERCOP.

// FieldElement represents an element of the field GF(2^255-19). An element t
// represents the integer t[0] + t[1]*2^51 + t[2]*2^102 + t[3]*2^153 +
// t[4]*2^204.
type FieldElement [5]uint64

const maskLow51Bits = (1 << 51) - 1

// FeAdd sets out = a + b. Long sequences of additions without reduction that
// let coefficients grow larger than 54 bits would be a problem. Paper
// cautions: "do not have such sequences of additions".
func FeAdd(out, a, b *FieldElement) {
	out[0] = a[0] + b[0]
	out[1] = a[1] + b[1]
	out[2] = a[2] + b[2]
	out[3] = a[3] + b[3]
	out[4] = a[4] + b[4]
}

// FeSub sets out = a - b
func FeSub(out, a, b *FieldElement) {
	var t FieldElement
	t = *b

	// Reduce each limb below 2^51, propagating carries. Ensures that results
	// fit within the limbs. This would not be required for reduced input.
	t[1] += t[0] >> 51
	t[0] = t[0] & maskLow51Bits
	t[2] += t[1] >> 51
	t[1] = t[1] & maskLow51Bits
	t[3] += t[2] >> 51
	t[2] = t[2] & maskLow51Bits
	t[4] += t[3] >> 51
	t[3] = t[3] & maskLow51Bits
	t[0] += (t[4] >> 51) * 19
	t[4] = t[4] & maskLow51Bits

	// This is slightly more complicated. Because we use unsigned coefficients,
	// we first add a multiple of p and then subtract.
	out[0] = (a[0] + 0xFFFFFFFFFFFDA) - t[0]
	out[1] = (a[1] + 0xFFFFFFFFFFFFE) - t[1]
	out[2] = (a[2] + 0xFFFFFFFFFFFFE) - t[2]
	out[3] = (a[3] + 0xFFFFFFFFFFFFE) - t[3]
	out[4] = (a[4] + 0xFFFFFFFFFFFFE) - t[4]
}

// FeNeg sets out = -a
func FeNeg(out, a *FieldElement) {
	var t FieldElement
	FeZero(&t)
	FeSub(out, &t, a)
}

// FeMul sets out = a * b
func FeMul(out, x, y *FieldElement) {
	var x0, x1, x2, x3, x4 uint64
	var y0, y1, y2, y3, y4 uint64

	x0 = x[0]
	x1 = x[1]
	x2 = x[2]
	x3 = x[3]
	x4 = x[4]

	y0 = y[0]
	y1 = y[1]
	y2 = y[2]
	y3 = y[3]
	y4 = y[4]

	// Reduction can be carried out simultaneously to multiplication. For
	// example, we do not compute a coefficient r_5 . Whenever the result of a
	// mul instruction belongs to r_5 , for example in the multiplication of
	// x_3*y_2 , we multiply one of the inputs by 19 and add the result to r_0.

	x1_19 := x1 * 19
	x2_19 := x2 * 19
	x3_19 := x3 * 19
	x4_19 := x4 * 19

	// calculate r0 = x0*y0 + 19*(x1*y4 + x2*y3 + x3*y2 + x4*y1)
	r00, r01 := mul64(0, 0, x0, y0)
	r00, r01 = mul64(r00, r01, x1_19, y4)
	r00, r01 = mul64(r00, r01, x2_19, y3)
	r00, r01 = mul64(r00, r01, x3_19, y2)
	r00, r01 = mul64(r00, r01, x4_19, y1)

	// calculate r1 = x0*y1 + x1*y0 + 19*(x2*y4 + x3*y3 + x4*y2)
	r10, r11 := mul64(0, 0, x0, y1)
	r10, r11 = mul64(r10, r11, x1, y0)
	r10, r11 = mul64(r10, r11, x2_19, y4)
	r10, r11 = mul64(r10, r11, x3_19, y3)
	r10, r11 = mul64(r10, r11, x4_19, y2)

	// calculate r2 = x0*y2 + x1*y1 + x2*y0 + 19*(x3*y4 + x4*y3)
	r20, r21 := mul64(0, 0, x0, y2)
	r20, r21 = mul64(r20, r21, x1, y1)
	r20, r21 = mul64(r20, r21, x2, y0)
	r20, r21 = mul64(r20, r21, x3_19, y4)
	r20, r21 = mul64(r20, r21, x4_19, y3)

	// calculate r3 = x0*y3 + x1*y2 + x2*y1 + x3*y0 + 19*x4*y4
	r30, r31 := mul64(0, 0, x0, y3)
	r30, r31 = mul64(r30, r31, x1, y2)
	r30, r31 = mul64(r30, r31, x2, y1)
	r30, r31 = mul64(r30, r31, x3, y0)
	r30, r31 = mul64(r30, r31, x4_19, y4)

	// calculate r4 = x0*y4 + x1*y3 + x2*y2 + x3*y1 + x4*y0
	r40, r41 := mul64(0, 0, x0, y4)
	r40, r41 = mul64(r40, r41, x1, y3)
	r40, r41 = mul64(r40, r41, x2, y2)
	r40, r41 = mul64(r40, r41, x3, y1)
	r40, r41 = mul64(r40, r41, x4, y0)

	// After the multiplication we need to reduce (carry) the 5 coefficients to
	// obtain a result with coefficients that are at most slightly larger than
	// 2^51 . Denote the two registers holding coefficient r_0 as r_00 and r_01
	// with r_0 = 2^64*r_01 + r_00 . Similarly denote the two registers holding
	// coefficient r_1 as r_10 and r_11 . We first shift r_01 left by 13, while
	// shifting in the most significant bits of r_00 (shld instruction) and
	// then compute the logical and of r_00 with 2^51 − 1. We do the same with
	// r_10 and r_11 and add r_01 into r_10 after the logical and with 2^51 −
	// 1. We proceed this way for coefficients r_2,...,r_4; register r_41 is
	// multiplied by 19 before adding it to r_00 .

	r01 = (r01 << 13) | (r00 >> 51)
	r00 &= maskLow51Bits

	r11 = (r11 << 13) | (r10 >> 51)
	r10 &= maskLow51Bits
	r10 += r01

	r21 = (r21 << 13) | (r20 >> 51)
	r20 &= maskLow51Bits
	r20 += r11

	r31 = (r31 << 13) | (r30 >> 51)
	r30 &= maskLow51Bits
	r30 += r21

	r41 = (r41 << 13) | (r40 >> 51)
	r40 &= maskLow51Bits
	r40 += r31

	r41 *= 19
	r00 += r41

	// Now all 5 coefficients fit into 64-bit registers but are still too large
	// to be used as input to another multiplication. We therefore carry from
	// r_0 to r_1 , from r_1 to r_2 , from r_2 to r_3 , from r_3 to r_4 , and
	// finally from r_4 to r_0 . Each of these carries is done as one copy, one
	// right shift by 51, one logical and with 2^51 − 1, and one addition.

	r10 += r00 >> 51
	r00 &= maskLow51Bits
	r20 += r10 >> 51
	r10 &= maskLow51Bits
	r30 += r20 >> 51
	r20 &= maskLow51Bits
	r40 += r30 >> 51
	r30 &= maskLow51Bits
	r00 += (r40 >> 51) * 19
	r40 &= maskLow51Bits

	out[0] = r00
	out[1] = r10
	out[2] = r20
	out[3] = r30
	out[4] = r40
}

// FeSquare sets out = x*x
func FeSquare(out, x *FieldElement) {
	// Squaring needs only 15 mul instructions. Some inputs are multiplied by 2;
	// this is combined with multiplication by 19 where possible. The coefficient
	// reduction after squaring is the same as for multiplication.

	var x0, x1, x2, x3, x4 uint64

	x0 = x[0]
	x1 = x[1]
	x2 = x[2]
	x3 = x[3]
	x4 = x[4]

	x0_2 := x0 << 1
	x1_2 := x1 << 1

	x1_38 := x1 * 38
	x2_38 := x2 * 38
	x3_38 := x3 * 38

	x3_19 := x3 * 19
	x4_19 := x4 * 19

	// r0 = x0*x0 + x1*38*x4 + x2*38*x3
	r00, r01 := mul64(0, 0, x0, x0)
	r00, r01 = mul64(r00, r01, x1_38, x4)
	r00, r01 = mul64(r00, r01, x2_38, x3)

	// r1 = x0*2*x1 + x2*38*x4 + x3*19*x3
	r10, r11 := mul64(0, 0, x0_2, x1)
	r10, r11 = mul64(r10, r11, x2_38, x4)
	r10, r11 = mul64(r10, r11, x3_19, x3)

	// r2 = x0*2*x2 + x1*x1 + x3*38*x4
	r20, r21 := mul64(0, 0, x0_2, x2)
	r20, r21 = mul64(r20, r21, x1, x1)
	r20, r21 = mul64(r20, r21, x3_38, x4)

	// r3 = x0*2*x3 + x1*2*x2 + x4*19*x4
	r30, r31 := mul64(0, 0, x0_2, x3)
	r30, r31 = mul64(r30, r31, x1_2, x2)
	r30, r31 = mul64(r30, r31, x4_19, x4)

	// r4 = x0*2*x4 + x1*2*x3 + x2*x2
	r40, r41 := mul64(0, 0, x0_2, x4)
	r40, r41 = mul64(r40, r41, x1_2, x3)
	r40, r41 = mul64(r40, r41, x2, x2)

	// Same reduction

	r01 = (r01 << 13) | (r00 >> 51)
	r00 &= maskLow51Bits

	r11 = (r11 << 13) | (r10 >> 51)
	r10 &= maskLow51Bits
	r10 += r01

	r21 = (r21 << 13) | (r20 >> 51)
	r20 &= maskLow51Bits
	r20 += r11

	r31 = (r31 << 13) | (r30 >> 51)
	r30 &= maskLow51Bits
	r30 += r21

	r41 = (r41 << 13) | (r40 >> 51)
	r40 &= maskLow51Bits
	r40 += r31

	r41 *= 19
	r00 += r41

	r10 += r00 >> 51
	r00 &= maskLow51Bits
	r20 += r10 >> 51
	r10 &= maskLow51Bits
	r30 += r20 >> 51
	r20 &= maskLow51Bits
	r40 += r30 >> 51
	r30 &= maskLow51Bits
	r00 += (r40 >> 51) * 19
	r40 &= maskLow51Bits

	out[0] = r00
	out[1] = r10
	out[2] = r20
	out[3] = r30
	out[4] = r40
}

func mul64(accLo, accHi, x, y uint64) (ol, oh uint64) {
	oh, ol = bits.Mul64(x, y)
	ol += accLo
	if ol < accLo {
		oh += 1
	}
	oh += accHi
	return
}

// FeSquare2 calculates out = 2 * a * a.
func FeSquare2(out, a *FieldElement) {
	FeSquare(out, a)
	FeAdd(out, out, out)
}

// Replace (f,g) with (g,g) if b == 1;
// replace (f,g) with (f,g) if b == 0.
//
// Preconditions: b in {0,1}.
func FeCMove(f, g *FieldElement, b int32) {
	negate := (1<<64 - 1) * uint64(b)
	f[0] ^= negate & (f[0] ^ g[0])
	f[1] ^= negate & (f[1] ^ g[1])
	f[2] ^= negate & (f[2] ^ g[2])
	f[3] ^= negate & (f[3] ^ g[3])
	f[4] ^= negate & (f[4] ^ g[4])
}

func FeFromBytes(v *FieldElement, x *[32]byte) {
	v[0] = uint64(x[0])
	v[0] |= uint64(x[1]) << 8
	v[0] |= uint64(x[2]) << 16
	v[0] |= uint64(x[3]) << 24
	v[0] |= uint64(x[4]) << 32
	v[0] |= uint64(x[5]) << 40
	v[0] |= uint64(x[6]&7) << 48

	v[1] = uint64(x[6]) >> 3
	v[1] |= uint64(x[7]) << 5
	v[1] |= uint64(x[8]) << 13
	v[1] |= uint64(x[9]) << 21
	v[1] |= uint64(x[10]) << 29
	v[1] |= uint64(x[11]) << 37
	v[1] |= uint64(x[12]&63) << 45

	v[2] = uint64(x[12]) >> 6
	v[2] |= uint64(x[13]) << 2
	v[2] |= uint64(x[14]) << 10
	v[2] |= uint64(x[15]) << 18
	v[2] |= uint64(x[16]) << 26
	v[2] |= uint64(x[17]) << 34
	v[2] |= uint64(x[18]) << 42
	v[2] |= uint64(x[19]&1) << 50

	v[3] = uint64(x[19]) >> 1
	v[3] |= uint64(x[20]) << 7
	v[3] |= uint64(x[21]) << 15
	v[3] |= uint64(x[22]) << 23
	v[3] |= uint64(x[23]) << 31
	v[3] |= uint64(x[24]) << 39
	v[3] |= uint64(x[25]&15) << 47

	v[4] = uint64(x[25]) >> 4
	v[4] |= uint64(x[26]) << 4
	v[4] |= uint64(x[27]) << 12
	v[4] |= uint64(x[28]) << 20
	v[4] |= uint64(x[29]) << 28
	v[4] |= uint64(x[30]) << 36
	v[4] |= uint64(x[31]&127) << 44
}

func FeToBytes(r *[32]byte, v *FieldElement) {
	var t FieldElement
	feReduce(&t, v)

	r[0] = byte(t[0] & 0xff)
	r[1] = byte((t[0] >> 8) & 0xff)
	r[2] = byte((t[0] >> 16) & 0xff)
	r[3] = byte((t[0] >> 24) & 0xff)
	r[4] = byte((t[0] >> 32) & 0xff)
	r[5] = byte((t[0] >> 40) & 0xff)
	r[6] = byte((t[0] >> 48))

	r[6] ^= byte((t[1] << 3) & 0xf8)
	r[7] = byte((t[1] >> 5) & 0xff)
	r[8] = byte((t[1] >> 13) & 0xff)
	r[9] = byte((t[1] >> 21) & 0xff)
	r[10] = byte((t[1] >> 29) & 0xff)
	r[11] = byte((t[1] >> 37) & 0xff)
	r[12] = byte((t[1] >> 45))

	r[12] ^= byte((t[2] << 6) & 0xc0)
	r[13] = byte((t[2] >> 2) & 0xff)
	r[14] = byte((t[2] >> 10) & 0xff)
	r[15] = byte((t[2] >> 18) & 0xff)
	r[16] = byte((t[2] >> 26) & 0xff)
	r[17] = byte((t[2] >> 34) & 0xff)
	r[18] = byte((t[2] >> 42) & 0xff)
	r[19] = byte((t[2] >> 50))

	r[19] ^= byte((t[3] << 1) & 0xfe)
	r[20] = byte((t[3] >> 7) & 0xff)
	r[21] = byte((t[3] >> 15) & 0xff)
	r[22] = byte((t[3] >> 23) & 0xff)
	r[23] = byte((t[3] >> 31) & 0xff)
	r[24] = byte((t[3] >> 39) & 0xff)
	r[25] = byte((t[3] >> 47))

	r[25] ^= byte((t[4] << 4) & 0xf0)
	r[26] = byte((t[4] >> 4) & 0xff)
	r[27] = byte((t[4] >> 12) & 0xff)
	r[28] = byte((t[4] >> 20) & 0xff)
	r[29] = byte((t[4] >> 28) & 0xff)
	r[30] = byte((t[4] >> 36) & 0xff)
	r[31] = byte((t[4] >> 44))
}

func feReduce(t, v *FieldElement) {
	// Copy v
	*t = *v

	// Let v = v[0] + v[1]*2^51 + v[2]*2^102 + v[3]*2^153 + v[4]*2^204
	// Reduce each limb below 2^51, propagating carries.
	t[1] += t[0] >> 51
	t[0] = t[0] & maskLow51Bits
	t[2] += t[1] >> 51
	t[1] = t[1] & maskLow51Bits
	t[3] += t[2] >> 51
	t[2] = t[2] & maskLow51Bits
	t[4] += t[3] >> 51
	t[3] = t[3] & maskLow51Bits
	t[0] += (t[4] >> 51) * 19
	t[4] = t[4] & maskLow51Bits

	// We now have a field element t < 2^255, but need t <= 2^255-19

	// Get the carry bit
	c := (t[0] + 19) >> 51
	c = (t[1] + c) >> 51
	c = (t[2] + c) >> 51
	c = (t[3] + c) >> 51
	c = (t[4] + c) >> 51

	t[0] += 19 * c

	t[1] += t[0] >> 51
	t[0] = t[0] & maskLow51Bits
	t[2] += t[1] >> 51
	t[1] = t[1] & maskLow51Bits
	t[3] += t[2] >> 51
	t[2] = t[2] & maskLow51Bits
	t[4] += t[3] >> 51
	t[3] = t[3] & maskLow51Bits
	// no additional carry
	t[4] = t[4] & maskLow51Bits
}
