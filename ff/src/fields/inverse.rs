//! Implementation based on:
//! - https://github.com/privacy-scaling-explorations/halo2curves/blob/3bfa6562f0ddcbac941091ba3c7c9b6c322efac1/src/ff_ext/inverse.rs
//! - https://github.com/RustCrypto/crypto-bigint/blob/682f17a979c3a1886fde5426b26400dfc3f4775b/src/modular/safegcd.rs
//!
//! It's more than twice faster than the default (algebra) implementation:
//! Calling `Fp::invert` 1_000_000 times takes 2.05 seconds, instead of 5.23 seconds

use core::cmp::PartialEq;

/// Integer using 62 bits limbs
#[derive(Clone)]
pub struct Integer(pub [u64; NLIMBS]);

const NLIMBS: usize = 6;
const NBITS_PER_LIMB: usize = 62;

impl Integer {
    pub const MASK: u64 = u64::MAX >> (64 - NBITS_PER_LIMB);
    pub const MINUS_ONE: Self = Self([Self::MASK; NLIMBS]);
    pub const ZERO: Self = Self([0; NLIMBS]);
    pub const ONE: Self = {
        let mut data = [0; NLIMBS];
        data[0] = 1;
        Self(data)
    };

    const fn shr(&self) -> Self {
        let mut data = [0; NLIMBS];
        if self.is_neg() {
            data[NLIMBS - 1] = Self::MASK;
        }
        let mut i = 0;
        while i < NLIMBS - 1 {
            data[i] = self.0[i + 1];
            i += 1;
        }
        Self(data)
    }

    const fn lowest(&self) -> u64 {
        self.0[0]
    }

    const fn is_neg(&self) -> bool {
        self.0[NLIMBS - 1] > (Self::MASK >> 1)
    }

    const fn add(&self, other: &Self) -> Self {
        let (mut data, mut carry) = ([0; NLIMBS], 0);
        let mut i = 0;
        while i < NLIMBS {
            let sum = self.0[i] + other.0[i] + carry;
            data[i] = sum & Integer::MASK;
            carry = sum >> NBITS_PER_LIMB;
            i += 1;
        }
        Self(data)
    }

    const fn mul(&self, other: i64) -> Self {
        let mut data = [0; NLIMBS];
        let (other, mut carry, mask) = if other < 0 {
            (-other, -other as u64, Integer::MASK)
        } else {
            (other, 0, 0)
        };
        let mut i = 0;
        while i < NLIMBS {
            let sum = (carry as u128) + ((self.0[i] ^ mask) as u128) * (other as u128);
            data[i] = sum as u64 & Integer::MASK;
            carry = (sum >> NBITS_PER_LIMB) as u64;
            i += 1;
        }
        Self(data)
    }

    const fn neg(self) -> Self {
        let (mut data, mut carry) = ([0; NLIMBS], 1);
        let mut i = 0;
        while i < NLIMBS {
            let sum = (self.0[i] ^ Integer::MASK) + carry;
            data[i] = sum & Integer::MASK;
            carry = sum >> NBITS_PER_LIMB;
            i += 1;
        }
        Self(data)
    }
}

impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        let mut is_eq = true;
        let mut i = 0;
        while i < NLIMBS {
            is_eq &= self.0[i] == other.0[i];
            i += 1;
        }
        is_eq
    }
}

/// Bernstein-Yang inverter
pub struct BYInverter {
    pub modulus: Integer,
    /// Adjusting parameter
    pub adjuster: Integer,
    /// Multiplicative inverse of the modulus modulo 2^62
    pub inverse: i64,
}

/// Type of the Bernstein-Yang transition matrix multiplied by 2^62
type Matrix = [[i64; 2]; 2];

impl BYInverter {
    const fn jump(f: &Integer, g: &Integer, mut delta: i64) -> (i64, Matrix) {
        const fn min(a: i64, b: i64) -> i64 {
            if a > b {
                b
            } else {
                a
            }
        }
        let (mut steps, mut f, mut g) = (62, f.lowest() as i64, g.lowest() as i128);
        let mut t: Matrix = [[1, 0], [0, 1]];
        loop {
            let zeros = min(steps, g.trailing_zeros() as i64);
            (steps, delta, g) = (steps - zeros, delta + zeros, g >> zeros);
            t[0] = [t[0][0] << zeros, t[0][1] << zeros];
            if steps == 0 {
                break;
            }
            if delta > 0 {
                (delta, f, g) = (-delta, g as i64, -f as i128);
                (t[0], t[1]) = (t[1], [-t[0][0], -t[0][1]]);
            }
            let mask = (1 << min(min(steps, 1 - delta), 5)) - 1;
            let w = (g as i64).wrapping_mul(f.wrapping_mul(3) ^ 28) & mask;
            t[1] = [t[0][0] * w + t[1][0], t[0][1] * w + t[1][1]];
            g += w as i128 * f as i128;
        }
        (delta, t)
    }

    const fn fg(f: Integer, g: Integer, t: Matrix) -> (Integer, Integer) {
        (
            f.mul(t[0][0]).add(&g.mul(t[0][1])).shr(),
            f.mul(t[1][0]).add(&g.mul(t[1][1])).shr(),
        )
    }

    const fn de(&self, d: Integer, e: Integer, t: Matrix) -> (Integer, Integer) {
        let mask = Integer::MASK as i64;
        let mut md = t[0][0] * d.is_neg() as i64 + t[0][1] * e.is_neg() as i64;
        let mut me = t[1][0] * d.is_neg() as i64 + t[1][1] * e.is_neg() as i64;
        let cd = t[0][0]
            .wrapping_mul(d.lowest() as i64)
            .wrapping_add(t[0][1].wrapping_mul(e.lowest() as i64))
            & mask;
        let ce = t[1][0]
            .wrapping_mul(d.lowest() as i64)
            .wrapping_add(t[1][1].wrapping_mul(e.lowest() as i64))
            & mask;
        md -= (self.inverse.wrapping_mul(cd).wrapping_add(md)) & mask;
        me -= (self.inverse.wrapping_mul(ce).wrapping_add(me)) & mask;
        let cd = d
            .mul(t[0][0])
            .add(&e.mul(t[0][1]))
            .add(&self.modulus.mul(md));
        let ce = d
            .mul(t[1][0])
            .add(&e.mul(t[1][1]))
            .add(&self.modulus.mul(me));
        (cd.shr(), ce.shr())
    }

    const fn norm(&self, mut value: Integer, negate: bool) -> Integer {
        if value.is_neg() {
            value = value.add(&self.modulus);
        }
        if negate {
            value = value.neg();
        }
        if value.is_neg() {
            value = value.add(&self.modulus);
        }
        value
    }

    const fn convert<const I: usize, const O: usize, const S: usize>(input: &[u64]) -> [u64; S] {
        const fn min(a: usize, b: usize) -> usize {
            if a > b {
                b
            } else {
                a
            }
        }
        let (total, mut output, mut bits) = (min(input.len() * I, S * O), [0; S], 0);
        while bits < total {
            let (i, o) = (bits % I, bits % O);
            output[bits / O] |= (input[bits / I] >> i) << o;
            bits += min(I - i, O - o);
        }
        let mask = u64::MAX >> (64 - O);
        let mut filled = total / O + if total % O > 0 { 1 } else { 0 };
        while filled > 0 {
            filled -= 1;
            output[filled] &= mask;
        }
        output
    }

    pub fn invert(&self, value: &[u64]) -> Option<[u64; 4]> {
        let (mut d, mut e) = (Integer::ZERO, self.adjuster.clone());
        let mut g = Integer(Self::convert::<64, 62, NLIMBS>(value));
        let (mut delta, mut f) = (1, self.modulus.clone());
        let mut matrix;
        while g != Integer::ZERO {
            (delta, matrix) = Self::jump(&f, &g, delta);
            (f, g) = Self::fg(f, g, matrix);
            (d, e) = self.de(d, e, matrix);
        }
        let antiunit = f == Integer::MINUS_ONE;
        if (f != Integer::ONE) && !antiunit {
            return None;
        }
        Some(Self::convert::<62, 64, 4>(&self.norm(d, antiunit).0))
    }
}
