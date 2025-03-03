#![allow(unused)]
use ark_std::vec::Vec;

/// Make 4 u64 multiplications, instead of 1 u128
/// It's faster than __multi3 in wasm
/// https://github.com/rust-lang/compiler-builtins/blob/4797774cd72e453e30785cfee684aaf68e16e03e/src/int/mul.rs#L108
/// https://github.com/zkBob/fawkes-crypto/pull/15
#[cfg(target_family = "wasm")]
#[inline(always)]
pub fn u64_mul_u64(x: u64, y: u64) -> u128 {
    let x_low = (x as u32) as u64;
    let x_high = x >> 32;
    let y_low = (y as u32) as u64;
    let y_high = y >> 32;

    let z_low = x_low * y_low;
    let z_high = x_high * y_high;
    let z = u128::from(x_low * y_high) + u128::from(x_high * y_low);

    (u128::from(z_high) << 64) + (z << 32) + u128::from(z_low)
}

#[cfg(not(target_family = "wasm"))]
#[inline(always)]
pub fn u64_mul_u64(x: u64, y: u64) -> u128 {
    u128::from(x) * u128::from(y)
}

/// Calculate a + b + carry, returning the sum and modifying the
/// carry value.
macro_rules! adc {
    ($a:expr, $b:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128) + ($carry as u128);

        $carry = (tmp >> 64) as u64;

        tmp as u64
    }};
}

/// Calculate a + (b * c) + carry, returning the least significant digit
/// and setting carry to the most significant digit.
macro_rules! mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + crate::biginteger::arithmetic::u64_mul_u64($b, $c) + ($carry as u128);
        // let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);

        $carry = (tmp >> 64) as u64;

        tmp as u64
    }};
}

/// Calculate a + (b * c) + carry, returning the least significant digit
/// and setting carry to the most significant digit.
macro_rules! const_mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);

        $carry = (tmp >> 64) as u64;

        tmp as u64
    }};
}

/// Calculate a - b - borrow, returning the result and modifying
/// the borrow value.
macro_rules! sbb {
    ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
        let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);

        $borrow = if tmp >> 64 == 0 { 1 } else { 0 };

        tmp as u64
    }};
}

#[inline(always)]
pub(crate) fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (u128::from(a)) + u64_mul_u64(b, c);
    // let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

#[inline(always)]
pub(crate) fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
    let tmp = (u128::from(a)) + u64_mul_u64(b, c);
    // let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

    *carry = (tmp >> 64) as u64;
}

pub fn find_wnaf(num: &[u64]) -> Vec<i64> {
    let is_zero = |num: &[u64]| num.iter().all(|x| *x == 0u64);
    let is_odd = |num: &[u64]| num[0] & 1 == 1;
    let sub_noborrow = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut borrow = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = sbb!(*a, b, &mut borrow);
        }
    };
    let add_nocarry = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut carry = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = adc!(*a, b, &mut carry);
        }
    };
    let div2 = |num: &mut [u64]| {
        let mut t = 0;
        for i in num.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    };

    let mut num = num.to_vec();
    let mut res = vec![];

    while !is_zero(&num) {
        let z: i64;
        if is_odd(&num) {
            z = 2 - (num[0] % 4) as i64;
            if z >= 0 {
                sub_noborrow(&mut num, z as u64)
            } else {
                add_nocarry(&mut num, (-z) as u64)
            }
        } else {
            z = 0;
        }
        res.push(z);
        div2(&mut num);
    }

    res
}
