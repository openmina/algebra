use crate::{
    bytes::{FromBytes, ToBytes}, fields::{BitIteratorBE, BitIteratorLE}, UniformRand
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use ark_std::{
    convert::TryFrom,
    fmt::{Debug, Display},
    io::{Read, Result as IoResult, Write},
    vec::Vec,
};
use num_bigint::BigUint;
use zeroize::Zeroize;

#[macro_use]
pub mod arithmetic;
#[macro_use]
mod macros;

pub fn signed_mod_reduction(n: u64, modulus: u64) -> i64 {
    let t = (n % modulus) as i64;
    if t as u64 >= (modulus / 2) {
        t - (modulus as i64)
    } else {
        t
    }
}

// bigint_impl!(BigInteger64, 1);
// bigint_impl!(BigInteger128, 2);
bigint_impl!(BigInteger256, 9);
// bigint_impl!(BigInteger320, 5);
// bigint_impl!(BigInteger384, 6);
// bigint_impl!(BigInteger448, 7);
// bigint_impl!(BigInteger768, 12);
// bigint_impl!(BigInteger832, 13);

#[cfg(test)]
mod tests;

/// This defines a `BigInteger`, a smart wrapper around a
/// sequence of `u64` limbs, least-significant limb first.
pub trait BigInteger:
    ToBytes
    + FromBytes
    + CanonicalSerialize
    + CanonicalDeserialize
    + Copy
    + Clone
    + Debug
    + Default
    + Display
    + Eq
    + Ord
    + Send
    + Sized
    + Sync
    + 'static
    + UniformRand
    + Zeroize
    + AsMut<[u32]>
    + AsRef<[u32]>
    + From<u64>
    + TryFrom<BigUint>
    + Into<BigUint>
{
    /// Number of limbs.
    const NUM_LIMBS: usize;

    fn to_64x4(&self) -> [u64; 4];
    fn from_64x4(value: [u64; 4]) -> Self;

    /// Add another representation to this one, returning the carry bit.
    fn add_nocarry(&mut self, other: &Self) -> bool;

    /// Subtract another representation from this one, returning the borrow bit.
    fn sub_noborrow(&mut self, other: &Self) -> bool;

    /// Performs a leftwise bitshift of this number, effectively multiplying
    /// it by 2. Overflow is ignored.
    fn mul2(&mut self);

    /// Performs a leftwise bitshift of this number by some amount.
    fn muln(&mut self, amt: u32);

    /// Performs a rightwise bitshift of this number, effectively dividing
    /// it by 2.
    fn div2(&mut self);

    /// Performs a rightwise bitshift of this number by some amount.
    fn divn(&mut self, amt: u32);

    /// Returns true iff this number is odd.
    fn is_odd(&self) -> bool;

    /// Returns true iff this number is even.
    fn is_even(&self) -> bool;

    /// Returns true iff this number is zero.
    fn is_zero(&self) -> bool;

    /// Compute the number of bits needed to encode this number. Always a
    /// multiple of 64.
    fn num_bits(&self) -> u32;

    /// Compute the `i`-th bit of `self`.
    fn get_bit(&self, i: usize) -> bool;

    /// Returns the big integer representation of a given big endian boolean
    /// array.
    fn from_bits_be(bits: &[bool]) -> Self;

    /// Returns the big integer representation of a given little endian boolean
    /// array.
    fn from_bits_le(bits: &[bool]) -> Self;

    /// Returns the bit representation in a big endian boolean array,
    /// with leading zeroes.
    fn to_bits_be(&self) -> Vec<bool> {
        let this = self.to_64x4();
        BitIteratorBE::new(this).collect::<Vec<_>>()
    }

    /// Returns the bit representation in a little endian boolean array,
    /// with trailing zeroes.
    fn to_bits_le(&self) -> Vec<bool> {
        let this = self.to_64x4();
        BitIteratorLE::new(this).collect::<Vec<_>>()
    }

    /// Returns the byte representation in a big endian byte array,
    /// with leading zeros.
    fn to_bytes_be(&self) -> Vec<u8>;

    /// Returns the byte representation in a little endian byte array,
    /// with trailing zeros.
    fn to_bytes_le(&self) -> Vec<u8>;

    /// Returns the windowed non-adjacent form of `self`, for a window of size `w`.
    fn find_wnaf(&self, w: usize) -> Option<Vec<i64>> {
        // w > 2 due to definition of wNAF, and w < 64 to make sure that `i64`
        // can fit each signed digit
        if w >= 2 && w < 64 {
            let mut res = vec![];
            let mut e = *self;
            let e64 = self.to_64x4();

            while !e.is_zero() {
                let z: i64;
                if e.is_odd() {
                    z = signed_mod_reduction(e64.as_ref()[0], 1 << w);
                    if z >= 0 {
                        e.sub_noborrow(&Self::from(z as u64));
                    } else {
                        e.add_nocarry(&Self::from((-z) as u64));
                    }
                } else {
                    z = 0;
                }
                res.push(z);
                e.div2();
            }

            Some(res)
        } else {
            None
        }
    }

    /// Writes this `BigInteger` as a big endian integer. Always writes
    /// `(num_bits` / 8) bytes.
    fn write_le<W: Write>(&self, writer: &mut W) -> IoResult<()> {
        self.write(writer)
    }

    /// Reads a big endian integer occupying (`num_bits` / 8) bytes into this
    /// representation.
    fn read_le<R: Read>(&mut self, reader: &mut R) -> IoResult<()> {
        *self = Self::read(reader)?;
        Ok(())
    }
}
