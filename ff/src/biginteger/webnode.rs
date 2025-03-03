
use core::{convert::TryFrom, fmt::Display};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{io::{Read, Result as IoResult, Write}, rand::{distributions::Standard, prelude::Distribution, Rng}, vec::Vec};
use num_bigint::BigUint;
use zeroize::Zeroize;

use crate::{FromBytes, ToBytes};
use crate::fields::webnode::MASK;

use super::BigInteger;


#[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash, Zeroize)]
pub struct BigInteger256(pub(crate) [u32; 9]);

impl BigInteger256 {
    pub const fn new(value: [u32; 9]) -> Self {
        BigInteger256(value)
    }

    pub const fn from_64x4(value: [u64; 4]) -> Self {
        BigInteger256(crate::fields::webnode::from_64x4(value))
    }

    pub const fn to_64x4(&self) -> [u64; 4] {
        crate::fields::webnode::to_64x4(self.0)
    }

    #[ark_ff_asm::unroll_for_loops]
    pub fn assign_bits_and(&mut self, other: &Self) {
        for i in 0..9 {
            self.0[i] |= other.0[i]
        }
    }

    pub fn to_native(&self) -> [u32; 9] {
        self.0
    }
}

impl BigInteger for BigInteger256 {
    const NUM_LIMBS: usize = 9;

    fn to_64x4(&self) -> [u64; 4] {
        crate::fields::webnode::to_64x4(self.0)
    }
    fn from_64x4(value: [u64; 4]) -> Self {
        BigInteger256(crate::fields::webnode::from_64x4(value))
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn add_nocarry(&mut self, other: &Self) -> bool {
        let mut carry = 0;
        for i in 0..9 {
            self.0[i] = {
                let tmp = self.0[i] as u64 + other.0[i] as u64 + carry;
                carry = tmp >> 29;
                (tmp as u32) & MASK
            };
        }
        carry != 0
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn sub_noborrow(&mut self, other: &Self) -> bool {
        let mut borrow = 0;
        for i in 0..9 {
            self.0[i] = {
                let tmp = (1u64 << 29) + (self.0[i] as u64) - (other.0[i] as u64) - (borrow as u64);
                borrow = if tmp >> 29 == 0 {
                    1
                } else {
                    0
                };
                (tmp as u32) & MASK
            };
        }
        borrow != 0
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    #[allow(unused)]
    fn mul2(&mut self) {
        let mut last = 0;
        for i in 0..9 {
            let a = &mut self.0[i];
            let tmp = (*a as u64) >> 28;
            *a = (*a << 1) & MASK;
            *a |= last as u32;
            last = tmp;
        }
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn muln(&mut self, mut n: u32) {
        if n >= 64 * 4 {
            *self = Self::from(0);
            return;
        }

        while n >= 29 {
            let mut t = 0;
            for i in 0..9 {
                core::mem::swap(&mut t, &mut self.0[i]);
            }
            n -= 29;
        }

        if n > 0 {
            let mut t = 0;
            #[allow(unused)]
            for i in 0..9 {
                let a = &mut self.0[i];
                let t2 = *a >> (29 - n);
                *a = (*a << n) & MASK;
                // *a <<= n;
                *a |= t;
                t = t2;
            }
        }
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    #[allow(unused)]
    fn div2(&mut self) {
        let mut t = 0;
        for i in 0..9 {
            let a = &mut self.0[9 - i - 1];
            let t2 = (*a << 28) & MASK;
            *a >>= 1;
            *a |= t;
            t = t2;
        }
    }

    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn divn(&mut self, mut n: u32) {
        if n >= 64 * 4 {
            *self = Self::from(0);
            return;
        }

        while n >= 29 {
            let mut t = 0;
            for i in 0..9 {
                core::mem::swap(&mut t, &mut self.0[9 - i - 1]);
            }
            n -= 29;
        }

        if n > 0 {
            let mut t = 0;
            #[allow(unused)]
            for i in 0..9 {
                let a = &mut self.0[9 - i - 1];
                let t2 = (*a << (29 - n) & MASK);
                // let t2 = *a << (29 - n);
                *a >>= n;
                *a |= t;
                t = t2;
            }
        }
    }

    #[inline]
    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    #[inline]
    fn is_even(&self) -> bool {
        !self.is_odd()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        for i in 0..9 {
            if self.0[i] != 0 {
                return false;
            }
        }
        true
    }

    #[inline]
    fn num_bits(&self) -> u32 {
        let value = self.to_64x4();

        let mut ret = 4 * 64;
        for i in value.iter().rev() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 64 {
                break;
            }
        }

        ret
    }

    #[inline]
    fn get_bit(&self, i: usize) -> bool {
        let value = self.to_64x4();
        if i >= 64 * 4 {
            false
        } else {
            let limb = i / 64;
            let bit = i - (64 * limb);
            (value[limb] & (1 << bit)) != 0
        }
    }

    #[inline]
    fn from_bits_be(bits: &[bool]) -> Self {
        let mut res: [u64; 4] = <[u64; 4]>::default();
        let mut acc: u64 = 0;

        for (i, bits64) in bits.rchunks(64).enumerate() {
            for bit in bits64.iter() {
                acc <<= 1;
                acc |= *bit as u64;
            }
            res[i] = acc;
            acc = 0;
        }
        Self::from_64x4(res)
    }

    fn from_bits_le(bits: &[bool]) -> Self {
        let mut res: [u64; 4] = <[u64; 4]>::default();
        let mut acc: u64 = 0;

        for (i, bits64) in bits.chunks(64).enumerate() {
            for bit in bits64.iter().rev() {
                acc <<= 1;
                acc |= *bit as u64;
            }
            res[i] = acc;
            acc = 0;
        }
        Self::from_64x4(res)
    }

    #[inline]
    fn to_bytes_be(&self) -> Vec<u8> {
        let mut le_bytes = self.to_bytes_le();
        le_bytes.reverse();
        le_bytes
    }

    #[inline]
    fn to_bytes_le(&self) -> Vec<u8> {
        let bigint = self.to_64x4();
        let array_map = bigint.iter().map(|limb| limb.to_le_bytes());
        let mut res = Vec::<u8>::with_capacity(4 * 8);
        for limb in array_map {
            res.extend_from_slice(&limb);
        }
        res
    }
}

impl CanonicalSerialize for BigInteger256 {
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.write(writer)?;
        Ok(())
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        Self::NUM_LIMBS * 8
    }
}

impl CanonicalDeserialize for BigInteger256 {
    #[inline]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let value = Self::read(reader)?;
        Ok(value)
    }
}

impl ToBytes for BigInteger256 {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> IoResult<()> {
        let bigint: [u64; 4] = self.to_64x4();
        bigint.write(writer)
    }
}

impl FromBytes for BigInteger256 {
    #[inline]
    fn read<R: Read>(reader: R) -> IoResult<Self> {
        <[u64; 4]>::read(reader).map(Self::from_64x4)
    }
}

impl Display for BigInteger256 {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        let this = self.to_64x4();
        for i in this.iter().rev() {
            write!(f, "{:016X}", *i)?;
        }
        Ok(())
    }
}

impl Ord for BigInteger256 {
    #[inline]
    #[ark_ff_asm::unroll_for_loops]
    fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
        use core::cmp::Ordering;
        for i in 0..9 {
            let a = &self.0[9 - i - 1];
            let b = &other.0[9 - i - 1];
            if a < b {
                return Ordering::Less;
            } else if a > b {
                return Ordering::Greater;
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for BigInteger256 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Distribution<BigInteger256> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BigInteger256 {
        let rand: [u64; 4] = rng.gen();
        BigInteger256::from_64x4(rand)
    }
}

impl AsMut<[u32]> for BigInteger256 {
    #[inline]
    fn as_mut(&mut self) -> &mut [u32] {
        &mut self.0
    }
}

impl AsRef<[u32]> for BigInteger256 {
    #[inline]
    fn as_ref(&self) -> &[u32] {
        &self.0
    }
}

impl From<u64> for BigInteger256 {
    #[inline]
    fn from(val: u64) -> BigInteger256 {
        Self::from_64x4([val, 0, 0, 0])
    }
}

impl TryFrom<BigUint> for BigInteger256 {
    type Error = ark_std::string::String;

    #[inline]
    fn try_from(val: num_bigint::BigUint) -> Result<BigInteger256, Self::Error> {
        let bytes = val.to_bytes_le();

        if bytes.len() > 4 * 8 {
            Err(format!(
                "A BigUint of {} bytes cannot fit into a {}.",
                bytes.len(),
                ark_std::stringify!(BigInteger256)
            ))
        } else {
            let mut limbs = [0u64; 4];

            bytes
                .chunks(8)
                .into_iter()
                .enumerate()
                .for_each(|(i, chunk)| {
                    let mut chunk_padded = [0u8; 8];
                    chunk_padded[..chunk.len()].copy_from_slice(chunk);
                    limbs[i] = u64::from_le_bytes(chunk_padded)
                });

            Ok(Self::from_64x4(limbs))
        }
    }
}

impl Into<BigUint> for BigInteger256 {
    #[inline]
    fn into(self) -> num_bigint::BigUint {
        BigUint::from_bytes_le(&self.to_bytes_le())
    }
}
