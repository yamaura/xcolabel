//! # xcolabel
//!
//! Convert between column label to 0-based number.
//!
//! **xcolabel** converts between 0-based numbers and column labels of spreadsheet software.
//! For example, "A" becomes 0. "AA" becomes 26.
//! It also converts tuples of the form (row, column) into strings like "C2".
//!
//! # Status
//! **xcolabel** is a pure Rust library.
//! Everything except TryFromCellStr has been implemented.
//!
//! # Examples
//! ```
//! use xcolabel::ToCellString;
//!
//! assert_eq!((4, 2).to_cell_string(), "C5"); // value is 0-based (row, column)
//! ```
//!
pub use core::num::IntErrorKind;
use std::fmt;

/// Same manneor as std::num::ParseIntError
#[derive(Debug)]
pub struct ParseIntError {
    kind: IntErrorKind,
}

impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_str().fmt(f)
    }
}

impl std::error::Error for ParseIntError {
    fn description(&self) -> &str {
        self.to_str()
    }
}

impl ParseIntError {
    pub fn kind(&self) -> &IntErrorKind {
        &self.kind
    }

    fn to_str(&self) -> &str {
        match self.kind {
            IntErrorKind::InvalidDigit => "invalid digit found in string",
            IntErrorKind::PosOverflow => "number too large to fit in target type",
            _ => todo!(),
        }
    }
}

pub(crate) mod convert {
    use super::{IntErrorKind, ParseIntError, ToColumnDigit};
    use core::ops::{Div, Rem};

    /// convert number to char of column label like 'A'
    #[inline]
    pub const fn from_digit_column(num: u32) -> Option<char> {
        if num < 26 {
            let num = num as u8;
            Some((b'A' + num) as char)
        } else {
            None
        }
    }

    /// convert column label char 'A' to a number like 0
    #[inline]
    pub const fn char_to_digit_column(c: char) -> Option<u32> {
        // Force the 6th bit to be set to ensure ascii is lower case.
        match c {
            'a'..='z' | 'A'..='Z' => Some((c as u32 | 0b10_0000).wrapping_sub('a' as u32)),
            _ => None,
        }
    }
    #[inline]
    pub(crate) fn try_from_column_str<T>(src: &str) -> Result<T, ParseIntError>
    where
        T: num::FromPrimitive + num::CheckedAdd + num::CheckedMul,
    {
        use IntErrorKind::*;
        use ParseIntError as PIE;

        let one = T::from_u8(1).unwrap();
        let radix = T::from_u8(26).unwrap();
        let mut result = T::from_u8(0).unwrap();

        for (i, &c) in src.as_bytes().iter().enumerate() {
            if i > 0 {
                result = result.checked_add(&one).ok_or(PIE { kind: PosOverflow })?;
            }
            let mul = result
                .checked_mul(&radix)
                .ok_or(PIE { kind: PosOverflow })?;
            let x = T::from_u32(
                (c as char)
                    .to_digit_column()
                    .ok_or(PIE { kind: InvalidDigit })?,
            )
            .unwrap();
            result = mul.checked_add(&x).ok_or(PIE { kind: PosOverflow })?;
        }
        Ok(result)
    }

    #[inline]
    fn num_to_26_le<T>(num: &T) -> Vec<u8>
    where
        T: Sized
            + Div<T, Output = T>
            + Rem<T, Output = T>
            + std::marker::Copy
            + num::FromPrimitive
            + num::ToPrimitive
            + std::cmp::PartialOrd<T>,
    {
        let mut result = vec![];
        let mut cur = *num;

        let zero = T::from_u8(0).unwrap();
        let radix = T::from_u8(26).unwrap();

        if cur == zero {
            return vec![0];
        }

        while cur > zero {
            let x = cur % radix;
            result.push(x.to_u8().unwrap());
            cur = cur / radix;
        }
        result
    }

    #[inline]
    pub(crate) fn num_to_column_le<T>(num: &T) -> Vec<u8>
    where
        T: Sized
            + Div<T, Output = T>
            + Rem<T, Output = T>
            + std::marker::Copy
            + num::FromPrimitive
            + num::ToPrimitive
            + std::cmp::PartialOrd<T>,
    {
        let radix = 26;
        let mut result = num_to_26_le(num);
        if result.len() == 1 {
            return result;
        }
        for i in 1..(result.len() - 1) {
            if result[i] <= 0 {
                result[i + 1] -= 1;
                result[i] += radix;
            }
        }
        if result[result.len() - 1] == 0 {
            result.pop();
        }
        result
    }
}
pub use convert::from_digit_column;
use convert::*;

pub trait ToColumnDigit {
    /// convert column label char 'A' to a number like 0
    fn to_digit_column(self) -> Option<u32>;
}

impl ToColumnDigit for char {
    fn to_digit_column(self) -> Option<u32> {
        char_to_digit_column(self)
    }
}

/// A trait to convert from a column string like "AA" for 26.
/// It is 0-based.
pub trait TryFromColumnStr: Sized {
    /// Convert column label string "AA" to a number like 26.
    /// It is 0-based
    fn try_from_column_str(src: &str) -> Result<Self, ParseIntError>;
}

macro_rules! try_from_column_str_impl {
    ($t:ty) => {
        impl TryFromColumnStr for $t {
            #[inline]
            fn try_from_column_str(src: &str) -> Result<$t, ParseIntError> {
                try_from_column_str::<$t>(src)
            }
        }
    };
}

try_from_column_str_impl!(u8);
try_from_column_str_impl!(u16);
try_from_column_str_impl!(u32);
try_from_column_str_impl!(u64);
try_from_column_str_impl!(usize);

/// A trait to convert to column string like "A" for 0. It is 0
pub trait ToColumnString: Sized {
    fn to_column_string(&self) -> String;
}

macro_rules! to_column_string_impl {
    ($t:ty) => {
        impl ToColumnString for $t {
            #[inline]
            fn to_column_string(&self) -> String {
                if self < &26 {
                    return from_digit_column(*self as u32).unwrap().to_string();
                }
                let mut result = "".to_string();
                let v = num_to_column_le(self);
                let last = v.len() - 1;
                println!("{} {:?}", self, v);
                for (i, n) in v.iter().rev().enumerate() {
                    let is_last_n = if i == last { 0 } else { 1 };
                    // unwrap always safe
                    result += &from_digit_column((n - is_last_n) as u32)
                        .unwrap()
                        .to_string();
                }
                result
            }
        }
    };
}

to_column_string_impl!(u8);
to_column_string_impl!(u16);
to_column_string_impl!(u32);
to_column_string_impl!(u64);
to_column_string_impl!(usize);

/// A trait to convert to cell string like "C4"
pub trait ToCellString {
    fn to_cell_string(&self) -> String;
}

impl ToCellString for (u32, u32) {
    fn to_cell_string(&self) -> String {
        self.1.to_column_string() + &(self.0 + 1).to_string()
    }
}

/// A trait to convert from cell string like "C4"
pub trait TryFromCellStr<T>: Sized {
    type Err;
    fn from_cell_str(s: &str) -> Result<Self, Self::Err>;
}

#[cfg(test)]
mod tests {
    use super::IntErrorKind::*;
    use super::*;

    #[test]
    fn prim() {
        assert_eq!(12, u8::from_str_radix("12", 10).unwrap());
        assert!(u8::from_str_radix("12\n", 10).is_err());
    }

    #[test]
    fn char_from_column() {
        assert_eq!(Some('A'), from_digit_column(0));
        assert_eq!(Some('Z'), from_digit_column(25));
        assert_eq!(None, from_digit_column(26));
    }

    #[test]
    fn char_to_column() {
        assert_eq!(Some(0), 'A'.to_digit_column());
        assert_eq!(Some(0), 'a'.to_digit_column());
        assert_eq!(Some(25), 'Z'.to_digit_column());
        assert_eq!(Some(25), 'z'.to_digit_column());
        assert_eq!(None, '!'.to_digit_column());
        assert_eq!(None, '_'.to_digit_column());
    }

    #[test]
    fn u8() {
        assert_eq!(
            &InvalidDigit,
            u8::try_from_column_str("0").unwrap_err().kind()
        );
        assert_eq!(
            &PosOverflow,
            u8::try_from_column_str("IW").unwrap_err().kind()
        );
        assert_eq!(0, u8::try_from_column_str("A").unwrap());
        assert_eq!(1, u8::try_from_column_str("B").unwrap());
        assert_eq!(26, u8::try_from_column_str("AA").unwrap());
        assert_eq!(255, u8::try_from_column_str("IV").unwrap());
    }

    #[test]
    fn u32() {
        macro_rules! u {
            ($s:literal) => {
                u32::try_from_column_str($s).unwrap()
            };
        }
        assert_eq!(0, u32::try_from_column_str("A").unwrap());
        assert_eq!(1, u32::try_from_column_str("B").unwrap());
        assert_eq!(26, u32::try_from_column_str("AA").unwrap());
        assert_eq!(51, u32::try_from_column_str("AZ").unwrap());
        assert_eq!(676, u32::try_from_column_str("ZA").unwrap());
        assert_eq!(701, u32::try_from_column_str("ZZ").unwrap());
        assert_eq!(702, u32::try_from_column_str("AAA").unwrap());
        assert_eq!(16384 - 1, u32::try_from_column_str("XFD").unwrap());
        assert_eq!(17603 - 1, u32::try_from_column_str("ZAA").unwrap());
        assert_eq!(18253 - 1, u32::try_from_column_str("ZZA").unwrap());

        assert_eq!(1, u!("B"));
        assert_eq!(1, u!("ZZA") - u!("ZYZ"));
        assert_eq!(1, u!("ZZZ") - u!("ZZY"));
        assert_eq!(1, u!("AAAA") - u!("ZZZ"));
        assert_eq!(1, u!("ZZZA") - u!("ZZYZ"));
        assert_eq!(1, u!("ZZAA") - u!("ZYZZ"));
        assert_eq!(1, u!("AAAAA") - u!("ZZZZ"));
    }

    #[test]
    fn to_le() {
        assert_eq!(num_to_column_le(&25), vec![25]);
        assert_eq!(num_to_column_le(&702), vec![0, 1, 1]);
        assert_eq!(num_to_column_le(&17602), vec![0, 1, 26]);
    }

    #[test]
    fn to_column_string() {
        assert_eq!("A", (0 as u8).to_column_string());
        assert_eq!("B", (1 as u8).to_column_string());
        assert_eq!("AA", (26 as u8).to_column_string());
        assert_eq!("IW", (256 as u32).to_column_string());
        assert_eq!("XFD", (16384u32 - 1).to_column_string());
        assert_eq!("ZAA", (17603u32 - 1).to_column_string());
        assert_eq!("ZZA", (18253u32 - 1).to_column_string());
    }

    #[test]
    fn s2s() {
        macro_rules! s2s {
            ($s:literal) => {
                assert_eq!($s, u64::try_from_column_str($s).unwrap().to_column_string());
            };
        }

        s2s!("A");
        s2s!("AA");
        s2s!("ZZ");
        s2s!("AZ");
        s2s!("ZA");
        s2s!("AAA");
        s2s!("ZZZ");
        s2s!("AAAAAAAAAAA");
    }

    #[test]
    fn u2u() {
        macro_rules! u2u {
            ($u:expr) => {
                assert_eq!(
                    $u as u64,
                    u64::try_from_column_str(&($u as u64).to_column_string()).unwrap()
                );
            };
        }

        u2u!(0);
        u2u!(1);
        u2u!(255);
        u2u!(1000);
        u2u!(1000000);
    }

    #[test]
    fn to_colmun() {
        assert_eq!("A1", (0, 0).to_cell_string());
        assert_eq!("AA52", (51, 26).to_cell_string());
    }
}
