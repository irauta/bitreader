// Copyright 2015 Ilkka Rauta
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! BitReader is a helper type to extract strings of bits from a slice of bytes.
//!
//! Here is how you read first a single bit, then three bits and finally four bits from a byte
//! buffer:
//!
//! ```
//! use bitreader::BitReader;
//!
//! let slice_of_u8 = &[0b1000_1111];
//! let mut reader = BitReader::new(slice_of_u8);
//!
//! // You probably should use try! or some other error handling mechanism in real code if the
//! // length of the input is not known in advance.
//! let a_single_bit = reader.read_u8(1).unwrap(); // 1
//! let more_bits = reader.read_u8(3).unwrap(); // 0
//! let last_bits_of_byte = reader.read_u8(4).unwrap(); // 0b1111
//! ```
//! You can naturally read bits from longer buffer of data than just a single byte.
//!
//! As you read bits, the internal cursor of BitReader moves on along the stream of bits. Little
//! endian format is assumed when reading the multi-byte values. BitReader supports reading maximum
//! of 64 bits at a time (with read_u64). Reading signed values directly is not supported at the
//! moment.
//!
//! The reads do not need to be aligned in any particular way.
//!
//! Reading zero bits is a no-op.
//!
//! You can also skip over a number of bits, in which case there is no arbitrary small limits like
//! when reading the values to a variable. However, you can not seek past the end of the slice,
//! either when reading or when skipping bits.
//!
//! Note that the code will likely not work correctly if the slice is longer than 2^61 bytes, but
//! exceeding that should be pretty unlikely. Let's get back to this when people read exabytes of
//! information one bit at a time.

use std::fmt;
use std::error::Error;
use std::result;

/// BitReader reads data from a byte slice at the granularity of a single bit.
pub struct BitReader<'a> {
    bytes: &'a [u8],
    /// Position from the start of the slice, counted as bits instead of bytes
    position: u64,
}

impl<'a> BitReader<'a> {
    /// Construct a new BitReader from a byte slice. The returned reader lives at most as long as
    /// the slice given to is valid.
    pub fn new(bytes: &'a [u8]) -> BitReader<'a> {
        BitReader {
            bytes: bytes,
            position: 0
        }
    }

    /// Read at most 8 bits into a u8.
    pub fn read_u8(&mut self, bit_count: u8) -> Result<u8> {
        let value = try!(self.read_value(bit_count, 8));
        Ok((value & 0xff) as u8)
    }

    /// Read at most 16 bits into a u16.
    pub fn read_u16(&mut self, bit_count: u8) -> Result<u16> {
        let value = try!(self.read_value(bit_count, 16));
        Ok((value & 0xffff) as u16)
    }

    /// Read at most 32 bits into a u32.
    pub fn read_u32(&mut self, bit_count: u8) -> Result<u32> {
        let value = try!(self.read_value(bit_count, 32));
        Ok((value & 0xffffffff) as u32)
    }

    /// Read at most 64 bits into a u64.
    pub fn read_u64(&mut self, bit_count: u8) -> Result<u64> {
        let value = try!(self.read_value(bit_count, 64));
        Ok(value)
    }

    /// Read at most 8 bits into a i8.
    /// Assumes the bits are stored in two's complement format.
    pub fn read_i8(&mut self, bit_count: u8) -> Result<i8> {
        let value = try!(self.read_signed_value(bit_count, 8));
        Ok((value & 0xff) as i8)
    }

    /// Read at most 16 bits into a i16.
    /// Assumes the bits are stored in two's complement format.
    pub fn read_i16(&mut self, bit_count: u8) -> Result<i16> {
        let value = try!(self.read_signed_value(bit_count, 16));
        Ok((value & 0xffff) as i16)
    }

    /// Read at most 32 bits into a i32.
    /// Assumes the bits are stored in two's complement format.
    pub fn read_i32(&mut self, bit_count: u8) -> Result<i32> {
        let value = try!(self.read_signed_value(bit_count, 32));
        Ok((value & 0xffffffff) as i32)
    }

    /// Read at most 64 bits into a i64.
    /// Assumes the bits are stored in two's complement format.
    pub fn read_i64(&mut self, bit_count: u8) -> Result<i64> {
        let value = try!(self.read_signed_value(bit_count, 64));
        Ok(value)
    }

    /// Skip arbitrary number of bits. However, you can skip at most to the end of the byte slice.
    pub fn skip(&mut self, bit_count: u32) -> Result<()> {
        let end_position = self.position + bit_count as u64;
        if end_position > self.bytes.len() as u64 * 8 {
            return Err(BitReaderError::NotEnoughData);
        }
        self.position = end_position;
        Ok(())
    }

    /// Returns the position of the cursor, or how many bits have been read so far.
    pub fn position(&self) -> u64 {
        self.position
    }

    /// Helper to make sure the "bit cursor" is exactly at the beginning of a byte, or at specific
    /// multi-byte alignment position.
    ///
    /// For example `reader.is_aligned(1)` returns true if exactly n bytes, or n * 8 bits, has been
    /// read. Similarly, `reader.is_aligned(4)` returns true if exactly n * 32 bits, or n 4-byte
    /// sequences has been read.
    ///
    /// This function can be used to validate the data is being read properly, for example by
    /// adding invocations wrapped into `debug_assert!()` to places where it is known the data
    /// should be n-byte aligned.
    pub fn is_aligned(&self, alignment_bytes: u32) -> bool {
        self.position % (alignment_bytes as u64 * 8) == 0
    }

    fn read_signed_value(&mut self, bit_count: u8, maximum_count: u8) -> Result<i64> {
        let unsigned = try!(self.read_value(bit_count, maximum_count));
        // Fill the bits above the requested bits with all ones or all zeros,
        // depending on the sign bit.
        let sign_bit = unsigned >> (bit_count - 1) & 1;
        let high_bits = if sign_bit == 1 { -1 } else { 0 };
        Ok(high_bits << bit_count | unsigned as i64)
    }

    fn read_value(&mut self, bit_count: u8, maximum_count: u8) -> Result<u64> {
        if bit_count == 0 {
            return Ok(0);
        }
        if bit_count > maximum_count {
            return Err(BitReaderError::TooManyBitsForType);
        }
        let start_position = self.position;
        let end_position = self.position + bit_count as u64;
        if end_position > self.bytes.len() as u64 * 8 {
            return Err(BitReaderError::NotEnoughData);
        }

        let mut value: u64 = 0;

        for i in start_position..end_position {
            let byte_index = (i / 8) as usize;
            let byte = self.bytes[byte_index];
            let shift = 7 - (i % 8);
            let bit = (byte >> shift) as u64 & 1;
            value = (value << 1) | bit;
        }

        self.position = end_position;
        Ok(value)
    }
}

/// Result type for those BitReader operations that can fail.
pub type Result<T> = result::Result<T, BitReaderError>;

/// Error enumeration of BitReader errors.
#[derive(Debug,PartialEq,Copy,Clone)]
pub enum BitReaderError {
    /// Requested more bits than there are left in the byte slice at the current position.
    NotEnoughData,
    /// Requested more bits than the returned variable can hold, for example more than 8 bits when
    /// reading into a u8.
    TooManyBitsForType
}

impl Error for BitReaderError {
    fn description(&self) -> &str {
        match *self {
            BitReaderError::NotEnoughData => "Requested more bits than the byte slice has left",
            BitReaderError::TooManyBitsForType => "Requested more bits than the requested integer type can hold",
        }
    }
}

impl fmt::Display for BitReaderError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.description().fmt(fmt)
    }
}

/// Helper trait to allow reading bits into a variable with the help of type inference.
///
/// If you can't or want, for some reason, to use BitReader's read methods (`read_u8` etc.) but
/// want to rely on type inference instead, you can use the ReadInto trait. The trait is
/// implemented for all basic integer types (8/16/32/64 bits, signed/unsigned).
///
/// ```
/// use bitreader::{BitReader,ReadInto};
///
/// let slice_of_u8 = &[0b1100_0000];
/// let mut reader = BitReader::new(slice_of_u8);
///
/// struct Foo {
///     bar: u8
/// }
///
/// // No type mentioned here, instead the type of `bits` is inferred from the type of Foo::bar,
/// // and consequently the correct "overload" is used.
/// let bits = ReadInto::read(&mut reader, 2).unwrap();
///
/// let foo = Foo { bar: bits };
/// assert_eq!(foo.bar, 3)
/// ```
pub trait ReadInto {
    fn read(reader: &mut BitReader, bits: u8) -> Result<Self>;
}

// There's eight almost identical implementations, let's make this easier.
macro_rules! impl_read_into {
    ($T:ty, $method:ident) => (
        impl ReadInto for $T {
            fn read(reader: &mut BitReader, bits: u8) -> Result<Self> {
                reader.$method(bits)
            }
        }
    )
}

impl_read_into!(u8, read_u8);
impl_read_into!(u16, read_u16);
impl_read_into!(u32, read_u32);
impl_read_into!(u64, read_u64);

impl_read_into!(i8, read_i8);
impl_read_into!(i16, read_i16);
impl_read_into!(i32, read_i32);
impl_read_into!(i64, read_i64);


#[test]
fn read_buffer() {
    let bytes = &[
        0b1011_0101, 0b0110_1010, 0b1010_1100, 0b1001_1001,
        0b1001_1001, 0b1001_1001, 0b1001_1001, 0b1110_0111,
    ];

    let mut reader = BitReader::new(bytes);

    assert_eq!(reader.read_u8(1).unwrap(), 0b1);
    assert_eq!(reader.read_u8(1).unwrap(), 0b0);
    assert_eq!(reader.read_u8(2).unwrap(), 0b11);

    assert_eq!(reader.read_u8(4).unwrap(), 0b0101);

    assert!(reader.is_aligned(1));

    assert_eq!(reader.read_u8(3).unwrap(), 0b11);
    assert_eq!(reader.read_u16(10).unwrap(), 0b01_0101_0101);
    assert_eq!(reader.read_u8(3).unwrap(), 0b100);

    assert!(reader.is_aligned(1));

    assert_eq!(reader.read_u32(32).unwrap(), 0b1001_1001_1001_1001_1001_1001_1001_1001);

    assert_eq!(reader.read_u8(4).unwrap(), 0b1110);
    assert_eq!(reader.read_u8(3).unwrap(), 0b011);
    assert_eq!(reader.read_u8(1).unwrap(), 0b1);

    // Could also be 8 at this point!
    assert!(reader.is_aligned(4));
}

#[test]
fn try_all_sizes() {
    let bytes = &[
        0x4a, 0x1e, 0x39, 0xbb, 0xd0, 0x07, 0xca, 0x9a,
        0xa6, 0xba, 0x25, 0x52, 0x6f, 0x0a, 0x6a, 0xba,
    ];

    let mut reader = BitReader::new(bytes);
    assert_eq!(reader.read_u64(64).unwrap(), 0x4a1e39bbd007ca9a);
    assert_eq!(reader.read_u64(64).unwrap(), 0xa6ba25526f0a6aba);

    let mut reader = BitReader::new(bytes);
    assert_eq!(reader.read_u32(32).unwrap(), 0x4a1e39bb);
    assert_eq!(reader.read_u32(32).unwrap(), 0xd007ca9a);
    assert_eq!(reader.read_u32(32).unwrap(), 0xa6ba2552);
    assert_eq!(reader.read_u32(32).unwrap(), 0x6f0a6aba);

    let mut reader = BitReader::new(bytes);
    assert_eq!(reader.read_u16(16).unwrap(), 0x4a1e);
    assert_eq!(reader.read_u16(16).unwrap(), 0x39bb);
    assert_eq!(reader.read_u16(16).unwrap(), 0xd007);
    assert_eq!(reader.read_u16(16).unwrap(), 0xca9a);
    assert_eq!(reader.read_u16(16).unwrap(), 0xa6ba);
    assert_eq!(reader.read_u16(16).unwrap(), 0x2552);
    assert_eq!(reader.read_u16(16).unwrap(), 0x6f0a);
    assert_eq!(reader.read_u16(16).unwrap(), 0x6aba);

    let mut reader = BitReader::new(&bytes[..]);
    for byte in bytes {
        assert_eq!(reader.read_u8(8).unwrap(), *byte);
    }
}

#[test]
fn skipping_and_zero_reads() {
    let bytes = &[
        0b1011_0101, 0b1110_1010, 0b1010_1100,
    ];

    let mut reader = BitReader::new(bytes);

    assert_eq!(reader.read_u8(4).unwrap(), 0b1011);
    // Reading zero bits should be a no-op
    assert_eq!(reader.read_u8(0).unwrap(), 0b0);
    assert_eq!(reader.read_u8(4).unwrap(), 0b0101);
    reader.skip(3).unwrap(); // 0b111
    assert_eq!(reader.read_u16(10).unwrap(), 0b0101010101);
    assert_eq!(reader.read_u8(3).unwrap(), 0b100);
}

#[test]
fn errors() {
    let bytes = &[
        0b1011_0101, 0b1110_1010, 0b1010_1100,
    ];

    let mut reader = BitReader::new(bytes);
    assert_eq!(reader.read_u8(4).unwrap(), 0b1011);
    assert_eq!(reader.read_u8(9).unwrap_err(), BitReaderError::TooManyBitsForType);
    // If an error happens, it should be possible to resume as if nothing had happened
    assert_eq!(reader.read_u8(4).unwrap(), 0b0101);

    let mut reader = BitReader::new(bytes);
    assert_eq!(reader.read_u8(4).unwrap(), 0b1011);
    // Same with this error
    assert_eq!(reader.read_u32(21).unwrap_err(), BitReaderError::NotEnoughData);
    assert_eq!(reader.read_u8(4).unwrap(), 0b0101);
}

#[test]
fn signed_values() {
    let from = -2048;
    let to = 2048;
    for x in from..to {
        let bytes = &[
            (x >> 8) as u8,
            x as u8,
        ];
        let mut reader = BitReader::new(bytes);
        assert_eq!(reader.read_u8(4).unwrap(), if x < 0 { 0b1111 } else { 0 });
        assert_eq!(reader.read_i16(12).unwrap(), x);
    }
}
