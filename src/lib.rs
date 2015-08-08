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

use std::fmt;
use std::error::Error;
use std::result;

pub struct BitReader<'a> {
    bytes: &'a [u8],
    /// Position from the start of the slice, counted as bits instead of bytes
    position: u64,
}

impl<'a> BitReader<'a> {
    pub fn new(bytes: &'a [u8]) -> BitReader<'a> {
        BitReader {
            bytes: bytes,
            position: 0
        }
    }

    pub fn read_u8(&mut self, bit_count: u8) -> Result<u8> {
        let value = try!(self.read_value(bit_count, 8));
        Ok((value & 0xff) as u8)
    }

    pub fn read_u16(&mut self, bit_count: u8) -> Result<u16> {
        let value = try!(self.read_value(bit_count, 16));
        Ok((value & 0xffff) as u16)
    }

    pub fn read_u32(&mut self, bit_count: u8) -> Result<u32> {
        let value = try!(self.read_value(bit_count, 32));
        Ok((value & 0xffffffff) as u32)
    }

    pub fn read_u64(&mut self, bit_count: u8) -> Result<u64> {
        let value = try!(self.read_value(bit_count, 64));
        Ok(value)
    }

    pub fn skip(&mut self, bit_count: u32) -> Result<()> {
        let end_position = self.position + bit_count as u64;
        if end_position > self.bytes.len() as u64 * 8 {
            return Err(BitReaderError::NotEnoughData);
        }
        self.position = end_position;
        Ok(())
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

pub type Result<T> = result::Result<T, BitReaderError>;

#[derive(Debug,PartialEq)]
pub enum BitReaderError {
    NotEnoughData,
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

    assert_eq!(reader.read_u8(3).unwrap(), 0b11);
    assert_eq!(reader.read_u16(10).unwrap(), 0b01_0101_0101);
    assert_eq!(reader.read_u8(3).unwrap(), 0b100);

    assert_eq!(reader.read_u32(32).unwrap(), 0b1001_1001_1001_1001_1001_1001_1001_1001);

    assert_eq!(reader.read_u8(4).unwrap(), 0b1110);
    assert_eq!(reader.read_u8(3).unwrap(), 0b011);
    assert_eq!(reader.read_u8(1).unwrap(), 0b1);
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
