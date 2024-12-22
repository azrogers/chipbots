use std::{
    io::Cursor,
    ops::{Index, IndexMut},
};

use anyhow::Result;
use byteorder::{BigEndian, ReadBytesExt};

#[repr(transparent)]
pub struct Memory<const N: usize> {
    ram: [u8; N],
}

impl<const N: usize> Default for Memory<N> {
    fn default() -> Self {
        Memory { ram: [0; N] }
    }
}

impl<const N: usize> Index<u16> for Memory<N> {
    type Output = u8;

    fn index(&self, index: u16) -> &Self::Output {
        &self.ram[index as usize]
    }
}

impl<const N: usize> IndexMut<u16> for Memory<N> {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        &mut self.ram[index as usize]
    }
}

impl<const N: usize> Memory<N> {
    pub fn memcpy(self: &mut Memory<N>, src: &[u8], to: u16) {
        self.ram[to as usize..(to as usize + src.len())].clone_from_slice(src)
    }

    pub fn next_instruction(self: &Memory<N>, counter: &mut u16) -> Result<u16> {
        let from = *counter as usize;
        assert!(from < N);
        let mut cursor = Cursor::new(&self.ram[from..]);
        let result = cursor.read_u16::<BigEndian>()?;
        *counter += 2;
        Ok(result)
    }
}
