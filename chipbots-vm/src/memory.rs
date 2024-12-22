use anyhow::Result;
use zerocopy::{FromBytes, FromZeros, IntoBytes, KnownLayout};

#[derive(FromZeros, IntoBytes)]
#[repr(transparent)]
pub struct Memory<const N: usize> {
    ram: [u8; N],
}

impl<const N: usize> Default for Memory<N> {
    fn default() -> Self {
        Memory { ram: [0; N] }
    }
}

impl<const N: usize> Memory<N> {
    pub fn next<T: FromBytes + KnownLayout + 'static>(
        self: &Memory<N>,
        counter: &mut u16,
    ) -> Result<T> {
        let from = *counter as usize;
        assert!(from < N);
        let result =
            T::read_from_bytes(&self.ram[from..]).map_err(|e| anyhow::Error::msg(e.to_string()))?;
        *counter = *counter + (std::mem::size_of::<T>() as u16);
        Ok(result)
    }
}
