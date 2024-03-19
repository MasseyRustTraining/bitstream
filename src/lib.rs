use std::collections::VecDeque;

type Chunk = u64;

#[derive(Default)]
pub struct BitStream {
    /// Each chunk is a sequence of bits ordered LSB→MSB.
    /// (Lowest-order bits are first in and first out.)
    /// Partial chunks are right-justified.
    q: VecDeque<Chunk>,

    /// Number of used bits in the front and back chunk of
    /// the queue.
    used: (usize, usize),

    /// Number of bits in the queue.
    len: usize,
}

impl BitStream {
    const NCHUNK: usize = 8 * std::mem::size_of::<Chunk>();

    fn mask(len: usize) -> u64 {
        if len == 64 {
            return !0;
        }
        (1 << len as u32) - 1
    }

    #[cfg(test)]
    /// If the queue length is:
    /// * 0 chunks: these should be 0.
    /// * 1 chunk: these should be the same as [len].
    /// * 2 or more chunks: [len] should be
    ///       NCHUNK * (q.len() - 2) + used.0 + used.1
    pub fn check_length_invariant(&self) {
        match self.q.len() {
            0 => assert_eq!(self.used, (0, 0)),
            1 => assert_eq!(self.used, (self.len, self.len)),
            n => {
                let len = Self::NCHUNK * (n - 2) + self.used.0 + self.used.1;
                assert_eq!(self.len, len);
            }
        }
    }

    pub fn insert<T: Into<Chunk>>(&mut self, x: T, mut len: usize) {
        assert!(len <= 8 * std::mem::size_of::<T>());
        if len == 0 {
            return;
        }
        let mut bits = x.into() & Self::mask(len);
        
        if self.q.is_empty() {
            self.used = (len, len);
            self.q.push_back(bits);
            self.len += len;
            return;
        }

        let nused = self.used.0;
        if nused > 0 {
            // Fill into back chunk.
            let mut chunk = self.q.pop_back().unwrap();
            let nbits = usize::min(Self::NCHUNK - nused, len);
            chunk |= (bits & Self::mask(nbits)) << nused as u32;
            bits >>= nbits as u32;
            self.q.push_back(chunk);
            self.len += nbits;
            self.used.0 += nbits;
            if self.q.len() == 1 {
                self.used.1 = self.used.0;
            }
            len -= nbits;
        }
        if len > 0 {
            // Start a new back chunk.
            self.q.push_back(bits);
            self.used.0 = len;
            if self.q.len() == 1 {
                self.used.1 = self.used.0;
            }
            self.len += len;
        }
    }

    /// Length in bits.
    pub fn len(&self) -> usize {
        self.len
    }


    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

#[test]
fn test_insert() {
    let mut bs = BitStream::default();
    bs.insert(0b10010u8, 5);
    assert_eq!(bs.len(), 5);
    bs.check_length_invariant();

    let mut len = 5;
    for _ in 0..40 {
        bs.insert(0b01110u8, 5);
        len += 5;
        assert_eq!(bs.len(), len);
        bs.check_length_invariant();
    }
}
