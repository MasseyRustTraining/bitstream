use std::collections::VecDeque;

/// The que is a [VecDeque] of these chunks.
type Chunk = u64;

/// Number of bits in a chunk.
const NCHUNK: usize = 8 * std::mem::size_of::<Chunk>();

/// Bitmask of `len` bits.
fn mask(len: usize) -> u64 {
    if len == 64 {
        return !0;
    }
    (1 << len as u32) - 1
}

/// An "end" of the queue may be partially filled.
#[derive(Debug, Clone, Default)]
pub struct End {
    len: usize,
    bits: Chunk,
}

#[cfg(test)]
impl End {
    pub fn check_invariant(&self) {
        assert!(self.len < NCHUNK);
    }
}

#[derive(Debug, Clone, Default)]
/// Each chunk is a sequence of bits ordered LSB→MSB.
/// (Lowest-order bits are first in and first out.)
/// Partial chunks are right-justified.
pub enum BitStream {
    /// Queue is empty.
    #[default]
    Empty,
    /// Queue is length one, so back and front are the same.
    Single(End),
    /// Queue is length two+, so back and front are different.
    Multiple {
        back: End,
        q: VecDeque<Chunk>,
        front: End,
    },
}
use BitStream::*;

impl BitStream {
    pub fn take(&mut self) -> Self {
        std::mem::replace(self, Empty)
    }

    pub fn insert<T: Into<Chunk>>(&mut self, x: T, len: usize) {
        assert!(len <= 8 * std::mem::size_of::<T>());
        if len == 0 {
            return;
        }
        let bits = x.into() & mask(len);

        let insert_with_carry = |end: &mut End| -> Option<Chunk> {
            if len + end.len < NCHUNK {
                end.bits |= bits << end.len;
                end.len += len;
                None
            } else {
                let used = NCHUNK - end.len;
                end.bits |= (bits & mask(used)) << end.len as u32;
                let carry = end.bits;
                end.bits = bits >> used as u32;
                end.len = len - used;
                Some(carry)
            }
        };

        let to_multiple = |end: End, carry: Chunk| -> BitStream {
            let back = end;
            let mut q = VecDeque::with_capacity(1);
            q.push_back(carry);
            let front = End::default();
            Multiple { back, q, front }
        };

        let promote = |mut end: End| -> BitStream {
            match insert_with_carry(&mut end) {
                None => Single(end),
                Some(carry) => to_multiple(end, carry),
            }
        };

        let value = self.take();
        *self = match value {
            Empty => {
                let end = End::default();
                promote(end)
            }
            Single(end) => promote(end),
            Multiple {
                mut back,
                mut q,
                front,
            } => match insert_with_carry(&mut back) {
                None => Multiple { back, q, front },
                Some(carry) => {
                    q.push_back(carry);
                    Multiple { back, q, front }
                }
            },
        };
    }

    pub fn extract(&mut self, _len: usize) -> Option<u64> {
        todo!()
    }

    /// Length in bits.
    pub fn len(&self) -> usize {
        match self {
            Empty => 0,
            Single(end) => end.len,
            Multiple { back, q, front } => back.len + q.len() * NCHUNK + front.len,
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Empty)
    }

    #[cfg(test)]
    fn check_invariant(&self) {
        match self {
            Empty => (),
            Single(end) => end.check_invariant(),
            Multiple { back, front, .. } => {
                back.check_invariant();
                front.check_invariant();
            }
        }
    }
}

#[test]
fn test_insert() {
    let mut bs = BitStream::default();
    bs.insert(0b10010u8, 5);
    assert_eq!(bs.len(), 5);
    bs.check_invariant();

    let mut len = 5;
    for _ in 0..40 {
        bs.insert(0b01110u8, 5);
        len += 5;
        assert_eq!(bs.len(), len);
    }
}

#[test]
fn test_extract() {
    let mut bs = BitStream::default();
    let mut len = 0;
    for _ in 0..80 {
        bs.insert(0b010u8, 3);
        len += 3;
    }

    for _ in 0..79 {
        let bits = bs.extract(3).unwrap();
        assert_eq!(bits, 0b010);
        len -= 3;
        assert_eq!(bs.len(), len);
        bs.check_invariant();
    }
    assert!(bs.is_empty());
    assert!(bs.extract(1).is_none());
}
