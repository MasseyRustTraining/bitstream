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

impl End {
    #[cfg(test)]
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

        let value = self.take();
        match value {
            Empty => {
                if len < NCHUNK {
                    *self = Single(End { bits, len });
                } else {
                    let back = End::default();
                    let mut q = VecDeque::with_capacity(1);
                    q.push_back(bits);
                    let front = End::default();
                    *self = Multiple { back, q, front };
                }
            }
            Single(mut end) => {
                if len + end.len < NCHUNK {
                    end.bits |= bits << end.len;
                    end.len += len;
                    *self = Single(end);
                } else {
                    let used = NCHUNK - end.len;
                    end.bits |= (bits & mask(used)) << end.len as u32;
                    let mut q = VecDeque::with_capacity(1);
                    q.push_back(end.bits);
                    end.bits = bits >> used as u32;
                    end.len = len - used;

                    let back = end;
                    let front = End::default();
                    *self = Multiple { back, q, front };
                }
            }
            Multiple {
                mut back,
                mut q,
                front,
            } => {
                if len + back.len < NCHUNK {
                    back.bits |= bits << back.len;
                    back.len += len;
                    *self = Multiple { back, q, front };
                } else {
                    let used = NCHUNK - back.len;
                    back.bits |= (bits & mask(used)) << back.len as u32;
                    q.push_back(back.bits);
                    back.bits = bits >> used as u32;
                    back.len = len - used;

                    *self = Multiple { back, q, front };
                }
            }
        }
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
