use std::collections::VecDeque;

/// The bitstream is built of these chunks.
pub type Chunk = u64;

#[derive(Debug, Clone, Default)]
pub struct BitStream(Bits);

impl BitStream {
    pub fn take(&mut self) -> Self {
        let contents = self.0.take();
        Self(contents)
    }

    pub fn insert<T: Into<Chunk>>(&mut self, x: T, len: usize) {
        self.0.insert(x, len);
    }

    pub fn extract(&mut self, len: usize) -> Option<Chunk> {
        self.0.extract(len)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Number of bits in a chunk.
pub const NCHUNK: usize = 8 * std::mem::size_of::<Chunk>();

/// Bitmask of `len` bits.
fn mask(len: usize) -> Chunk {
    if len == NCHUNK {
        return !0;
    }
    (1 << len as u32) - 1
}

/// An "end" of the queue may be partially filled.
#[derive(Debug, Clone, Default)]
struct End {
    len: usize,
    bits: Chunk,
}

#[cfg(test)]
impl End {
    fn check_invariant(&self) {
        assert!(self.len < NCHUNK);
    }
}

#[derive(Debug, Clone, Default)]
/// Each chunk is a sequence of bits ordered LSB→MSB.
/// (Lowest-order bits are first in and first out.)
/// Partial chunks are right-justified.
enum Bits {
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
use Bits::*;

impl Bits {
    fn take(&mut self) -> Self {
        std::mem::replace(self, Empty)
    }

    fn insert<T: Into<Chunk>>(&mut self, x: T, len: usize) {
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

        let to_multiple = |end: End, carry: Chunk| -> Self {
            let back = end;
            let mut q = VecDeque::with_capacity(1);
            q.push_back(carry);
            let front = End::default();
            Multiple { back, q, front }
        };

        let promote = |mut end: End| -> Self {
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

    fn extract(&mut self, len: usize) -> Option<Chunk> {
        if len == 0 {
            return Some(0);
        }

        let canon = |repr: Self| -> Self {
            match repr {
                Empty => Empty,
                Single(end) => {
                    if end.len == 0 {
                        Empty
                    } else {
                        Single(end)
                    }
                }
                Multiple {
                    back,
                    mut q,
                    mut front,
                } => {
                    if front.len == NCHUNK {
                        q.push_front(front.bits);
                        front.len = 0;
                        front.bits = 0;
                    }
                    if q.is_empty() {
                        if back.len + front.len == 0 {
                            Empty
                        } else if back.len + front.len < NCHUNK {
                            front.bits |= back.bits << front.len as u32;
                            front.len += back.len;
                            Single(front)
                        } else {
                            Multiple { back, q, front }
                        }
                    } else {
                        Multiple { back, q, front }
                    }
                }
            }
        };

        let value = self.take();
        let (new_value, result) = match value {
            Empty => (Empty, None),
            Single(mut end) => {
                if len <= end.len {
                    let bits = end.bits & mask(len);
                    end.bits >>= len as u32;
                    end.len -= len;
                    (Single(end), Some(bits))
                } else {
                    (Single(end), None)
                }
            }
            Multiple {
                back,
                mut q,
                mut front,
            } => {
                if len <= front.len {
                    let bits = front.bits & mask(len);
                    front.bits >>= len as u32;
                    front.len -= len;
                    (Multiple { back, q, front }, Some(bits))
                } else if let Some(borrow) = q.pop_front() {
                    let needed = len - front.len;
                    let mut bits = borrow & mask(needed);
                    bits <<= front.len;
                    bits |= front.bits & mask(front.len);
                    front.bits = borrow >> needed as u32;
                    front.len = NCHUNK - needed;
                    (Multiple { back, q, front }, Some(bits))
                } else if len <= front.len + back.len {
                    assert!(q.is_empty());
                    front.bits |= back.bits << front.len as u32;
                    front.len += back.len;
                    let bits = front.bits & mask(len);
                    front.bits >>= len;
                    front.len -= len;
                    (Single(front), Some(bits))
                } else {
                    assert!(q.is_empty());
                    (Multiple { back, q, front }, None)
                }
            }
        };
        *self = canon(new_value);
        result
    }

    /// Length in bits.
    fn len(&self) -> usize {
        match self {
            Empty => 0,
            Single(end) => end.len,
            Multiple { back, q, front } => back.len + q.len() * NCHUNK + front.len,
        }
    }

    fn is_empty(&self) -> bool {
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
fn test_bits_insert() {
    let mut bs = Bits::default();
    bs.insert(0b10010u8, 5);
    assert_eq!(bs.len(), 5);
    bs.check_invariant();

    let mut len = 5;
    for _ in 0..40 {
        bs.insert(0b01110u8, 5);
        len += 5;
        assert_eq!(bs.len(), len);
        bs.check_invariant();
    }
}

#[test]
fn test_bits_extract() {
    let mut bs = Bits::default();
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
    assert_eq!(0b10, bs.extract(2).unwrap());
    assert!(!bs.is_empty());
    assert_eq!(0b0, bs.extract(1).unwrap());
    assert!(bs.is_empty());
    assert!(bs.extract(1).is_none());
}
