use lccc_siphash::SipHasher;
use std::collections::VecDeque;

pub struct RandUnit {
    enthropy_pool: [u64; 64],
    head: usize,
    tail: usize,
    enthropy: [u64; 8],
    offset: usize,
}

impl RandUnit {
    pub const fn new() -> Self {
        Self {
            enthropy_pool: [0; 64],
            head: 0,
            tail: 0,
            enthropy: [0; 8],
            offset: 0,
        }
    }

    fn push_enthropy(&mut self, x: u64) {
        if (self.tail.wrapping_add(1) & 63) != (self.head & 63) {
            self.enthropy_pool[self.tail & 63] = x;
            self.tail = self.tail.wrapping_add(1);
            for i in 0..8 {
                self.enthropy[i] ^= x.rotate_right(((self.offset.wrapping_add(i)) & 63) as u32);
            }
            self.offset = self.offset.wrapping_mul(11).wrapping_add(17);
        }
    }

    fn count_enthropy(&self) -> u32 {
        self.enthropy
            .iter()
            .copied()
            .fold(0, |x, y| x ^ y)
            .count_ones()
    }
}
