//! Fenwick 树（Binary Indexed Tree）：支持前缀和与点更新，O(log n)

#[derive(Clone, Debug)]
pub struct Fenwick {
    n: usize,
    bit: Vec<i64>,
}

impl Fenwick {
    pub fn new(n: usize) -> Self { Self { n, bit: vec![0; n + 1] } }

    pub fn add(&mut self, mut idx: usize, delta: i64) {
        // 1-based
        idx += 1;
        while idx <= self.n { self.bit[idx] += delta; idx += idx & (!idx + 1); }
    }

    pub fn sum_prefix(&self, mut idx: usize) -> i64 {
        // sum [0..=idx]
        let mut res = 0i64;
        idx += 1;
        let mut i = idx;
        while i > 0 { res += self.bit[i]; i &= i - 1; }
        res
    }

    pub fn range_sum(&self, l: usize, r: usize) -> i64 {
        if r < l { return 0; }
        self.sum_prefix(r) - if l == 0 { 0 } else { self.sum_prefix(l - 1) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fenwick_basic() {
        let mut fw = Fenwick::new(5);
        fw.add(0, 1);
        fw.add(1, 2);
        fw.add(2, 3);
        fw.add(3, 4);
        fw.add(4, 5);
        assert_eq!(fw.sum_prefix(4), 15);
        assert_eq!(fw.range_sum(1, 3), 9);
    }
}


