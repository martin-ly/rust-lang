//! Sparse Table（稀疏表）：支持幂等操作的静态区间查询，如 RMQ(min/max)、GCD、按位与/或/异或。

#[derive(Clone, Debug)]
pub struct SparseTable<T> {
    pub n: usize,
    pub log: Vec<usize>,
    pub st: Vec<Vec<T>>, // st[k][i] = op on [i, i + 2^k)
}

impl<T: Copy> SparseTable<T> {
    pub fn build<F>(arr: &[T], mut op: F) -> Self
    where
        F: FnMut(T, T) -> T + Copy,
    {
        let n = arr.len();
        let mut log = vec![0usize; n + 1];
        for i in 2..=n {
            log[i] = log[i / 2] + 1;
        }
        let kmax = log[n] + 1;
        let mut st: Vec<Vec<T>> = vec![vec![arr[0]; n]; kmax];
        st[0].clone_from_slice(arr);
        let mut k = 1usize;
        while k < kmax {
            let len = 1usize << k;
            let half = len >> 1;
            for i in 0..=(n.saturating_sub(len)) {
                st[k][i] = op(st[k - 1][i], st[k - 1][i + half]);
            }
            k += 1;
        }
        Self { n, log, st }
    }

    /// 查询幂等操作（如 min/max/gcd）： op(op(a,b),c) = op(a,op(b,c)) 且满足可重复覆盖
    pub fn query_idempotent<F>(&self, l: usize, r_exclusive: usize, mut op: F) -> T
    where
        F: FnMut(T, T) -> T,
    {
        assert!(l < r_exclusive && r_exclusive <= self.n);
        let len = r_exclusive - l;
        let k = self.log[len];
        let left = self.st[k][l];
        let right = self.st[k][r_exclusive - (1usize << k)];
        op(left, right)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sparse_table_min() {
        let a = [5, 2, 4, 7, 1, 3, 6, 0];
        let st = SparseTable::build(&a, |x, y| x.min(y));
        assert_eq!(st.query_idempotent(0, 4, |x, y| x.min(y)), 2);
        assert_eq!(st.query_idempotent(2, 7, |x, y| x.min(y)), 1);
        assert_eq!(st.query_idempotent(4, 8, |x, y| x.min(y)), 0);
    }
}
