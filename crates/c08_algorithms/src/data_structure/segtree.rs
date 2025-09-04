//! Segment Tree（线段树）：点更新、区间和查询，O(log n)

#[derive(Clone, Debug)]
pub struct SegmentTree {
    n: usize,
    tree: Vec<i64>,
}

impl SegmentTree {
    pub fn from_slice(arr: &[i64]) -> Self {
        let n = arr.len();
        let mut st = Self { n, tree: vec![0; n.next_power_of_two() * 4] };
        st.build(1, 0, n - 1, arr);
        st
    }

    fn build(&mut self, node: usize, l: usize, r: usize, arr: &[i64]) {
        if l == r { self.tree[node] = arr[l]; return; }
        let mid = (l + r) / 2;
        self.build(node * 2, l, mid, arr);
        self.build(node * 2 + 1, mid + 1, r, arr);
        self.tree[node] = self.tree[node * 2] + self.tree[node * 2 + 1];
    }

    pub fn update_point(&mut self, idx: usize, val: i64) { self.update(1, 0, self.n - 1, idx, val); }

    fn update(&mut self, node: usize, l: usize, r: usize, idx: usize, val: i64) {
        if l == r { self.tree[node] = val; return; }
        let mid = (l + r) / 2;
        if idx <= mid { self.update(node * 2, l, mid, idx, val); } else { self.update(node * 2 + 1, mid + 1, r, idx, val); }
        self.tree[node] = self.tree[node * 2] + self.tree[node * 2 + 1];
    }

    pub fn query_sum(&self, ql: usize, qr: usize) -> i64 { self.query(1, 0, self.n - 1, ql, qr) }

    fn query(&self, node: usize, l: usize, r: usize, ql: usize, qr: usize) -> i64 {
        if ql > r || qr < l { return 0; }
        if ql <= l && r <= qr { return self.tree[node]; }
        let mid = (l + r) / 2;
        self.query(node * 2, l, mid, ql, qr) + self.query(node * 2 + 1, mid + 1, r, ql, qr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_segtree_sum() {
        let mut st = SegmentTree::from_slice(&[1,2,3,4,5]);
        assert_eq!(st.query_sum(1, 3), 9);
        st.update_point(2, 10);
        assert_eq!(st.query_sum(1, 3), 16);
    }
}


