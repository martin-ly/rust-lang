//! 贪心算法：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;
use std::collections::{BinaryHeap, HashMap};

// =========================
// 区间调度（最大不重叠区间数）
// =========================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Interval {
    pub start: i64,
    pub end: i64,
}

/// 同步：按结束时间排序选择
pub fn interval_scheduling_sync(mut intervals: Vec<Interval>) -> Vec<Interval> {
    intervals.sort_by_key(|iv| iv.end);
    let mut result = Vec::new();
    let mut current_end = i64::MIN;
    for iv in intervals {
        if iv.start >= current_end {
            result.push(iv);
            current_end = iv.end;
        }
    }
    result
}

/// 并行：并行排序后线性选择
pub fn interval_scheduling_parallel(mut intervals: Vec<Interval>) -> Vec<Interval> {
    intervals.par_sort_unstable_by_key(|iv| iv.end);
    let mut result = Vec::new();
    let mut current_end = i64::MIN;
    for iv in intervals {
        if iv.start >= current_end {
            result.push(iv);
            current_end = iv.end;
        }
    }
    result
}

/// 异步：spawn_blocking 包裹
pub async fn interval_scheduling_async(intervals: Vec<Interval>) -> Result<Vec<Interval>> {
    Ok(tokio::task::spawn_blocking(move || interval_scheduling_parallel(intervals)).await?)
}

// =========================
// 零钱兑换（最少硬币数，贪心对部分币值系统正确）
// =========================

/// 同步：对标准币值系统（如美分）正确
pub fn coin_change_greedy_sync(mut coins: Vec<i64>, mut amount: i64) -> Vec<i64> {
    coins.sort_unstable();
    coins.reverse();
    let mut res = Vec::new();
    for c in coins {
        while amount >= c {
            amount -= c;
            res.push(c);
        }
        if amount == 0 { break; }
    }
    res
}

/// 并行：并行预处理（排序），选择仍为线性
pub fn coin_change_greedy_parallel(mut coins: Vec<i64>, amount: i64) -> Vec<i64> {
    coins.par_sort_unstable();
    let coins: Vec<i64> = coins.into_iter().rev().collect();
    coin_change_greedy_sync(coins, amount)
}

/// 异步：spawn_blocking 包裹
pub async fn coin_change_greedy_async(coins: Vec<i64>, amount: i64) -> Result<Vec<i64>> {
    Ok(tokio::task::spawn_blocking(move || coin_change_greedy_parallel(coins, amount)).await?)
}

// =========================
// 分数背包（Fractional Knapsack）
// =========================

#[derive(Clone, Copy, Debug)]
pub struct Item {
    pub weight: f64,
    pub value: f64,
}

pub fn fractional_knapsack_sync(mut items: Vec<Item>, capacity: f64) -> f64 {
    items.sort_by(|a, b| (b.value / b.weight).partial_cmp(&(a.value / a.weight)).unwrap());
    let mut cap = capacity;
    let mut total = 0.0;
    for it in items {
        if cap <= 0.0 { break; }
        let take = it.weight.min(cap);
        total += (it.value / it.weight) * take;
        cap -= take;
    }
    total
}

pub fn fractional_knapsack_parallel(mut items: Vec<Item>, capacity: f64) -> f64 {
    items.par_sort_unstable_by(|a, b| (b.value / b.weight).partial_cmp(&(a.value / a.weight)).unwrap());
    fractional_knapsack_sync(items, capacity)
}

pub async fn fractional_knapsack_async(items: Vec<Item>, capacity: f64) -> Result<f64> {
    Ok(tokio::task::spawn_blocking(move || fractional_knapsack_parallel(items, capacity)).await?)
}

// =========================
// Huffman 编码（构建编码表/编码/解码）
// =========================

#[derive(Clone, Debug)]
pub struct HuffNode {
    freq: usize,
    ch: Option<u8>,
    left: Option<Box<HuffNode>>,
    right: Option<Box<HuffNode>>,
}

impl PartialEq for HuffNode { fn eq(&self, other: &Self) -> bool { self.freq == other.freq } }
impl Eq for HuffNode {}
impl PartialOrd for HuffNode { fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(other)) } }
impl Ord for HuffNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // 使 BinaryHeap 作为最小堆：频率小的优先（反转）
        other.freq.cmp(&self.freq)
    }
}

fn build_huffman_tree(freqs: &HashMap<u8, usize>) -> Option<Box<HuffNode>> {
    let mut heap: BinaryHeap<HuffNode> = BinaryHeap::new();
    for (&ch, &f) in freqs.iter() {
        heap.push(HuffNode { freq: f, ch: Some(ch), left: None, right: None });
    }
    if heap.is_empty() { return None; }
    while heap.len() > 1 {
        let a = heap.pop().unwrap();
        let b = heap.pop().unwrap();
        heap.push(HuffNode { freq: a.freq + b.freq, ch: None, left: Some(Box::new(a)), right: Some(Box::new(b)) });
    }
    heap.pop().map(Box::new)
}

fn build_codes_rec(node: &HuffNode, path: &mut Vec<char>, codes: &mut HashMap<u8, String>) {
    if let Some(ch) = node.ch {
        let code: String = if path.is_empty() { "0".to_string() } else { path.iter().collect() };
        codes.insert(ch, code);
        return;
    }
    if let Some(ref l) = node.left { path.push('0'); build_codes_rec(l, path, codes); path.pop(); }
    if let Some(ref r) = node.right { path.push('1'); build_codes_rec(r, path, codes); path.pop(); }
}

pub fn huffman_build_codes(input: &str) -> (HashMap<u8, String>, Option<Box<HuffNode>>) {
    let mut freqs: HashMap<u8, usize> = HashMap::new();
    for &b in input.as_bytes() { *freqs.entry(b).or_insert(0) += 1; }
    let tree = build_huffman_tree(&freqs);
    let mut codes = HashMap::new();
    if let Some(ref root) = tree { let mut path = Vec::new(); build_codes_rec(root, &mut path, &mut codes); }
    (codes, tree)
}

pub fn huffman_encode(input: &str, codes: &HashMap<u8, String>) -> String {
    let mut out = String::new();
    for &b in input.as_bytes() { out.push_str(codes.get(&b).map(String::as_str).unwrap_or("")); }
    out
}

pub fn huffman_decode(bits: &str, tree: &HuffNode) -> Vec<u8> {
    let mut res = Vec::new();
    if tree.ch.is_some() { // 单字符特殊情况
        if let Some(ch) = tree.ch { for _ in bits.chars() { res.push(ch); } }
        return res;
    }
    let mut cur = tree;
    for c in bits.chars() {
        cur = match c {
            '0' => cur.left.as_deref().unwrap_or(cur),
            '1' => cur.right.as_deref().unwrap_or(cur),
            _ => cur,
        };
        if let Some(ch) = cur.ch { res.push(ch); cur = tree; }
    }
    res
}

pub async fn huffman_build_codes_async(input: String) -> Result<(HashMap<u8, String>, Option<Box<HuffNode>>)> {
    Ok(tokio::task::spawn_blocking(move || huffman_build_codes(&input)).await?)
}

pub async fn huffman_encode_async(input: String, codes: HashMap<u8, String>) -> Result<String> {
    Ok(tokio::task::spawn_blocking(move || huffman_encode(&input, &codes)).await?)
}

pub async fn huffman_decode_async(bits: String, tree: Box<HuffNode>) -> Result<Vec<u8>> {
    Ok(tokio::task::spawn_blocking(move || huffman_decode(&bits, &tree)).await?)
}

// =========================
// 作业排序（deadline, profit）最大收益，单位时间/单机
// =========================

#[derive(Clone, Copy, Debug)]
pub struct Job { pub id: usize, pub deadline: usize, pub profit: i64 }

pub fn job_sequencing_max_profit(mut jobs: Vec<Job>) -> (i64, Vec<Option<usize>>) {
    if jobs.is_empty() { return (0, vec![]); }
    jobs.sort_by_key(|j| std::cmp::Reverse(j.profit));
    let max_d = jobs.iter().map(|j| j.deadline).max().unwrap_or(0);
    let mut slots: Vec<Option<usize>> = vec![None; max_d + 1]; // 1..=max_d 使用
    let mut total = 0i64;
    for j in jobs {
        let mut t = j.deadline.min(max_d);
        while t >= 1 {
            if slots[t].is_none() { slots[t] = Some(j.id); total += j.profit; break; }
            t -= 1;
        }
    }
    (total, slots)
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interval_scheduling() {
        let intervals = vec![
            Interval { start: 1, end: 3 },
            Interval { start: 2, end: 4 },
            Interval { start: 3, end: 5 },
            Interval { start: 0, end: 7 },
            Interval { start: 5, end: 9 },
        ];
        let r1 = interval_scheduling_sync(intervals.clone());
        let r2 = interval_scheduling_parallel(intervals.clone());
        assert_eq!(r1.len(), r2.len());
        assert!(!r1.is_empty());
    }

    #[test]
    fn test_coin_change_greedy() {
        let coins = vec![1, 5, 10, 25];
        let r1 = coin_change_greedy_sync(coins.clone(), 41);
        assert_eq!(r1.iter().sum::<i64>(), 41);
        assert!(r1.len() <= 5);

        let r2 = coin_change_greedy_parallel(coins.clone(), 41);
        assert_eq!(r2.iter().sum::<i64>(), 41);
    }

    #[test]
    fn test_fractional_knapsack() {
        let items = vec![
            Item { weight: 10.0, value: 60.0 },
            Item { weight: 20.0, value: 100.0 },
            Item { weight: 30.0, value: 120.0 },
        ];
        let best = fractional_knapsack_sync(items.clone(), 50.0);
        assert!((best - 240.0).abs() < 1e-9);
        let best2 = fractional_knapsack_parallel(items, 50.0);
        assert!((best2 - 240.0).abs() < 1e-9);
    }

    #[test]
    fn test_huffman_basic() {
        let s = "abracadabra";
        let (codes, tree) = huffman_build_codes(s);
        assert!(!codes.is_empty());
        let bits = huffman_encode(s, &codes);
        let decoded = huffman_decode(&bits, tree.as_ref().unwrap());
        assert_eq!(String::from_utf8(decoded).unwrap(), s);
    }

    #[test]
    fn test_job_sequencing() {
        let jobs = vec![
            Job { id: 1, deadline: 2, profit: 100 },
            Job { id: 2, deadline: 1, profit: 19 },
            Job { id: 3, deadline: 2, profit: 27 },
            Job { id: 4, deadline: 1, profit: 25 },
            Job { id: 5, deadline: 3, profit: 15 },
        ];
        let (profit, slots) = job_sequencing_max_profit(jobs);
        assert!(profit >= 127); // 期望最佳 142（1,3,5）
        assert!(slots.iter().filter(|s| s.is_some()).count() >= 2);
    }

    #[test]
    fn test_async_wrappers() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        let intervals = vec![Interval { start: 1, end: 2 }, Interval { start: 2, end: 3 }];
        let res = rt.block_on(async { interval_scheduling_async(intervals).await.unwrap() });
        assert!(!res.is_empty());

        let coins = vec![1, 2, 5, 10];
        let r = rt.block_on(async { coin_change_greedy_async(coins, 18).await.unwrap() });
        assert_eq!(r.iter().sum::<i64>(), 18);
    }
}

