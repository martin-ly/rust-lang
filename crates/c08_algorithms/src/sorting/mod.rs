//! 排序算法：同步 / Rayon并行 / Tokio异步 统一接口

use anyhow::Result;
use rayon::prelude::*;
use rayon::slice::{ParallelSlice, ParallelSliceMut};

/// 排序算法类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortingAlgo {
    Quick,
    Merge,
    Heap,
}

/// 同步排序（原地）
pub fn sort_sync<T>(data: &mut [T], algo: SortingAlgo)
where
    T: Ord + Clone,
{
    match algo {
        SortingAlgo::Quick => quicksort(data),
        SortingAlgo::Merge => mergesort_in_place(data),
        SortingAlgo::Heap => heapsort(data),
    }
}

/// Rayon 并行排序（原地）
pub fn sort_parallel<T>(data: &mut [T], algo: SortingAlgo)
where
    T: Ord + Send,
{
    match algo {
        // 为了演示与稳定性，Quick/Heap 统一使用 Rayon 的并行排序
        SortingAlgo::Quick | SortingAlgo::Heap => data.par_sort_unstable(),
        SortingAlgo::Merge => data.par_sort(),
    }
}

/// Tokio 异步排序（接收与返回 Vec）
pub async fn sort_async<T>(mut data: Vec<T>, algo: SortingAlgo) -> Result<Vec<T>>
where
    T: Ord + Send + 'static,
{
    let handle = tokio::task::spawn_blocking(move || {
        match algo {
            SortingAlgo::Quick => data.sort_unstable(),
            SortingAlgo::Merge => data.sort(),
            SortingAlgo::Heap => heap_sort_vec(&mut data),
        }
        data
    });
    Ok(handle.await?)
}

// =========================
// 参考实现（教学版）
// =========================

fn quicksort<T: Ord>(data: &mut [T]) {
    if data.len() <= 1 {
        return;
    }
    let pivot_index = partition(data);
    let (left, right) = data.split_at_mut(pivot_index);
    quicksort(left);
    quicksort(&mut right[1..]);
}

fn partition<T: Ord>(data: &mut [T]) -> usize {
    let len = data.len();
    let pivot_index = len - 1;
    let mut store = 0;
    for i in 0..pivot_index {
        if data[i] <= data[pivot_index] {
            data.swap(i, store);
            store += 1;
        }
    }
    data.swap(store, pivot_index);
    store
}

fn mergesort_in_place<T: Ord + Clone>(data: &mut [T]) {
    let len = data.len();
    if len <= 1 {
        return;
    }
    let mid = len / 2;
    mergesort_in_place(&mut data[..mid]);
    mergesort_in_place(&mut data[mid..]);
    merge(data, mid);
}

fn merge<T: Ord + Clone>(data: &mut [T], mid: usize) {
    let buf: Vec<_> = data.to_vec();
    let (left, right) = buf.split_at(mid);
    let mut i = 0;
    let mut j = 0;
    for k in 0..data.len() {
        if i < left.len() && (j >= right.len() || left[i] <= right[j]) {
            data[k] = left[i].to_owned();
            i += 1;
        } else {
            data[k] = right[j].to_owned();
            j += 1;
        }
    }
}

fn heapsort<T: Ord>(data: &mut [T]) {
    build_max_heap(data);
    let mut end = data.len();
    while end > 1 {
        data.swap(0, end - 1);
        end -= 1;
        sift_down(data, 0, end);
    }
}

fn build_max_heap<T: Ord>(data: &mut [T]) {
    let len = data.len();
    if len <= 1 {
        return;
    }
    let mut start = (len - 2) / 2;
    loop {
        sift_down(data, start, len);
        if start == 0 { break; }
        start -= 1;
    }
}

fn sift_down<T: Ord>(data: &mut [T], mut root: usize, end: usize) {
    loop {
        let left = root * 2 + 1;
        if left >= end { break; }
        let mut swap_i = root;
        if data[swap_i] < data[left] { swap_i = left; }
        let right = left + 1;
        if right < end && data[swap_i] < data[right] { swap_i = right; }
        if swap_i == root { return; }
        data.swap(root, swap_i);
        root = swap_i;
    }
}

fn heap_sort_vec<T: Ord>(data: &mut Vec<T>) {
    heapsort(data.as_mut_slice());
}

// =========================
// 计数排序 / 基数排序（u32 专用演示）
// =========================

/// 计数排序（非负整数，返回新的 Vec）
pub fn counting_sort_sync_u32(data: &[u32]) -> Vec<u32> {
    if data.is_empty() { return Vec::new(); }
    let &max_v = data.iter().max().unwrap();
    let mut cnt = vec![0usize; max_v as usize + 1];
    for &x in data { cnt[x as usize] += 1; }
    let mut out = Vec::with_capacity(data.len());
    for (v, &c) in cnt.iter().enumerate() {
        for _ in 0..c { out.push(v as u32); }
    }
    out
}

/// 并行计数排序（并行统计 + 归并）
pub fn counting_sort_parallel_u32(data: &[u32]) -> Vec<u32> {
    if data.is_empty() { return Vec::new(); }
    let &max_v = data.iter().max().unwrap();
    let range = max_v as usize + 1;
    let chunks: Vec<Vec<usize>> = data
        .par_chunks(1.max(data.len() / rayon::current_num_threads().max(1)))
        .map(|chunk| {
            let mut local = vec![0usize; range];
            for &x in chunk { local[x as usize] += 1; }
            local
        })
        .collect();
    let mut cnt = vec![0usize; range];
    for local in chunks { for (i, v) in local.into_iter().enumerate() { cnt[i] += v; } }
    let mut out = Vec::with_capacity(data.len());
    for (v, &c) in cnt.iter().enumerate() { for _ in 0..c { out.push(v as u32); } }
    out
}

pub async fn counting_sort_async_u32(data: Vec<u32>) -> Result<Vec<u32>> {
    Ok(tokio::task::spawn_blocking(move || counting_sort_parallel_u32(&data)).await?)
}

/// 基数排序（LSD，按 8bit 桶，原地稳定，返回新 Vec）
pub fn radix_sort_lsd_sync_u32(mut data: Vec<u32>) -> Vec<u32> {
    let n = data.len();
    if n <= 1 { return data; }
    let mut buf = vec![0u32; n];
    for shift in (0..32).step_by(8) {
        let mut cnt = [0usize; 256];
        for &x in &data { cnt[((x >> shift) & 0xFF) as usize] += 1; }
        let mut pos = [0usize; 256];
        let mut sum = 0usize;
        for i in 0..256 { let c = cnt[i]; pos[i] = sum; sum += c; }
        for &x in &data {
            let b = ((x >> shift) & 0xFF) as usize;
            let p = pos[b];
            buf[p] = x;
            pos[b] += 1;
        }
        std::mem::swap(&mut data, &mut buf);
    }
    data
}

pub async fn radix_sort_lsd_async_u32(data: Vec<u32>) -> Result<Vec<u32>> {
    Ok(tokio::task::spawn_blocking(move || radix_sort_lsd_sync_u32(data)).await?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sync_sort_variants() {
        let mut a = vec![3, 1, 4, 1, 5, 9, 2];
        sort_sync(&mut a, SortingAlgo::Quick);
        assert!(a.windows(2).all(|w| w[0] <= w[1]));

        let mut b = vec![3, 1, 4, 1, 5, 9, 2];
        sort_sync(&mut b, SortingAlgo::Merge);
        assert!(b.windows(2).all(|w| w[0] <= w[1]));

        let mut c = vec![3, 1, 4, 1, 5, 9, 2];
        sort_sync(&mut c, SortingAlgo::Heap);
        assert!(c.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn test_parallel_sort() {
        let mut a = vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
        sort_parallel(&mut a, SortingAlgo::Quick);
        assert!(a.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn test_counting_and_radix_u32() {
        let v = vec![5u32,1,3,3,0,9,255,128,128,2];
        let c = counting_sort_sync_u32(&v);
        assert!(c.windows(2).all(|w| w[0] <= w[1]));
        let cp = counting_sort_parallel_u32(&v);
        assert_eq!(c, cp);
        let r = radix_sort_lsd_sync_u32(v.clone());
        assert!(r.windows(2).all(|w| w[0] <= w[1]));
    }
}

