//! 通用优先队列封装：最小堆/最大堆，支持同步/异步批处理

use anyhow::Result;
use std::cmp::Reverse;
use std::collections::BinaryHeap;

/// 堆类型
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapKind {
    Max,
    Min,
}

/// 通用优先队列
#[derive(Clone, Debug)]
pub struct PriorityQueue<T> {
    kind: HeapKind,
    max_heap: BinaryHeap<T>,
    min_heap: BinaryHeap<Reverse<T>>,
}

impl<T: Ord> PriorityQueue<T> {
    pub fn new(kind: HeapKind) -> Self {
        match kind {
            HeapKind::Max => Self {
                kind,
                max_heap: BinaryHeap::new(),
                min_heap: BinaryHeap::new(),
            },
            HeapKind::Min => Self {
                kind,
                max_heap: BinaryHeap::new(),
                min_heap: BinaryHeap::new(),
            },
        }
    }

    pub fn push(&mut self, value: T) {
        match self.kind {
            HeapKind::Max => self.max_heap.push(value),
            HeapKind::Min => self.min_heap.push(Reverse(value)),
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        match self.kind {
            HeapKind::Max => self.max_heap.pop(),
            HeapKind::Min => self.min_heap.pop().map(|r| r.0),
        }
    }

    pub fn peek(&self) -> Option<&T> {
        match self.kind {
            HeapKind::Max => self.max_heap.peek(),
            HeapKind::Min => self.min_heap.peek().map(|r| &r.0),
        }
    }

    pub fn len(&self) -> usize {
        self.max_heap.len().max(self.min_heap.len())
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 批量推入（同步）
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for v in iter {
            self.push(v);
        }
    }
}

/// 异步批量构建一个堆并返回（CPU 密集：spawn_blocking）
pub async fn build_heap_async<T: Ord + Send + 'static>(
    kind: HeapKind,
    data: Vec<T>,
) -> Result<PriorityQueue<T>> {
    Ok(tokio::task::spawn_blocking(move || {
        let mut pq = PriorityQueue::new(kind);
        pq.extend(data);
        pq
    })
    .await?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_heap_basic() {
        let mut pq = PriorityQueue::new(HeapKind::Max);
        pq.extend(vec![3, 1, 4, 1, 5]);
        assert_eq!(pq.peek().copied().unwrap(), 5);
        assert_eq!(pq.pop(), Some(5));
        assert_eq!(pq.pop(), Some(4));
    }

    #[test]
    fn test_min_heap_basic() {
        let mut pq = PriorityQueue::new(HeapKind::Min);
        pq.extend(vec![3, 1, 4, 1, 5]);
        assert_eq!(pq.peek().copied().unwrap(), 1);
        assert_eq!(pq.pop(), Some(1));
        assert_eq!(pq.pop(), Some(1));
    }

    #[test]
    fn test_build_heap_async() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        let pq = rt.block_on(async {
            build_heap_async(HeapKind::Max, vec![1, 2, 3])
                .await
                .unwrap()
        });
        assert_eq!(pq.len(), 3);
    }
}
