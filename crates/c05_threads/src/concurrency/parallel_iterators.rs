//! 并行迭代器实现和示例
//!
//! 本模块提供并行迭代器的实现和示例，展示如何使用并行处理来加速迭代操作。
//! 可以集成 `rayon` 或提供自定义实现。

use std::sync::{Arc, Mutex};

/// 并行迭代器适配器
///
/// 将普通迭代器转换为并行迭代器
pub struct ParallelIteratorAdapter<I> {
    #[allow(dead_code)]
    iter: I,
    chunk_size: usize,
}

impl<I> ParallelIteratorAdapter<I> {
    /// 创建新的并行迭代器适配器
    pub fn new(iter: I, chunk_size: usize) -> Self {
        Self { iter, chunk_size }
    }

    /// 设置块大小
    pub fn with_chunk_size(mut self, chunk_size: usize) -> Self {
        self.chunk_size = chunk_size;
        self
    }
}

/// 并行处理结果
pub struct ParallelResult<T> {
    results: Vec<T>,
    processing_time: std::time::Duration,
}

impl<T> ParallelResult<T> {
    /// 创建新的并行处理结果
    pub fn new(results: Vec<T>, processing_time: std::time::Duration) -> Self {
        Self {
            results,
            processing_time,
        }
    }

    /// 获取结果
    pub fn results(&self) -> &[T] {
        &self.results
    }

    /// 获取处理时间
    pub fn processing_time(&self) -> std::time::Duration {
        self.processing_time
    }
}

/// 并行映射函数
///
/// 对集合中的每个元素应用函数，并行处理
pub fn parallel_map<T, R, F>(items: &[T], f: F) -> Vec<R>
where
    T: Send + Sync + Clone + 'static,
    R: Send + Sync + std::fmt::Debug + 'static,
    F: Fn(&T) -> R + Send + Sync + 'static,
{
    use std::thread;

    let num_threads = num_cpus::get().min(items.len());
    let chunk_size = (items.len() + num_threads - 1) / num_threads;

    // 对于小数据集，直接顺序处理
    if items.len() < 100 {
        return items.iter().map(|item| f(item)).collect();
    }

    let results: Arc<Mutex<Vec<R>>> = Arc::new(Mutex::new(Vec::new()));
    let f = Arc::new(f);

    let handles: Vec<_> = items
        .chunks(chunk_size)
        .map(|chunk| {
            let chunk = chunk.to_vec();
            let results = Arc::clone(&results);
            let f = Arc::clone(&f);

            thread::spawn(move || {
                let mut chunk_results: Vec<R> = chunk.iter().map(|item| f(item)).collect();
                let mut results = results.lock().unwrap();
                results.append(&mut chunk_results);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    Arc::try_unwrap(results).unwrap().into_inner().unwrap()
}

/// 并行过滤函数
///
/// 并行过滤集合中的元素
/// 注意：这是一个简化实现，实际项目中建议使用 rayon 库
pub fn parallel_filter<T, F>(items: &[T], predicate: F) -> Vec<T>
where
    T: Send + Sync + Clone + std::fmt::Debug + 'static,
    F: Fn(&T) -> bool + Send + Sync + 'static,
{
    use std::thread;

    // 对于小数据集，直接顺序处理
    if items.len() < 100 {
        return items.iter().filter(|item| predicate(item)).cloned().collect();
    }

    let num_threads = num_cpus::get().min(items.len());
    let chunk_size = (items.len() + num_threads - 1) / num_threads;

    let results: Arc<Mutex<Vec<T>>> = Arc::new(Mutex::new(Vec::new()));
    let predicate = Arc::new(predicate);

    let handles: Vec<_> = items
        .chunks(chunk_size)
        .map(|chunk| {
            let chunk = chunk.to_vec();
            let results = Arc::clone(&results);
            let predicate = Arc::clone(&predicate);

            thread::spawn(move || {
                let mut chunk_results: Vec<T> = chunk
                    .into_iter()
                    .filter(|item| predicate(item))
                    .collect();
                let mut results = results.lock().unwrap();
                results.append(&mut chunk_results);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    Arc::try_unwrap(results).unwrap().into_inner().unwrap()
}

/// 并行归约函数
///
/// 并行归约集合中的元素
/// 注意：这是一个简化实现，实际项目中建议使用 rayon 库
pub fn parallel_reduce<T, F>(items: &[T], identity: T, op: F) -> T
where
    T: Send + Sync + Clone + std::fmt::Debug + 'static,
    F: Fn(T, &T) -> T + Send + Sync + 'static,
{
    use std::thread;

    // 对于小数据集，直接顺序处理
    if items.len() < 100 {
        return items.iter().fold(identity.clone(), |acc, item| op(acc, item));
    }

    let num_threads = num_cpus::get().min(items.len());
    let chunk_size = (items.len() + num_threads - 1) / num_threads;

    let results: Arc<Mutex<Vec<T>>> = Arc::new(Mutex::new(Vec::new()));
    let op = Arc::new(op);

    let handles: Vec<_> = items
        .chunks(chunk_size)
        .map(|chunk| {
            let chunk = chunk.to_vec();
            let results = Arc::clone(&results);
            let op = Arc::clone(&op);
            let identity = identity.clone();

            thread::spawn(move || {
                let result = chunk.iter().fold(identity, |acc, item| op(acc, item));
                let mut results = results.lock().unwrap();
                results.push(result);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    let partial_results = Arc::try_unwrap(results).unwrap().into_inner().unwrap();
    partial_results
        .into_iter()
        .fold(identity, |acc, item| op(acc, &item))
}

/// 并行查找函数
///
/// 并行查找集合中满足条件的元素
/// 注意：这是一个简化实现，实际项目中建议使用 rayon 库
pub fn parallel_find<T, F>(items: &[T], predicate: F) -> Option<usize>
where
    T: Send + Sync + Clone + 'static,
    F: Fn(&T) -> bool + Send + Sync + 'static,
{
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::thread;

    // 对于小数据集，直接顺序处理
    if items.len() < 100 {
        return items.iter().position(|item| predicate(item));
    }

    let num_threads = num_cpus::get().min(items.len());
    let chunk_size = (items.len() + num_threads - 1) / num_threads;

    let found = Arc::new(AtomicBool::new(false));
    let result_index = Arc::new(AtomicUsize::new(usize::MAX));
    let predicate = Arc::new(predicate);

    let handles: Vec<_> = items
        .chunks(chunk_size)
        .enumerate()
        .map(|(chunk_idx, chunk)| {
            let chunk = chunk.to_vec();
            let found = Arc::clone(&found);
            let result_index = Arc::clone(&result_index);
            let predicate = Arc::clone(&predicate);

            thread::spawn(move || {
                for (idx, item) in chunk.iter().enumerate() {
                    if found.load(Ordering::Relaxed) {
                        break;
                    }

                    if predicate(item) {
                        found.store(true, Ordering::Relaxed);
                        result_index.store(chunk_idx * chunk.len() + idx, Ordering::Relaxed);
                        break;
                    }
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    if found.load(Ordering::Relaxed) {
        let idx = result_index.load(Ordering::Relaxed);
        if idx < items.len() {
            Some(idx)
        } else {
            None
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_map() {
        let items = vec![1, 2, 3, 4, 5];
        let results = parallel_map(&items, |x| x * 2);
        assert_eq!(results, vec![2, 4, 6, 8, 10]);
    }

    #[test]
    fn test_parallel_filter() {
        let items = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let results = parallel_filter(&items, |x| x % 2 == 0);
        assert_eq!(results.len(), 5);
        assert!(results.iter().all(|x| x % 2 == 0));
    }

    #[test]
    fn test_parallel_reduce() {
        let items = vec![1, 2, 3, 4, 5];
        let result = parallel_reduce(&items, 0, |acc, x| acc + x);
        assert_eq!(result, 15);
    }

    #[test]
    fn test_parallel_find() {
        let items = vec![1, 2, 3, 4, 5];
        let index = parallel_find(&items, |x| *x == 3);
        assert_eq!(index, Some(2));

        let index = parallel_find(&items, |x| *x == 10);
        assert_eq!(index, None);
    }

    #[test]
    fn test_parallel_iterator_adapter() {
        let _adapter = ParallelIteratorAdapter::new(vec![1, 2, 3].into_iter(), 10);
        // 测试适配器创建
        assert!(true);
    }
}
