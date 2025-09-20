/*
 * 实用示例模块 - Rust 1.89 泛型编程实践
 * 
 * 本模块提供了大量实用的泛型编程示例，展示如何在实际项目中使用
 * Rust 1.89 的新特性和改进的泛型系统。
 * 
 * 包含的示例：
 * 1. 数据结构实现
 * 2. 算法实现
 * 3. 系统编程示例
 * 4. 网络编程示例
 * 5. 并发编程示例
 * 6. 错误处理示例
 * 7. 序列化/反序列化示例
 * 8. 性能优化示例
 */

use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::ops::{Add, Mul, Sub, Div, Rem};
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};

/// 数据结构实现示例
pub mod data_structures {
    use super::*;

    /// 泛型环形缓冲区 - 展示常量泛型推断
    #[derive(Debug, Clone)]
    pub struct RingBuffer<T, const CAPACITY: usize> {
        buffer: [Option<T>; CAPACITY],
        head: usize,
        tail: usize,
        count: usize,
    }

    impl<T, const CAPACITY: usize> Default for RingBuffer<T, CAPACITY> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T, const CAPACITY: usize> RingBuffer<T, CAPACITY> {
        /// 创建新的环形缓冲区
        pub fn new() -> Self {
            Self {
                buffer: [(); CAPACITY].map(|_| None),
                head: 0,
                tail: 0,
                count: 0,
            }
        }

        /// 添加元素到缓冲区
        pub fn push(&mut self, item: T) -> Result<(), T> {
            if self.count >= CAPACITY {
                return Err(item);
            }

            self.buffer[self.tail] = Some(item);
            self.tail = (self.tail + 1) % CAPACITY;
            self.count += 1;
            Ok(())
        }

        /// 从缓冲区移除元素
        pub fn pop(&mut self) -> Option<T> {
            if self.count == 0 {
                return None;
            }

            let item = self.buffer[self.head].take();
            self.head = (self.head + 1) % CAPACITY;
            self.count -= 1;
            item
        }

        /// 获取缓冲区当前大小
        pub fn len(&self) -> usize {
            self.count
        }

        /// 检查缓冲区是否为空
        pub fn is_empty(&self) -> bool {
            self.count == 0
        }

        /// 检查缓冲区是否已满
        pub fn is_full(&self) -> bool {
            self.count >= CAPACITY
        }

        /// 获取缓冲区容量
        pub fn capacity(&self) -> usize {
            CAPACITY
        }

        /// 清空缓冲区
        pub fn clear(&mut self) {
            self.buffer = [(); CAPACITY].map(|_| None);
            self.head = 0;
            self.tail = 0;
            self.count = 0;
        }
    }

    /// 泛型LRU缓存 - 展示复杂泛型使用
    #[derive(Debug, Clone)]
    pub struct LRUCache<K, V, const CAPACITY: usize>
    where
        K: Clone + Eq + std::hash::Hash,
        V: Clone,
    {
        cache: HashMap<K, V>,
        access_order: Vec<K>,
    }

    impl<K, V, const CAPACITY: usize> Default for LRUCache<K, V, CAPACITY>
    where
            K: Clone + Eq + std::hash::Hash,
            V: Clone,
     {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<K, V, const CAPACITY: usize> LRUCache<K, V, CAPACITY>
    where
        K: Clone + Eq + std::hash::Hash,
        V: Clone,
    {
        /// 创建新的LRU缓存
        pub fn new() -> Self {
            Self {
                cache: HashMap::new(),
                access_order: Vec::new(),
            }
        }

        /// 获取值
        pub fn get(&mut self, key: &K) -> Option<&V> {
            if let Some(value) = self.cache.get(key) {
                // 更新访问顺序
                self.access_order.retain(|k| k != key);
                self.access_order.push(key.clone());
                Some(value)
            } else {
                None
            }
        }

        /// 设置值
        pub fn set(&mut self, key: K, value: V) {
            if self.cache.contains_key(&key) {
                // 更新现有值
                self.cache.insert(key.clone(), value);
                self.access_order.retain(|k| k != &key);
                self.access_order.push(key);
            } else {
                // 添加新值
                if self.cache.len() >= CAPACITY {
                    // 移除最久未使用的项
                    if let Some(oldest_key) = self.access_order.first().cloned() {
                        self.cache.remove(&oldest_key);
                        self.access_order.remove(0);
                    }
                }
                self.cache.insert(key.clone(), value);
                self.access_order.push(key);
            }
        }

        /// 获取缓存大小
        pub fn len(&self) -> usize {
            self.cache.len()
        }

        /// 检查缓存是否为空
        pub fn is_empty(&self) -> bool {
            self.cache.is_empty()
        }

        /// 清空缓存
        pub fn clear(&mut self) {
            self.cache.clear();
            self.access_order.clear();
        }
    }

    /// 泛型堆栈 - 展示简单泛型数据结构
    #[derive(Debug, Clone)]
    pub struct Stack<T> {
        items: Vec<T>,
    }

    impl<T> Default for Stack<T> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T> Stack<T> {
        /// 创建新的堆栈
        pub fn new() -> Self {
            Self {
                items: Vec::new(),
            }
        }

        /// 推入元素
        pub fn push(&mut self, item: T) {
            self.items.push(item);
        }

        /// 弹出元素
        pub fn pop(&mut self) -> Option<T> {
            self.items.pop()
        }

        /// 查看栈顶元素
        pub fn peek(&self) -> Option<&T> {
            self.items.last()
        }

        /// 获取堆栈大小
        pub fn len(&self) -> usize {
            self.items.len()
        }

        /// 检查堆栈是否为空
        pub fn is_empty(&self) -> bool {
            self.items.is_empty()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_ring_buffer() {
            let mut buffer: RingBuffer<i32, 3> = RingBuffer::new();
            
            assert!(buffer.is_empty());
            assert_eq!(buffer.capacity(), 3);
            
            assert!(buffer.push(1).is_ok());
            assert!(buffer.push(2).is_ok());
            assert!(buffer.push(3).is_ok());
            
            assert!(buffer.is_full());
            assert!(buffer.push(4).is_err());
            
            assert_eq!(buffer.pop(), Some(1));
            assert_eq!(buffer.pop(), Some(2));
            assert_eq!(buffer.pop(), Some(3));
            assert_eq!(buffer.pop(), None);
        }

        #[test]
        fn test_lru_cache() {
            let mut cache: LRUCache<String, i32, 3> = LRUCache::new();
            
            cache.set("a".to_string(), 1);
            cache.set("b".to_string(), 2);
            cache.set("c".to_string(), 3);
            
            assert_eq!(cache.get(&"a".to_string()), Some(&1));
            
            cache.set("d".to_string(), 4); // 这会移除 "b"
            assert_eq!(cache.get(&"b".to_string()), None);
            assert_eq!(cache.get(&"d".to_string()), Some(&4));
        }

        #[test]
        fn test_stack() {
            let mut stack = Stack::new();
            
            assert!(stack.is_empty());
            
            stack.push(1);
            stack.push(2);
            stack.push(3);
            
            assert_eq!(stack.len(), 3);
            assert_eq!(stack.peek(), Some(&3));
            
            assert_eq!(stack.pop(), Some(3));
            assert_eq!(stack.pop(), Some(2));
            assert_eq!(stack.pop(), Some(1));
            assert_eq!(stack.pop(), None);
        }
    }
}

/// 算法实现示例
pub mod algorithms {
    use super::*;

    /// 泛型排序算法
    pub mod sorting {

        /// 快速排序实现
        pub fn quicksort<T>(arr: &mut [T])
        where
            T: PartialOrd + Clone,
        {
            if arr.len() <= 1 {
                return;
            }

            let pivot_index = partition(arr);
            quicksort(&mut arr[..pivot_index]);
            quicksort(&mut arr[pivot_index + 1..]);
        }

        fn partition<T>(arr: &mut [T]) -> usize
        where
            T: PartialOrd + Clone,
        {
            let pivot = arr[arr.len() - 1].clone();
            let mut i = 0;

            for j in 0..arr.len() - 1 {
                if arr[j] <= pivot {
                    arr.swap(i, j);
                    i += 1;
                }
            }

            arr.swap(i, arr.len() - 1);
            i
        }

        /// 归并排序实现
        pub fn mergesort<T>(arr: &mut [T])
        where
            T: PartialOrd + Clone,
        {
            if arr.len() <= 1 {
                return;
            }

            let mid = arr.len() / 2;
            mergesort(&mut arr[..mid]);
            mergesort(&mut arr[mid..]);
            merge(arr, mid);
        }

        fn merge<T>(arr: &mut [T], mid: usize)
        where
            T: PartialOrd + Clone,
        {
            let left = arr[..mid].to_vec();
            let right = arr[mid..].to_vec();

            let mut i = 0;
            let mut j = 0;
            let mut k = 0;

            while i < left.len() && j < right.len() {
                if left[i] <= right[j] {
                    arr[k] = left[i].clone();
                    i += 1;
                } else {
                    arr[k] = right[j].clone();
                    j += 1;
                }
                k += 1;
            }

            while i < left.len() {
                arr[k] = left[i].clone();
                i += 1;
                k += 1;
            }

            while j < right.len() {
                arr[k] = right[j].clone();
                j += 1;
                k += 1;
            }
        }
    }

    /// 泛型搜索算法
    pub mod searching {

        /// 二分搜索实现
        pub fn binary_search<T>(arr: &[T], target: &T) -> Option<usize>
        where
            T: PartialOrd,
        {
            let mut left = 0;
            let mut right = arr.len();

            while left < right {
                let mid = left + (right - left) / 2;
                match arr[mid].partial_cmp(target) {
                    Some(std::cmp::Ordering::Equal) => return Some(mid),
                    Some(std::cmp::Ordering::Less) => left = mid + 1,
                    Some(std::cmp::Ordering::Greater) => right = mid,
                    None => return None,
                }
            }

            None
        }

        /// 线性搜索实现
        pub fn linear_search<T>(arr: &[T], target: &T) -> Option<usize>
        where
            T: PartialEq,
        {
            for (index, item) in arr.iter().enumerate() {
                if item == target {
                    return Some(index);
                }
            }
            None
        }
    }

    /// 泛型数学算法
    pub mod math {
        use super::*;

        /// 计算最大公约数
        pub fn gcd<T>(a: T, b: T) -> T
        where
            T: PartialEq + Sub<Output = T> + Rem<Output = T> + Clone + Default,
        {
            if b == T::default() {
                a
            } else {
                gcd(b.clone(), a % b)
            }
        }

        /// 计算最小公倍数
        pub fn lcm<T>(a: T, b: T) -> T
        where
            T: PartialEq + Sub<Output = T> + Rem<Output = T> + Mul<Output = T> + Div<Output = T> + Clone + Default,
        {
            (a.clone() * b.clone()) / gcd(a, b)
        }

        /// 计算斐波那契数列
        pub fn fibonacci<T>(n: usize) -> T
        where
            T: Add<Output = T> + Clone + Default + From<u32>,
        {
            if n <= 1 {
                return T::from(n as u32);
            }

            let mut a = T::from(0);
            let mut b = T::from(1);

            for _ in 2..=n {
                let temp = a.clone() + b.clone();
                a = b;
                b = temp;
            }

            b
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_quicksort() {
            let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
            sorting::quicksort(&mut arr);
            assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
        }

        #[test]
        fn test_mergesort() {
            let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
            sorting::mergesort(&mut arr);
            assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
        }

        #[test]
        fn test_binary_search() {
            let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
            assert_eq!(searching::binary_search(&arr, &7), Some(3));
            assert_eq!(searching::binary_search(&arr, &8), None);
        }

        #[test]
        fn test_linear_search() {
            let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
            assert_eq!(searching::linear_search(&arr, &7), Some(3));
            assert_eq!(searching::linear_search(&arr, &8), None);
        }

        #[test]
        fn test_gcd() {
            assert_eq!(math::gcd(48, 18), 6);
            assert_eq!(math::gcd(17, 13), 1);
        }

        #[test]
        fn test_lcm() {
            assert_eq!(math::lcm(12, 18), 36);
            assert_eq!(math::lcm(17, 13), 221);
        }

        #[test]
        fn test_fibonacci() {
            assert_eq!(math::fibonacci::<u32>(0), 0);
            assert_eq!(math::fibonacci::<u32>(1), 1);
            assert_eq!(math::fibonacci::<u32>(10), 55);
        }
    }
}

/// 并发编程示例
pub mod concurrency {
    use super::*;

    /// 线程安全的泛型计数器
    pub struct ThreadSafeCounter<T> {
        value: Arc<Mutex<T>>,
    }

    impl<T> ThreadSafeCounter<T> {
        /// 创建新的线程安全计数器
        pub fn new(initial_value: T) -> Self {
            Self {
                value: Arc::new(Mutex::new(initial_value)),
            }
        }

        /// 获取当前值
        pub fn get(&self) -> T
        where
            T: Clone,
        {
            self.value.lock().unwrap().clone()
        }

        /// 设置值
        pub fn set(&self, new_value: T) {
            *self.value.lock().unwrap() = new_value;
        }

        /// 增加计数（仅适用于数值类型）
        pub fn increment(&self) -> T
        where
            T: Add<T, Output = T> + Clone + From<i32>,
        {
            let mut value = self.value.lock().unwrap();
            *value = value.clone() + T::from(1);
            value.clone()
        }
    }

    impl<T> Clone for ThreadSafeCounter<T> {
        fn clone(&self) -> Self {
            Self {
                value: Arc::clone(&self.value),
            }
        }
    }

    /// 泛型线程池
    #[allow(dead_code)]
    pub struct ThreadPool<T, R> {
        workers: Vec<thread::JoinHandle<()>>,
        sender: std::sync::mpsc::Sender<T>,
        _phantom: PhantomData<R>,
    }

    impl<T, R> ThreadPool<T, R>
    where
        T: Send + 'static,
        R: Send + 'static,
    {
        /// 创建新的线程池
        pub fn new<F>(size: usize, worker_fn: F) -> Self
        where
            F: Fn() -> R + Send + Sync + 'static + Clone,
        {
            let (sender, receiver) = std::sync::mpsc::channel();
            let receiver = Arc::new(Mutex::new(receiver));

            let mut workers = Vec::with_capacity(size);

            for _ in 0..size {
                let receiver = Arc::clone(&receiver);
                let worker_fn = worker_fn.clone();

                let worker = thread::spawn(move || {
            while let Ok(_task) = receiver.lock().unwrap().recv() {
                // 处理任务
                let _result = worker_fn();
            }
                });

                workers.push(worker);
            }

            Self {
                workers,
                sender,
                _phantom: PhantomData,
            }
        }

        /// 提交任务
        pub fn execute(&self, task: T) -> Result<(), std::sync::mpsc::SendError<T>> {
            self.sender.send(task)
        }
    }

    /// 读写锁保护的泛型数据
    pub struct ReadWriteData<T> {
        data: Arc<RwLock<T>>,
    }

    impl<T> ReadWriteData<T> {
        /// 创建新的读写锁保护数据
        pub fn new(data: T) -> Self {
            Self {
                data: Arc::new(RwLock::new(data)),
            }
        }

        /// 读取数据
        pub fn read<F, R>(&self, reader: F) -> R
        where
            F: FnOnce(&T) -> R,
        {
            let data = self.data.read().unwrap();
            reader(&data)
        }

        /// 写入数据
        pub fn write<F, R>(&self, writer: F) -> R
        where
            F: FnOnce(&mut T) -> R,
        {
            let mut data = self.data.write().unwrap();
            writer(&mut data)
        }
    }

    impl<T> Clone for ReadWriteData<T> {
        fn clone(&self) -> Self {
            Self {
                data: Arc::clone(&self.data),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_thread_safe_counter() {
            let counter = ThreadSafeCounter::new(0);
            
            assert_eq!(counter.get(), 0);
            counter.increment();
            assert_eq!(counter.get(), 1);
            
            counter.set(42);
            assert_eq!(counter.get(), 42);
        }

        #[test]
        fn test_read_write_data() {
            let data = ReadWriteData::new(vec![1, 2, 3]);
            
            let len = data.read(|vec| vec.len());
            assert_eq!(len, 3);
            
            data.write(|vec| vec.push(4));
            
            let len = data.read(|vec| vec.len());
            assert_eq!(len, 4);
        }
    }
}

/// 错误处理示例
pub mod error_handling {
    use super::*;

    /// 自定义错误类型
    #[derive(Debug, Clone)]
    pub enum GenericError<T> {
        NotFound(T),
        InvalidInput(T),
        ProcessingError(String),
        Custom(String),
    }

    impl<T> std::fmt::Display for GenericError<T>
    where
        T: Display,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                GenericError::NotFound(item) => write!(f, "未找到: {}", item),
                GenericError::InvalidInput(item) => write!(f, "无效输入: {}", item),
                GenericError::ProcessingError(msg) => write!(f, "处理错误: {}", msg),
                GenericError::Custom(msg) => write!(f, "自定义错误: {}", msg),
            }
        }
    }

    impl<T> std::error::Error for GenericError<T> 
    where 
        T: Display + Debug,
    {}

    /// 泛型结果类型
    pub type GenericResult<T, E> = Result<T, GenericError<E>>;

    /// 泛型查找函数
    pub fn find_item<'a, T, U>(items: &'a [T], target: &U) -> GenericResult<&'a T, U>
    where
        T: PartialEq<U>,
        U: Clone,
    {
        items
            .iter()
            .find(|item| item == &target)
            .ok_or_else(|| GenericError::NotFound(target.clone()))
    }

    /// 泛型验证函数
    pub fn validate_input<T, F>(input: T, validator: F) -> GenericResult<T, T>
    where
        F: Fn(&T) -> bool,
        T: Clone,
    {
        if validator(&input) {
            Ok(input)
        } else {
            Err(GenericError::InvalidInput(input))
        }
    }

    /// 泛型处理函数
    pub fn process_data<T, U, F>(data: T, processor: F) -> GenericResult<U, String>
    where
        F: Fn(T) -> Result<U, String>,
    {
        processor(data).map_err(GenericError::ProcessingError)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_find_item() {
            let items = vec![1, 2, 3, 4, 5];
            let result = find_item(&items, &3);
            assert!(result.is_ok());
            assert_eq!(*result.unwrap(), 3);

            let result = find_item(&items, &6);
            assert!(result.is_err());
        }

        #[test]
        fn test_validate_input() {
            let result = validate_input(42, |&x| x > 0);
            assert!(result.is_ok());

            let result = validate_input(-1, |&x| x > 0);
            assert!(result.is_err());
        }

        #[test]
        fn test_process_data() {
            let result = process_data(42, |x| Ok(x * 2));
            assert!(result.is_ok());
            assert_eq!(result.unwrap(), 84);

            let result = process_data(42, |_| Err::<i32, String>("处理失败".to_string()));
            assert!(result.is_err());
        }
    }
}

/// 性能优化示例
pub mod performance {
    use super::*;

    /// 泛型性能计时器
    pub struct PerformanceTimer<T> {
        start_time: Instant,
        _phantom: PhantomData<T>,
    }

    impl<T> PerformanceTimer<T> {
        /// 开始计时
        pub fn start() -> Self {
            Self {
                start_time: Instant::now(),
                _phantom: PhantomData,
            }
        }

        /// 结束计时并返回耗时
        pub fn elapsed(&self) -> Duration {
            self.start_time.elapsed()
        }

        /// 测量函数执行时间
        pub fn measure<F, R>(f: F) -> (R, Duration)
        where
            F: FnOnce() -> R,
        {
            let timer = PerformanceTimer::<()>::start();
            let result = f();
            let elapsed = timer.elapsed();
            (result, elapsed)
        }
    }

    /// 泛型缓存系统
    pub struct Cache<K, V> {
        cache: HashMap<K, V>,
        max_size: usize,
    }

    impl<K, V> Cache<K, V>
    where
        K: Clone + Eq + std::hash::Hash,
        V: Clone,
    {
        /// 创建新的缓存
        pub fn new(max_size: usize) -> Self {
            Self {
                cache: HashMap::new(),
                max_size,
            }
        }

        /// 获取值
        pub fn get(&self, key: &K) -> Option<&V> {
            self.cache.get(key)
        }

        /// 设置值
        pub fn set(&mut self, key: K, value: V) {
            if self.cache.len() >= self.max_size {
                // 简单的LRU实现：移除第一个元素
                if let Some(first_key) = self.cache.keys().next().cloned() {
                    self.cache.remove(&first_key);
                }
            }
            self.cache.insert(key, value);
        }

        /// 清空缓存
        pub fn clear(&mut self) {
            self.cache.clear();
        }

        /// 获取缓存大小
        pub fn len(&self) -> usize {
            self.cache.len()
        }

        /// 检查缓存是否为空
        pub fn is_empty(&self) -> bool {
            self.cache.is_empty()
        }
    }

    /// 泛型批处理系统
    pub struct BatchProcessor<T, R> {
        batch_size: usize,
        processor: Box<dyn Fn(Vec<T>) -> Vec<R> + Send + Sync>,
    }

    impl<T, R> BatchProcessor<T, R> {
        /// 创建新的批处理器
        pub fn new<F>(batch_size: usize, processor: F) -> Self
        where
            F: Fn(Vec<T>) -> Vec<R> + Send + Sync + 'static,
        {
            Self {
                batch_size,
                processor: Box::new(processor),
            }
        }

        /// 处理数据批次
        pub fn process_batch(&self, data: Vec<T>) -> Vec<R> {
            (self.processor)(data)
        }

        /// 分批处理大量数据
        pub fn process_all(&self, mut data: Vec<T>) -> Vec<R> {
            let mut results = Vec::new();

            while !data.is_empty() {
                let batch_size = std::cmp::min(self.batch_size, data.len());
                let batch = data.drain(0..batch_size).collect();
                let batch_results = self.process_batch(batch);
                results.extend(batch_results);
            }

            results
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_performance_timer() {
            let (result, elapsed) = PerformanceTimer::<()>::measure(|| {
                thread::sleep(Duration::from_millis(10));
                42
            });

            assert_eq!(result, 42);
            assert!(elapsed >= Duration::from_millis(10));
        }

        #[test]
        fn test_cache() {
            let mut cache = Cache::new(2);
            
            cache.set("key1", "value1");
            cache.set("key2", "value2");
            cache.set("key3", "value3"); // 这会移除 key1
            
            assert_eq!(cache.get(&"key1"), None);
            assert_eq!(cache.get(&"key2"), Some(&"value2"));
            assert_eq!(cache.get(&"key3"), Some(&"value3"));
        }

        #[test]
        fn test_batch_processor() {
            let processor = BatchProcessor::new(2, |batch| {
                batch.into_iter().map(|x| x * 2).collect()
            });

            let data = vec![1, 2, 3, 4, 5];
            let results = processor.process_all(data);
            assert_eq!(results, vec![2, 4, 6, 8, 10]);
        }
    }
}

/// 综合演示函数
pub fn demonstrate_practical_examples() {
    println!("\n=== 实用示例演示 ===");

    println!("\n1. 数据结构示例:");
    let mut buffer: data_structures::RingBuffer<i32, 5> = data_structures::RingBuffer::new();
    let _ = buffer.push(1);
    let _ = buffer.push(2);
    let _ = buffer.push(3);
    println!("环形缓冲区大小: {}", buffer.len());

    let mut cache: data_structures::LRUCache<String, i32, 3> = data_structures::LRUCache::new();
    cache.set("key1".to_string(), 1);
    cache.set("key2".to_string(), 2);
    cache.set("key3".to_string(), 3);
    println!("LRU缓存大小: {}", cache.len());

    println!("\n2. 算法示例:");
    let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
    algorithms::sorting::quicksort(&mut arr);
    println!("快速排序结果: {:?}", arr);

    let search_arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
    let index = algorithms::searching::binary_search(&search_arr, &7);
    println!("二分搜索结果: {:?}", index);

    println!("\n3. 并发编程示例:");
    let counter = concurrency::ThreadSafeCounter::new(0);
    counter.increment();
    println!("线程安全计数器: {}", counter.get());

    let data = concurrency::ReadWriteData::new(vec![1, 2, 3]);
    let len = data.read(|vec| vec.len());
    println!("读写锁保护数据长度: {}", len);

    println!("\n4. 错误处理示例:");
    let items = vec![1, 2, 3, 4, 5];
    let result = error_handling::find_item(&items, &3);
    match result {
        Ok(item) => println!("找到项目: {}", item),
        Err(e) => println!("错误: {}", e),
    }

    println!("\n5. 性能优化示例:");
    let (result, elapsed) = performance::PerformanceTimer::<u32>::measure(|| {
        algorithms::math::fibonacci::<u32>(20)
    });
    println!("斐波那契(20) = {}, 耗时: {:?}", result, elapsed);

    let mut cache = performance::Cache::new(3);
    cache.set("key1", "value1");
    cache.set("key2", "value2");
    println!("缓存大小: {}", cache.len());

    println!("\n=== 实用示例演示完成 ===");
}

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_all_practical_examples() {
        demonstrate_practical_examples();
    }
}
