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

use std::collections::{HashMap, VecDeque};
use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::ops::{Add, Mul, Sub, Div, Rem};
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};

/// 数据结构实现示例
pub mod data_structures {
    use super::*;
    use std::hash::Hash;

    // 常用可选类型别名，降低类型复杂度
    type Maybe<T> = Option<T>;
    type MaybeRef<'a, T> = Option<&'a T>;
    type GenVec<T> = Vec<T>;
    #[allow(dead_code)]
    type GenSlice<'a, T> = &'a [T];
    #[allow(dead_code)]
    type GenMutSlice<'a, T> = &'a mut [T];
    type GenHashMap<K, V> = HashMap<K, V>;
    #[allow(dead_code)]
    type GenVecDeque<T> = VecDeque<T>;
    #[allow(dead_code)]
    type GenResult<T, E> = Result<T, E>;
    type GenOption<T> = Option<T>;
    #[allow(dead_code)]
    type GenArcMutex<T> = Arc<Mutex<T>>;
    #[allow(dead_code)]
    type GenArcRwLock<T> = Arc<RwLock<T>>;
    #[allow(dead_code)]
    type GenThreadJoinHandle<T> = thread::JoinHandle<T>;
    #[allow(dead_code)]
    type GenThreadJoinHandles<T> = Vec<thread::JoinHandle<T>>;
    #[allow(dead_code)]
    type GenSender<T> = std::sync::mpsc::Sender<T>;
    #[allow(dead_code)]
    type GenReceiver<T> = std::sync::mpsc::Receiver<T>;
    #[allow(dead_code)]
    type GenSendError<T> = std::sync::mpsc::SendError<T>;
    #[allow(dead_code)]
    type GenPhantomData<T> = PhantomData<T>;

    /// 泛型环形缓冲区 - 展示常量泛型推断
    #[derive(Debug, Clone)]
    pub struct RingBuffer<T, const CAPACITY: usize> {
        buffer: [GenOption<T>; CAPACITY],
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
        pub fn push(&mut self, item: T) -> GenResult<(), T> {
            if self.count >= CAPACITY {
                return Err(item);
            }

            self.buffer[self.tail] = Some(item);
            self.tail = (self.tail + 1) % CAPACITY;
            self.count += 1;
            Ok(())
        }

        /// 从缓冲区移除元素
        pub fn pop(&mut self) -> GenOption<T> {
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
        K: LruKey,
        V: LruValue,
    {
        cache: GenHashMap<K, V>,
        access_order: GenVec<K>,
    }

    impl<K, V, const CAPACITY: usize> Default for LRUCache<K, V, CAPACITY>
    where
        K: LruKey,
        V: LruValue,
    {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<K, V, const CAPACITY: usize> LRUCache<K, V, CAPACITY>
    where
        K: LruKey,
        V: LruValue,
    {
        /// 创建新的LRU缓存
        pub fn new() -> Self {
            Self {
                cache: HashMap::new(),
                access_order: Vec::new(),
            }
        }

        /// 获取值
        pub fn get(&mut self, key: &K) -> MaybeRef<'_, V> {
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
                self.update_existing(&key, value);
            } else {
                self.insert_new(key, value);
            }
        }

        /// 更新现有值
        fn update_existing(&mut self, key: &K, value: V) {
            self.cache.insert(key.clone(), value);
            self.access_order.retain(|k| k != key);
            self.access_order.push(key.clone());
        }

        /// 插入新值
        fn insert_new(&mut self, key: K, value: V) {
            self.evict_if_needed();
            self.cache.insert(key.clone(), value);
            self.access_order.push(key);
        }

        /// 如果需要，移除最久未使用的项
        fn evict_if_needed(&mut self) {
            if self.cache.len() >= CAPACITY {
                self.remove_oldest_item();
            }
        }

        /// 移除最老的项
        fn remove_oldest_item(&mut self) {
            if let Some(oldest_key) = self.access_order.first().cloned() {
                self.cache.remove(&oldest_key);
                self.access_order.remove(0);
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

    // 为降低类型复杂度而引入的内部 trait 约束
    pub trait LruKey: Clone + Eq + Hash {}
    impl<T: Clone + Eq + Hash> LruKey for T {}

    pub trait LruValue: Clone {}
    impl<T: Clone> LruValue for T {}

    /// 泛型堆栈 - 展示简单泛型数据结构
    #[derive(Debug, Clone)]
    pub struct Stack<T> {
        items: GenVec<T>,
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
        pub fn pop(&mut self) -> Maybe<T> {
            self.items.pop()
        }

        /// 查看栈顶元素
        pub fn peek(&self) -> MaybeRef<'_, T> {
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

    // 算法相关类型别名
    #[allow(dead_code)]
    type GenVec<T> = Vec<T>;
    type GenSlice<'a, T> = &'a [T];
    type GenMutSlice<'a, T> = &'a mut [T];
    type GenOption<T> = Option<T>;
    #[allow(dead_code)]
    type GenResult<T, E> = Result<T, E>;

    /// 快速排序实现
    pub fn quicksort<T>(arr: GenMutSlice<T>)
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

    fn partition<T>(arr: GenMutSlice<T>) -> usize
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
    pub fn mergesort<T>(arr: GenMutSlice<T>)
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

    fn merge<T>(arr: GenMutSlice<T>, mid: usize)
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

    /// 二分搜索实现
    pub fn binary_search<T>(arr: GenSlice<T>, target: &T) -> GenOption<usize>
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
    pub fn linear_search<T>(arr: GenSlice<T>, target: &T) -> GenOption<usize>
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

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_quicksort() {
            let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
            quicksort(&mut arr);
            assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
        }

        #[test]
        fn test_mergesort() {
            let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
            mergesort(&mut arr);
            assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
        }

        #[test]
        fn test_binary_search() {
            let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
            assert_eq!(binary_search(&arr, &7), Some(3));
            assert_eq!(binary_search(&arr, &8), None);
        }

        #[test]
        fn test_linear_search() {
            let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
            assert_eq!(linear_search(&arr, &7), Some(3));
            assert_eq!(linear_search(&arr, &8), None);
        }

        #[test]
        fn test_gcd() {
            assert_eq!(gcd(48, 18), 6);
            assert_eq!(gcd(17, 13), 1);
        }

        #[test]
        fn test_lcm() {
            assert_eq!(lcm(12, 18), 36);
            assert_eq!(lcm(17, 13), 221);
        }

        #[test]
        fn test_fibonacci() {
            assert_eq!(fibonacci::<u32>(0), 0);
            assert_eq!(fibonacci::<u32>(1), 1);
            assert_eq!(fibonacci::<u32>(10), 55);
        }
    }
}

/// 并发编程示例
pub mod concurrency {
    use super::*;

    // 并发相关类型别名
    type GenArcMutex<T> = Arc<Mutex<T>>;
    type GenArcRwLock<T> = Arc<RwLock<T>>;
    #[allow(dead_code)]
    type GenThreadJoinHandle<T> = thread::JoinHandle<T>;
    type GenThreadJoinHandles<T> = Vec<thread::JoinHandle<T>>;
    type GenSender<T> = std::sync::mpsc::Sender<T>;
    #[allow(dead_code)]
    type GenReceiver<T> = std::sync::mpsc::Receiver<T>;
    type GenSendError<T> = std::sync::mpsc::SendError<T>;
    type GenPhantomData<T> = PhantomData<T>;
    type GenResult<T, E> = Result<T, E>;

    /// 线程安全的泛型计数器
    pub struct ThreadSafeCounter<T> {
        value: GenArcMutex<T>,
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
        workers: GenThreadJoinHandles<()>,
        sender: GenSender<T>,
        _phantom: GenPhantomData<R>,
    }

    type TaskReceiver<T> = Arc<Mutex<std::sync::mpsc::Receiver<T>>>;

    fn worker_loop<T, R, F>(receiver: TaskReceiver<T>, worker_fn: F)
    where
        T: Send + 'static,
        R: Send + 'static,
        F: Fn() -> R + Send + 'static + Clone,
    {
        while let Ok(_task) = receiver.lock().unwrap().recv() {
            let _ = worker_fn();
        }
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

                let worker = thread::spawn(move || worker_loop::<T, R, F>(receiver, worker_fn));

                workers.push(worker);
            }

            Self {
                workers,
                sender,
                _phantom: PhantomData,
            }
        }

        /// 提交任务
        pub fn execute(&self, task: T) -> GenResult<(), GenSendError<T>> {
            self.sender.send(task)
        }
    }

    /// 读写锁保护的泛型数据
    pub struct ReadWriteData<T> {
        data: GenArcRwLock<T>,
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

            let len = data.read(|vec: &Vec<i32>| vec.len());
            assert_eq!(len, 3);

            data.write(|vec| vec.push(4));

            let len = data.read(|vec: &Vec<i32>| vec.len());
            assert_eq!(len, 4);
        }
    }
}

/// 错误处理示例
pub mod error_handling {
    use super::*;

    // 错误处理相关类型别名
    #[allow(dead_code)]
    type GenResult<T, E> = Result<T, E>;

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
    pub fn find_item<'a, T, U>(items: &'a [T], target: &U) -> Result<&'a T, GenericError<U>>
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
    pub fn validate_input<T, F>(input: T, validator: F) -> Result<T, GenericError<T>>
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
    pub fn process_data<T, U, F>(data: T, processor: F) -> Result<U, GenericError<String>>
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

    // 性能优化相关类型别名
    type GenPhantomData<T> = PhantomData<T>;
    type GenHashMap<K, V> = HashMap<K, V>;
    type GenVecDeque<T> = VecDeque<T>;
    type GenOption<T> = Option<T>;
    #[allow(dead_code)]
    type GenVec<T> = Vec<T>;

    /// 泛型性能计时器
    pub struct PerformanceTimer<T> {
        start_time: Instant,
        _phantom: GenPhantomData<T>,
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
            let elapsed: Duration = timer.elapsed();
            (result, elapsed)
        }
    }

    /// 泛型缓存系统
    pub struct Cache<K, V> {
        cache: GenHashMap<K, V>,
        max_size: usize,
        order: GenVecDeque<K>,
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
                order: VecDeque::new(),
            }
        }

        /// 获取值
        pub fn get(&self, key: &K) -> GenOption<&V> {
            self.cache.get(key)
        }

        /// 设置值
        pub fn set(&mut self, key: K, value: V) {
            self.update_order_if_exists(&key);
            self.evict_oldest_if_needed();
            self.cache.insert(key.clone(), value);
            self.order.push_back(key);
        }

        /// 如果键已存在，更新顺序
        fn update_order_if_exists(&mut self, key: &K) {
            if self.cache.contains_key(key) {
                self.order.retain(|k| k != key);
            }
        }

        /// 如果需要，移除最老的项
        fn evict_oldest_if_needed(&mut self) {
            while self.cache.len() >= self.max_size {
                self.remove_next_oldest();
            }
        }

        /// 移除下一个最老的项
        fn remove_next_oldest(&mut self) {
            if let Some(oldest) = self.order.pop_front() {
                self.cache.remove(&oldest);
            }
        }

        /// 清空缓存
        pub fn clear(&mut self) {
            self.cache.clear();
            self.order.clear();
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
        processor: Box<BatchFn<T, R>>,
    }

    type BatchFn<T, R> = dyn Fn(Vec<T>) -> Vec<R> + Send + Sync;

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
        pub fn process_batch(&self, data: GenVec<T>) -> GenVec<R> {
            (self.processor)(data)
        }

        /// 分批处理大量数据
        pub fn process_all(&self, mut data: GenVec<T>) -> GenVec<R> {
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

/// Rust 1.90 新特性示例
pub mod rust_190_improvements {
    use super::*;

    /// 改进的泛型类型推断
    pub fn improved_type_inference() {
        // Rust 1.90 在类型推断方面有所改进
        let numbers = [1, 2, 3, 4, 5];
        let doubled: Vec<i32> = numbers.iter()
            .map(|&x| x * 2)
            .collect();

        println!("改进的类型推断示例: {:?}", doubled);
    }

    /// 更简洁的泛型约束语法
    pub fn simplified_constraint_syntax<T>(value: T) -> T
    where
        T: Clone + Debug,
    {
        println!("值: {:?}", value);
        value.clone()
    }

    /// 增强的错误处理与泛型
    pub fn enhanced_error_handling<T, E>(result: Result<T, E>) -> Result<String, String>
    where
        T: Display,
        E: Display,
    {
        result.map(|v| format!("成功: {}", v))
              .map_err(|e| format!("错误: {}", e))
    }

    /// 改进的异步泛型
    pub async fn improved_async_generic<T>(value: T) -> T
    where
        T: Send + Sync + Clone,
    {
        // 模拟异步操作
        std::thread::sleep(Duration::from_millis(10));
        value.clone()
    }

    /// 更强大的类型别名
    pub type GenericResult<T, E = String> = Result<T, E>;
    pub type GenericOption<T> = Option<T>;

    /// 使用改进的类型别名
    pub fn use_improved_aliases(value: i32) -> GenericResult<i32> {
        if value > 0 {
            Ok(value * 2)
        } else {
            Err("值必须大于0".to_string())
        }
    }

    /// 改进的迭代器链式操作
    pub fn improved_iterator_chains() {
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        let result: Vec<i32> = data
            .into_iter()
            .filter(|&x| x % 2 == 0)
            .map(|x| x * x)
            .take(3)
            .collect();

        println!("改进的迭代器链: {:?}", result);
    }

    /// 更好的生命周期推断
    pub fn better_lifetime_inference<'a>(first: &'a str, second: &'a str) -> &'a str {
        if first.len() > second.len() {
            first
        } else {
            second
        }
    }

    /// 增强的 const 泛型
    pub fn enhanced_const_generics<const N: usize>(arr: [i32; N]) -> i32 {
        arr.iter().sum()
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_improved_type_inference() {
            improved_type_inference();
        }

        #[test]
        fn test_simplified_constraint_syntax() {
            let result = simplified_constraint_syntax(42);
            assert_eq!(result, 42);
        }

        #[test]
        fn test_enhanced_error_handling() {
            let ok_result = enhanced_error_handling::<i32, String>(Ok(42));
            assert!(ok_result.is_ok());

            let err_result = enhanced_error_handling::<i32, &str>(Err("测试错误"));
            assert!(err_result.is_err());
        }

        #[test]
        fn test_use_improved_aliases() {
            let result = use_improved_aliases(5);
            assert_eq!(result, Ok(10));

            let error = use_improved_aliases(-1);
            assert!(error.is_err());
        }

        #[test]
        fn test_improved_iterator_chains() {
            improved_iterator_chains();
        }

        #[test]
        fn test_better_lifetime_inference() {
            let first = "短";
            let second = "这是一个更长的字符串";
            let result = better_lifetime_inference(first, second);
            assert_eq!(result, second);
        }

        #[test]
        fn test_enhanced_const_generics() {
            let arr = [1, 2, 3, 4, 5];
            let sum = enhanced_const_generics(arr);
            assert_eq!(sum, 15);
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
    algorithms::quicksort(&mut arr);
    println!("快速排序结果: {:?}", arr);

    let search_arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
    let index = algorithms::binary_search(&search_arr, &7);
    println!("二分搜索结果: {:?}", index);

    println!("\n3. 并发编程示例:");
    let counter = concurrency::ThreadSafeCounter::new(0);
    counter.increment();
    println!("线程安全计数器: {}", counter.get());

    let data = concurrency::ReadWriteData::new(vec![1, 2, 3]);
    let len = data.read(|vec: &Vec<i32>| vec.len());
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
        algorithms::fibonacci::<u32>(20)
    });
    println!("斐波那契(20) = {}, 耗时: {:?}", result, elapsed);

    let mut cache = performance::Cache::new(3);
    cache.set("key1", "value1");
    cache.set("key2", "value2");
    println!("缓存大小: {}", cache.len());

    println!("\n6. Rust 1.90 改进示例:");
    rust_190_improvements::improved_type_inference();
    rust_190_improvements::improved_iterator_chains();

    let improved_result = rust_190_improvements::use_improved_aliases(10);
    match improved_result {
        Ok(value) => println!("改进的类型别名结果: {}", value),
        Err(e) => println!("错误: {}", e),
    }

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
