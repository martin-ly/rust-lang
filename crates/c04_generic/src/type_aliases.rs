//! 类型别名定义模块
//! type definition module
//! 该模块包含项目中使用的所有复杂类型别名，
//! this module project in all complex type ，
//! 用于简化类型复杂度并提高代码可读性。
//! type complex and 。
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
    sync::{Arc, Mutex, RwLock},
    thread::JoinHandle,
    time::Instant,
};

// =============================================================================
// 基础类型别名
// =============================================================================

/// 线程句柄类型别名
/// thread type
pub type ThreadHandle<T> = JoinHandle<T>;

/// 线程句柄向量类型别名
/// thread type
pub type ThreadHandles<T> = Vec<ThreadHandle<T>>;

/// 共享计数器类型别名
/// type
pub type SharedCounter = Arc<Mutex<i32>>;

/// 共享数据向量类型别名
/// type
pub type SharedVec<T> = Arc<Mutex<Vec<T>>>;

/// 共享哈希映射类型别名
/// type
pub type SharedHashMap<K, V> = Arc<Mutex<HashMap<K, V>>>;

/// 读写锁保护的数据类型别名
/// rwlock type
pub type RwLockData<T> = Arc<RwLock<T>>;

/// 原子计数器类型别名
/// atomic counter type
pub type AtomicCounter = Arc<std::sync::atomic::AtomicUsize>;

/// 原子布尔值类型别名
/// type
pub type AtomicBool = Arc<std::sync::atomic::AtomicBool>;

// =============================================================================
// 迭代器和函数类型别名
// =============================================================================

/// 迭代器类型别名
/// type
pub type IteratorType<T> = Box<dyn Iterator<Item = T> + Send>;

/// 并行迭代器类型别名
/// parallelism type
pub type ParIteratorType<T> = rayon::slice::Iter<'static, T>;

/// 映射函数类型别名
/// function type
pub type MapFn<T, U> = Box<dyn Fn(T) -> U + Send + Sync>;

/// 过滤函数类型别名
/// function type
pub type FilterFn<T> = Box<dyn Fn(&T) -> bool + Send + Sync>;

/// 折叠函数类型别名
/// function type
pub type FoldFn<T, U> = Box<dyn Fn(U, T) -> U + Send + Sync>;

// =============================================================================
// 错误处理类型别名
// =============================================================================

/// 通用结果类型别名
/// result type
pub type GenericResult<T, E = String> = Result<T, E>;

/// 应用结果类型别名
/// application result type
pub type AppResult<T> = Result<T, String>;

/// 处理结果类型别名
/// result type
pub type ProcessResult<T> = Result<T, String>;

/// 机器学习结果类型别名
/// machine learning result type
pub type MLResult<T> = Result<T, String>;

// =============================================================================
// 数据结构类型别名
// =============================================================================

/// 环形缓冲区类型别名
/// buffering type
pub type RingBuffer<T> = VecDeque<T>;

/// 内存数据块类型别名
/// memory type
pub type MemoryData = Vec<Vec<u8>>;

/// 可排序向量类型别名
/// ordering type
pub type SortableVec = Vec<i32>;

/// 哈希集合类型别名
/// set type
pub type HashSetType<T> = HashSet<T>;

/// 哈希映射类型别名
/// type
pub type HashMapType<K, V> = HashMap<K, V>;

// =============================================================================
// 异步和并发类型别名
// =============================================================================

/// 异步任务类型别名
/// async task type
pub type AsyncTask = Box<dyn std::future::Future<Output = ()> + Send + Unpin>;

/// 异步结果类型别名
/// async result type
pub type AsyncResult<T> =
    std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, String>> + Send>>;

/// 通道发送器类型别名
/// channel type
pub type Sender<T> = std::sync::mpsc::Sender<T>;

/// 通道接收器类型别名
/// channel type
pub type Receiver<T> = std::sync::mpsc::Receiver<T>;

/// 异步通道发送器类型别名
/// async channel type
pub type AsyncSender<T> = std::sync::mpsc::Sender<T>;

/// 异步通道接收器类型别名
/// async channel type
pub type AsyncReceiver<T> = std::sync::mpsc::Receiver<T>;

// =============================================================================
// 复杂泛型类型别名
// =============================================================================

/// 处理器类型别名
/// type
pub type Processor<T, R> = Box<dyn Fn(T) -> R + Send + Sync>;

/// 验证器类型别名
/// type
pub type Validator<T> = Box<dyn Fn(&T) -> bool + Send + Sync>;

/// 转换器类型别名
/// conversion type
pub type Converter<T, U> = Box<dyn Fn(T) -> U + Send + Sync>;

/// 序列化器类型别名
/// sequence type
pub type Serializer<T> = Box<dyn Fn(&T) -> Result<String, String> + Send + Sync>;

/// 反序列化器类型别名
/// sequence type
pub type Deserializer<T> = Box<dyn Fn(&str) -> Result<T, String> + Send + Sync>;

// =============================================================================
// 特定领域类型别名
// =============================================================================

/// 图形节点类型别名
/// node type
pub type GraphNode<T> = HashMap<T, Vec<T>>;

/// 加权边类型别名
/// edge type
pub type WeightedEdge<T> = (T, T, f64);

/// 图形类型别名
/// type
pub type Graph<T> = HashMap<T, Vec<(T, f64)>>;

/// 数据点类型别名
/// point type
pub type DataPoint = Vec<f64>;

/// 数据集类型别名
/// type
pub type Dataset = Vec<DataPoint>;

/// 标签类型别名
/// type
pub type Labels = Vec<usize>;

/// 聚类中心类型别名
/// center type
pub type ClusterCenters = Vec<DataPoint>;

// =============================================================================
// 缓存和性能类型别名
// =============================================================================

/// 缓存类型别名
/// type
pub type Cache<K, V> = HashMap<K, V>;

/// 性能计时器类型别名
/// performance type
pub type PerformanceTimer = Instant;

/// 批处理函数类型别名
/// function type
pub type BatchFn<T, R> = Box<dyn Fn(Vec<T>) -> Vec<R> + Send + Sync>;

/// 批处理器类型别名
/// type
pub type BatchProcessor<T, R> = (usize, BatchFn<T, R>);

// =============================================================================
// 配置和选项类型别名
// =============================================================================

/// 配置类型别名
/// type
pub type Config = HashMap<String, String>;

/// 选项类型别名
/// type
pub type OptionType<T> = Option<T>;

/// 结果类型别名
/// result type
pub type ResultType<T, E> = Result<T, E>;

/// 向量类型别名
/// type
pub type VectorType<T> = Vec<T>;

/// 数组类型别名
/// type
pub type ArrayType<T, const N: usize> = [T; N];

// =============================================================================
// 生命周期相关类型别名
// =============================================================================

/// 生命周期引用类型别名
/// lifetime reference type
pub type RefType<'a, T> = &'a T;

/// 可变生命周期引用类型别名
/// lifetime reference type
pub type MutRefType<'a, T> = &'a mut T;

/// 生命周期切片类型别名
/// lifetime type
pub type SliceType<'a, T> = &'a [T];

/// 生命周期字符串切片类型别名
/// lifetime type
pub type StrSliceType<'a> = &'a str;

/// 生命周期字符串类型别名
/// lifetime type
pub type StringType<'a> = &'a String;

// =============================================================================
// 特征对象类型别名
// =============================================================================

/// 可克隆特征对象类型别名
/// to type
pub type Cloneable = Box<dyn Clone>;

/// 可调试特征对象类型别名
/// to type
pub type Debuggable = Box<dyn Debug>;

/// 可显示特征对象类型别名
/// display to type
pub type Displayable = Box<dyn std::fmt::Display>;

/// 可发送特征对象类型别名
/// to type
pub type Sendable = Box<dyn Send>;

/// 可同步特征对象类型别名
/// synchronous to type
pub type Syncable = Box<dyn Sync>;

/// 可发送同步特征对象类型别名
/// synchronous to type
pub type SendSync = Box<dyn Send + Sync>;

// =============================================================================
// 实用工具类型别名
// =============================================================================

/// 空类型别名
/// type
pub type Empty = ();

/// 单位类型别名
/// type
pub type Unit = ();

/// 布尔类型别名
/// type
pub type Bool = bool;

/// 整数类型别名
/// type
pub type Int = i32;

/// 无符号整数类型别名
/// symbol type
pub type UInt = u32;

/// 浮点数类型别名
/// point type
pub type Float = f64;

/// 字符串类型别名
/// type
pub type String = std::string::String;

/// 字符类型别名
/// type
pub type Char = char;

/// 字节类型别名
/// type
pub type Byte = u8;

/// 字节向量类型别名
/// type
pub type ByteVec = Vec<u8>;

/// 字节数组类型别名
/// type
pub type ByteArray = [u8; 32];

// =============================================================================
// 复杂组合类型别名
// =============================================================================

/// 复杂处理器类型别名
/// complex type
pub type ComplexProcessor<T, U, V> = Box<dyn Fn(T, U) -> V + Send + Sync>;

/// 复杂验证器类型别名
/// complex type
pub type ComplexValidator<T, U> = Box<dyn Fn(&T, &U) -> bool + Send + Sync>;

/// 复杂转换器类型别名
/// complex conversion type
pub type ComplexConverter<T, U, V> = Box<dyn Fn(T, U) -> V + Send + Sync>;

/// 复杂序列化器类型别名
/// complex sequence type
pub type ComplexSerializer<T, U> = Box<dyn Fn(&T, &U) -> Result<String, String> + Send + Sync>;

/// 复杂反序列化器类型别名
/// complex sequence type
pub type ComplexDeserializer<T, U> = Box<dyn Fn(&str, &U) -> Result<T, String> + Send + Sync>;

// =============================================================================
// 泛型编程专用类型别名
// =============================================================================

/// 泛型向量类型别名
/// generic type
pub type GenVec<T> = Vec<T>;

/// 泛型切片类型别名
/// generic type
pub type GenSlice<'a, T> = &'a [T];

/// 泛型选项类型别名
/// generic type
pub type GenOption<T> = Option<T>;

/// 泛型结果类型别名
/// generic result type
pub type GenResult<T, E> = Result<T, E>;

/// 泛型哈希映射类型别名
/// generic type
pub type GenHashMap<K, V> = HashMap<K, V>;

/// 泛型哈希集合类型别名
/// generic set type
pub type GenHashSet<T> = HashSet<T>;

/// 泛型双端队列类型别名
/// generic type
pub type GenVecDeque<T> = VecDeque<T>;

/// 泛型数组类型别名
/// generic type
pub type GenArray<T, const N: usize> = [T; N];

/// 泛型函数指针类型别名
/// generic function pointer type
pub type GenFn<T, U> = fn(T) -> U;

/// 泛型闭包类型别名
/// generic type
pub type GenClosure<T, U> = Box<dyn Fn(T) -> U + Send + Sync>;

/// 泛型迭代器类型别名
/// generic type
pub type GenIterator<T> = Box<dyn Iterator<Item = T> + Send>;

/// 泛型并行迭代器类型别名
/// generic parallelism type
pub type GenParIterator<T> = rayon::slice::Iter<'static, T>;

// =============================================================================
// 常用复杂类型别名
// =============================================================================

/// 标准结果类型别名
/// standard result type
pub type StdResult<T, E> = std::result::Result<T, E>;

/// 标准选项类型别名
/// standard type
pub type StdOption<T> = std::option::Option<T>;

/// 标准向量类型别名
/// standard type
pub type StdVec<T> = std::vec::Vec<T>;

/// 标准切片类型别名
/// standard type
pub type StdSlice<'a, T> = &'a [T];

/// 标准字符串切片类型别名
/// standard type
pub type StdStrSlice<'a> = &'a str;

/// 标准字符串类型别名
/// standard type
pub type StdString = std::string::String;

/// 标准哈希映射类型别名
/// standard type
pub type StdHashMap<K, V> = std::collections::HashMap<K, V>;

/// 标准哈希集合类型别名
/// standard set type
pub type StdHashSet<T> = std::collections::HashSet<T>;

/// 标准双端队列类型别名
/// standard type
pub type StdVecDeque<T> = std::collections::VecDeque<T>;

// =============================================================================
// 线程和并发相关类型别名
// =============================================================================

/// 线程句柄类型别名
/// thread type
pub type ThreadJoinHandle<T> = std::thread::JoinHandle<T>;

/// 线程句柄向量类型别名
/// thread type
pub type ThreadJoinHandles<T> = Vec<ThreadJoinHandle<T>>;

/// 互斥锁类型别名
/// mutex type
pub type MutexType<T> = std::sync::Mutex<T>;

/// 读写锁类型别名
/// rwlock type
pub type RwLockType<T> = std::sync::RwLock<T>;

/// 原子计数器类型别名
/// atomic counter type
pub type AtomicUsize = std::sync::atomic::AtomicUsize;

/// 原子布尔值类型别名（无 Arc 包装）
/// type （ Arc ）
pub type AtomicBoolType = std::sync::atomic::AtomicBool;

/// 原子整数类型别名
/// type
pub type AtomicI32 = std::sync::atomic::AtomicI32;

/// 原子无符号整数类型别名
/// symbol type
pub type AtomicU32 = std::sync::atomic::AtomicU32;

// =============================================================================
// 通道相关类型别名
// =============================================================================

/// 通道发送器类型别名
/// channel type
pub type ChannelSender<T> = std::sync::mpsc::Sender<T>;

/// 通道接收器类型别名
/// channel type
pub type ChannelReceiver<T> = std::sync::mpsc::Receiver<T>;

/// 通道错误类型别名
/// channel error type
pub type ChannelError<T> = std::sync::mpsc::SendError<T>;

/// 通道接收错误类型别名
/// channel error type
pub type ChannelRecvError = std::sync::mpsc::RecvError;

// =============================================================================
// 异步相关类型别名
// =============================================================================

/// 异步任务类型别名（无 Arc 包装）
/// async task type （ Arc ）
pub type AsyncTaskType = Box<dyn std::future::Future<Output = ()> + Send + Unpin>;

/// 异步结果类型别名（无 Arc 包装）
/// async result type （ Arc ）
pub type AsyncResultType<T> =
    std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, String>> + Send>>;

/// 异步发送器类型别名（无 Arc 包装）
/// async type （ Arc ）
pub type AsyncSenderType<T> = std::sync::mpsc::Sender<T>;

/// 异步接收器类型别名（无 Arc 包装）
/// async type （ Arc ）
pub type AsyncReceiverType<T> = std::sync::mpsc::Receiver<T>;

// =============================================================================
// 错误处理类型别名
// =============================================================================

/// 通用错误类型别名
/// error type
pub type GenericError = String;

/// 应用错误类型别名
/// application error type
pub type AppError = String;

/// 处理错误类型别名
/// error type
pub type ProcessError = String;

/// 验证错误类型别名
/// error type
pub type ValidationError = String;

/// 序列化错误类型别名
/// sequence error type
pub type SerializationError = String;

/// 反序列化错误类型别名
/// sequence error type
pub type DeserializationError = String;

// =============================================================================
// 导出所有类型别名
// =============================================================================

// 注意：由于这些类型别名已经在同一个模块中定义，
// 我们不需要使用 pub use 重新导出它们
// 它们已经可以通过模块路径访问
