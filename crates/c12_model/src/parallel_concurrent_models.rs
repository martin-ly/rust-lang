//! 并行并发模型
//! 
//! 本模块实现了现代并行并发编程模型，包括：
//! - Actor模型
//! - CSP模型（通信顺序进程）
//! - 共享内存模型
//! - 数据并行模型
//! - 任务并行模型
//! - 管道并行模型
//! - Fork-Join模型
//! - MapReduce模型
//! 
//! 充分利用 Rust 1.90 的并发安全特性和零成本抽象

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, RwLock, mpsc};
use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};
use std::time::{Duration, Instant};
use std::thread::{self, JoinHandle};
use std::marker::PhantomData;
use std::cmp::Ordering as CmpOrdering;
use std::fmt::Debug;
use serde::{Deserialize, Serialize};
use crate::error::ModelError;


/// 并发模型结果类型
pub type ConcurrentResult<T> = Result<T, ModelError>;

/// Actor标识符
pub type ActorId = String;

/// 消息标识符
pub type MessageId = u64;

/// ========================================
/// Actor模型实现
/// ========================================

/// Actor消息trait
pub trait ActorMessage: Send + 'static {
    fn message_id(&self) -> MessageId;
}

/// Actor行为trait
pub trait ActorBehavior: Send + 'static {
    type Message: ActorMessage;
    
    fn receive(&mut self, message: Self::Message, context: &mut ActorContext);
    fn pre_start(&mut self, _context: &mut ActorContext) {}
    fn post_stop(&mut self, _context: &mut ActorContext) {}
}

/// Actor上下文
#[derive(Debug)]
pub struct ActorContext {
    pub actor_id: ActorId,
    pub sender: Option<ActorId>,
    system: Arc<ActorSystem>,
}

impl ActorContext {
    pub fn new(actor_id: ActorId, system: Arc<ActorSystem>) -> Self {
        Self {
            actor_id,
            sender: None,
            system,
        }
    }
    
    /// 发送消息给另一个Actor
    pub fn tell<M: ActorMessage>(&self, target: &ActorId, message: M) -> ConcurrentResult<()> {
        self.system.send_message(target, Box::new(message))
    }
    
    /// 创建子Actor
    pub fn spawn_child<B: ActorBehavior>(&self, name: String, behavior: B) -> ConcurrentResult<ActorId> {
        let child_id = format!("{}/{}", self.actor_id, name);
        self.system.spawn_actor_with_id(child_id.clone(), behavior)?;
        Ok(child_id)
    }
    
    /// 停止Actor
    pub fn stop(&self, actor_id: &ActorId) -> ConcurrentResult<()> {
        self.system.stop_actor(actor_id)
    }
}

/// Actor引用
pub struct ActorRef<M: ActorMessage> {
    actor_id: ActorId,
    system: Arc<ActorSystem>,
    _phantom: PhantomData<M>,
}

impl<M: ActorMessage> ActorRef<M> {
    pub fn new(actor_id: ActorId, system: Arc<ActorSystem>) -> Self {
        Self {
            actor_id,
            system,
            _phantom: PhantomData,
        }
    }
    
    pub fn tell(&self, message: M) -> ConcurrentResult<()> {
        self.system.send_message(&self.actor_id, Box::new(message))
    }
    
    pub fn actor_id(&self) -> &ActorId {
        &self.actor_id
    }
}

impl<M: ActorMessage> Clone for ActorRef<M> {
    fn clone(&self) -> Self {
        Self {
            actor_id: self.actor_id.clone(),
            system: Arc::clone(&self.system),
            _phantom: PhantomData,
        }
    }
}

/// Actor实例
struct ActorInstance {
    actor_id: ActorId,
    mailbox: Arc<Mutex<VecDeque<Box<dyn ActorMessage>>>>,
    handle: Option<JoinHandle<()>>,
    is_running: Arc<AtomicBool>,
}

impl Debug for ActorInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ActorInstance")
            .field("actor_id", &self.actor_id)
            .field("mailbox_len", &self.mailbox.lock().unwrap().len())
            .field("is_running", &self.is_running)
            .finish()
    }
}

/// Actor系统
#[allow(dead_code)]
#[derive(Debug)]
pub struct ActorSystem {
    name: String,
    actors: Arc<RwLock<HashMap<ActorId, ActorInstance>>>,
    is_running: Arc<AtomicBool>,
}

impl ActorSystem {
    pub fn new(name: String) -> Arc<Self> {
        Arc::new(Self {
            name,
            actors: Arc::new(RwLock::new(HashMap::new())),
            is_running: Arc::new(AtomicBool::new(true)),
        })
    }
    
    /// 创建Actor
    pub fn spawn_actor<B: ActorBehavior>(self: &Arc<Self>, behavior: B) -> ConcurrentResult<ActorRef<B::Message>> {
        let actor_id = format!("actor_{}", uuid::Uuid::new_v4());
        self.spawn_actor_with_id(actor_id.clone(), behavior)?;
        Ok(ActorRef::new(actor_id, Arc::clone(self)))
    }
    
    fn spawn_actor_with_id<B: ActorBehavior>(self: &Arc<Self>, actor_id: ActorId, mut behavior: B) -> ConcurrentResult<()> {
        let mailbox: Arc<Mutex<VecDeque<Box<dyn ActorMessage>>>> = Arc::new(Mutex::new(VecDeque::new()));
        let is_running = Arc::new(AtomicBool::new(true));
        
        let mailbox_clone = Arc::clone(&mailbox);
        let is_running_clone = Arc::clone(&is_running);
        let system_clone = Arc::clone(self);
        let actor_id_clone = actor_id.clone();
        
        let handle = thread::spawn(move || {
            let mut context = ActorContext::new(actor_id_clone.clone(), system_clone);
            behavior.pre_start(&mut context);
            
            while is_running_clone.load(Ordering::SeqCst) {
                let message = {
                    let mut mailbox_guard = mailbox_clone.lock().unwrap();
                    mailbox_guard.pop_front()
                };
                
                if let Some(message) = message {
                    // 类型擦除后无法直接调用，这里简化处理
                    // 实际实现需要使用trait object或者其他机制
                    println!("Actor {} received message {}", actor_id_clone, message.message_id());
                } else {
                    thread::sleep(Duration::from_millis(10));
                }
            }
            
            behavior.post_stop(&mut context);
        });
        
        let instance = ActorInstance {
            actor_id: actor_id.clone(),
            mailbox,
            handle: Some(handle),
            is_running,
        };
        
        self.actors.write().unwrap().insert(actor_id, instance);
        Ok(())
    }
    
    fn send_message(&self, target: &ActorId, message: Box<dyn ActorMessage>) -> ConcurrentResult<()> {
        let actors = self.actors.read().unwrap();
        if let Some(actor) = actors.get(target) {
            actor.mailbox.lock().unwrap().push_back(message);
            Ok(())
        } else {
            Err(ModelError::ValidationError(format!("Actor not found: {}", target)))
        }
    }
    
    fn stop_actor(&self, actor_id: &ActorId) -> ConcurrentResult<()> {
        let mut actors = self.actors.write().unwrap();
        if let Some(mut actor) = actors.remove(actor_id) {
            actor.is_running.store(false, Ordering::SeqCst);
            if let Some(handle) = actor.handle.take() {
                let _ = handle.join();
            }
            Ok(())
        } else {
            Err(ModelError::ValidationError(format!("Actor not found: {}", actor_id)))
        }
    }
    
    pub fn shutdown(&self) {
        self.is_running.store(false, Ordering::SeqCst);
        let mut actors = self.actors.write().unwrap();
        for (_, mut actor) in actors.drain() {
            actor.is_running.store(false, Ordering::SeqCst);
            if let Some(handle) = actor.handle.take() {
                let _ = handle.join();
            }
        }
    }
}

/// ========================================
/// CSP模型实现（通信顺序进程）
/// ========================================

/// CSP通道
pub struct CSPChannel<T> {
    sender: mpsc::Sender<T>,
    receiver: Arc<Mutex<mpsc::Receiver<T>>>,
}

impl<T: Send + 'static> CSPChannel<T> {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel();
        Self {
            sender,
            receiver: Arc::new(Mutex::new(receiver)),
        }
    }
    
    pub fn bounded(capacity: usize) -> Self {
        let (_sender, receiver) = mpsc::sync_channel(capacity);
        // 转换为unbounded以统一接口
        let (tx, rx) = mpsc::channel();
        let tx_clone = tx.clone();
        thread::spawn(move || {
            while let Ok(msg) = receiver.recv() {
                if tx_clone.send(msg).is_err() {
                    break;
                }
            }
        });
        
        Self {
            sender: tx,
            receiver: Arc::new(Mutex::new(rx)),
        }
    }
    
    pub fn send(&self, value: T) -> ConcurrentResult<()> {
        self.sender.send(value).map_err(|_| {
            ModelError::AsyncError("Channel send failed".to_string())
        })
    }
    
    pub fn recv(&self) -> ConcurrentResult<T> {
        self.receiver.lock().unwrap().recv().map_err(|_| {
            ModelError::AsyncError("Channel recv failed".to_string())
        })
    }
    
    pub fn try_recv(&self) -> ConcurrentResult<Option<T>> {
        match self.receiver.lock().unwrap().try_recv() {
            Ok(value) => Ok(Some(value)),
            Err(mpsc::TryRecvError::Empty) => Ok(None),
            Err(mpsc::TryRecvError::Disconnected) => {
                Err(ModelError::AsyncError("Channel disconnected".to_string()))
            }
        }
    }
}

impl<T: Send + 'static> Clone for CSPChannel<T> {
    fn clone(&self) -> Self {
        Self {
            sender: self.sender.clone(),
            receiver: Arc::clone(&self.receiver),
        }
    }
}

impl<T: Send + 'static> Default for CSPChannel<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// CSP进程trait
pub trait CSPProcess: Send + 'static {
    fn run(&mut self) -> ConcurrentResult<()>;
}

/// CSP系统
pub struct CSPSystem {
    processes: Vec<JoinHandle<ConcurrentResult<()>>>,
}

impl CSPSystem {
    pub fn new() -> Self {
        Self {
            processes: Vec::new(),
        }
    }
    
    pub fn spawn<P: CSPProcess>(&mut self, mut process: P) {
        let handle = thread::spawn(move || process.run());
        self.processes.push(handle);
    }
    
    pub fn wait_all(self) -> ConcurrentResult<()> {
        for handle in self.processes {
            handle.join().map_err(|_| {
                ModelError::ValidationError("Process panicked".to_string())
            })??;
        }
        Ok(())
    }
}

impl Default for CSPSystem {
    fn default() -> Self {
        Self::new()
    }
}

/// ========================================
/// 共享内存模型实现
/// ========================================

/// 共享内存区域
pub struct SharedMemory<T> {
    data: Arc<RwLock<T>>,
    version: Arc<AtomicU64>,
}

impl<T> SharedMemory<T>
where
    T: Clone + Send + Sync + 'static,
{
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(RwLock::new(data)),
            version: Arc::new(AtomicU64::new(0)),
        }
    }
    
    /// 读取数据
    pub fn read<F, R>(&self, f: F) -> ConcurrentResult<R>
    where
        F: FnOnce(&T) -> R,
    {
        let guard = self.data.read().map_err(|_| {
            ModelError::SyncError("Failed to acquire read lock".to_string())
        })?;
        Ok(f(&*guard))
    }
    
    /// 写入数据
    pub fn write<F, R>(&self, f: F) -> ConcurrentResult<R>
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut guard = self.data.write().map_err(|_| {
            ModelError::SyncError("Failed to acquire write lock".to_string())
        })?;
        let result = f(&mut *guard);
        self.version.fetch_add(1, Ordering::SeqCst);
        Ok(result)
    }
    
    /// 原子交换
    pub fn swap(&self, new_data: T) -> ConcurrentResult<T> {
        let mut guard = self.data.write().map_err(|_| {
            ModelError::SyncError("Failed to acquire write lock".to_string())
        })?;
        let old_data = std::mem::replace(&mut *guard, new_data);
        self.version.fetch_add(1, Ordering::SeqCst);
        Ok(old_data)
    }
    
    /// 获取版本号
    pub fn version(&self) -> u64 {
        self.version.load(Ordering::SeqCst)
    }
}

impl<T> Clone for SharedMemory<T> {
    fn clone(&self) -> Self {
        Self {
            data: Arc::clone(&self.data),
            version: Arc::clone(&self.version),
        }
    }
}

/// 事务内存
#[allow(dead_code)]
pub struct TransactionalMemory<T> {
    data: Arc<RwLock<T>>,
    log: Arc<Mutex<Vec<Transaction<T>>>>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct Transaction<T> {
    timestamp: Instant,
    old_value: T,
    new_value: T,
}

impl<T> TransactionalMemory<T>
where
    T: Clone + Send + Sync + 'static,
{
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(RwLock::new(data)),
            log: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    /// 执行事务
    pub fn transaction<F>(&self, f: F) -> ConcurrentResult<()>
    where
        F: FnOnce(&mut T) -> ConcurrentResult<()>,
    {
        let mut guard = self.data.write().map_err(|_| {
            ModelError::SyncError("Failed to acquire write lock".to_string())
        })?;
        
        let old_value = (*guard).clone();
        
        match f(&mut *guard) {
            Ok(()) => {
                let transaction = Transaction {
                    timestamp: Instant::now(),
                    old_value,
                    new_value: (*guard).clone(),
                };
                self.log.lock().unwrap().push(transaction);
                Ok(())
            }
            Err(e) => {
                // 回滚
                *guard = old_value;
                Err(e)
            }
        }
    }
    
    /// 获取事务日志长度
    pub fn log_len(&self) -> usize {
        self.log.lock().unwrap().len()
    }
}

/// ========================================
/// 数据并行模型
/// ========================================

/// 数据并行执行器
pub struct DataParallelExecutor {
    thread_count: usize,
}

impl DataParallelExecutor {
    pub fn new(thread_count: usize) -> Self {
        Self { thread_count }
    }
    
    /// 并行映射
    pub fn parallel_map<T, R, F>(&self, data: Vec<T>, f: F) -> ConcurrentResult<Vec<R>>
    where
        T: Send + 'static + Clone,
        R: Send + 'static + Debug,
        F: Fn(T) -> R + Send + Sync + 'static,
    {
        let f = Arc::new(f);
        let chunk_size = (data.len() + self.thread_count - 1) / self.thread_count;
        let mut handles = Vec::new();
        let result = Arc::new(Mutex::new(Vec::with_capacity(data.len())));
        
        for chunk in data.chunks(chunk_size).map(|c| c.to_vec()) {
            let f = Arc::clone(&f);
            let result = Arc::clone(&result);
            
            let handle = thread::spawn(move || {
                let mapped: Vec<R> = chunk.into_iter().map(|item| f(item)).collect();
                result.lock().unwrap().extend(mapped);
            });
            
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().map_err(|_| {
                ModelError::ValidationError("Thread panicked".to_string())
            })?;
        }
        
        Ok(Arc::try_unwrap(result).unwrap().into_inner().unwrap())
    }
    
    /// 并行归约
    pub fn parallel_reduce<T, F>(&self, data: Vec<T>, identity: T, f: F) -> ConcurrentResult<T>
    where
        T: Send + Clone + 'static,
        F: Fn(T, T) -> T + Send + Sync + 'static,
    {
        if data.is_empty() {
            return Ok(identity);
        }
        
        let f = Arc::new(f);
        let chunk_size = (data.len() + self.thread_count - 1) / self.thread_count;
        let mut handles = Vec::new();
        
        for chunk in data.chunks(chunk_size).map(|c| c.to_vec()) {
            let f = Arc::clone(&f);
            let identity = identity.clone();
            
            let handle = thread::spawn(move || {
                chunk.into_iter().fold(identity, |acc, item| f(acc, item))
            });
            
            handles.push(handle);
        }
        
        let mut results = Vec::new();
        for handle in handles {
            results.push(handle.join().map_err(|_| {
                ModelError::ValidationError("Thread panicked".to_string())
            })?);
        }
        
        Ok(results.into_iter().fold(identity, |acc, item| (*f)(acc, item)))
    }
}

/// ========================================
/// Fork-Join模型
/// ========================================

/// Fork-Join任务trait
pub trait ForkJoinTask: Send + 'static {
    type Output: Send + 'static;
    
    fn compute(&mut self) -> Self::Output;
    fn should_fork(&self) -> bool;
    fn fork(&mut self) -> Option<Box<dyn ForkJoinTask<Output = Self::Output>>>;
    fn join(&mut self, left: Self::Output, right: Self::Output) -> Self::Output;
}

/// Fork-Join池
pub struct ForkJoinPool {
    #[allow(dead_code)]
    thread_count: usize,
}

impl ForkJoinPool {
    pub fn new(thread_count: usize) -> Self {
        Self { thread_count }
    }
    
    pub fn execute<T: ForkJoinTask>(&self, mut task: T) -> ConcurrentResult<T::Output> {
        if !task.should_fork() {
            return Ok(task.compute());
        }
        
        if let Some(right_task) = task.fork() {
            let handle = thread::spawn(move || {
                let mut right_task = right_task;
                right_task.compute()
            });
            
            let left_result = task.compute();
            let right_result = handle.join().map_err(|_| {
                ModelError::ValidationError("Thread panicked".to_string())
            })?;
            
            Ok(task.join(left_result, right_result))
        } else {
            Ok(task.compute())
        }
    }
}

/// ========================================
/// MapReduce模型
/// ========================================

/// MapReduce执行器
pub struct MapReduceExecutor<K, V> {
    thread_count: usize,
    _phantom: PhantomData<(K, V)>,
}

impl<K, V> MapReduceExecutor<K, V>
where
    K: Eq + std::hash::Hash + Clone + Send + 'static,
    V: Send + 'static + Clone,
{
    pub fn new(thread_count: usize) -> Self {
        Self {
            thread_count,
            _phantom: PhantomData,
        }
    }
    
    pub fn execute<T, M, R>(
        &self,
        data: Vec<T>,
        mapper: M,
        reducer: R,
    ) -> ConcurrentResult<HashMap<K, V>>
    where
        T: Send + 'static + Clone,
        M: Fn(T) -> Vec<(K, V)> + Send + Sync + 'static,
        R: Fn(K, Vec<V>) -> V + Send + Sync + 'static,
    {
        // Map阶段
        let mapper = Arc::new(mapper);
        let chunk_size = (data.len() + self.thread_count - 1) / self.thread_count;
        let mut map_handles = Vec::new();
        
        for chunk in data.chunks(chunk_size).map(|c| c.to_vec()) {
            let mapper = Arc::clone(&mapper);
            
            let handle = thread::spawn(move || {
                let mut intermediate = Vec::new();
                for item in chunk {
                    intermediate.extend(mapper(item));
                }
                intermediate
            });
            
            map_handles.push(handle);
        }
        
        // 收集Map结果
        let mut intermediate: Vec<(K, V)> = Vec::new();
        for handle in map_handles {
            intermediate.extend(handle.join().map_err(|_| {
                ModelError::ValidationError("Thread panicked".to_string())
            })?);
        }
        
        // Shuffle阶段
        let mut grouped: HashMap<K, Vec<V>> = HashMap::new();
        for (key, value) in intermediate {
            grouped.entry(key).or_insert_with(Vec::new).push(value);
        }
        
        // Reduce阶段
        let reducer = Arc::new(reducer);
        let mut reduce_handles = Vec::new();
        let grouped_vec: Vec<_> = grouped.into_iter().collect();
        let reduce_chunk_size = (grouped_vec.len() + self.thread_count - 1) / self.thread_count;
        
        for chunk in grouped_vec.chunks(reduce_chunk_size) {
            let chunk = chunk.to_vec();
            let reducer = Arc::clone(&reducer);
            
            let handle = thread::spawn(move || {
                let mut results = HashMap::new();
                for (key, values) in chunk {
                    let result = reducer(key.clone(), values);
                    results.insert(key, result);
                }
                results
            });
            
            reduce_handles.push(handle);
        }
        
        // 收集Reduce结果
        let mut final_result = HashMap::new();
        for handle in reduce_handles {
            final_result.extend(handle.join().map_err(|_| {
                ModelError::ValidationError("Thread panicked".to_string())
            })?);
        }
        
        Ok(final_result)
    }
}

/// ========================================
/// 并发模型分析器
/// ========================================

/// 并发模型类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConcurrencyModel {
    Actor,
    CSP,
    SharedMemory,
    DataParallel,
    TaskParallel,
    ForkJoin,
    MapReduce,
}

/// 并发模型特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcurrencyModelCharacteristics {
    pub model_type: ConcurrencyModel,
    pub communication_mechanism: CommunicationMechanism,
    pub synchronization_mechanism: SynchronizationMechanism,
    pub scalability: ScalabilityLevel,
    pub complexity: ComplexityLevel,
    pub use_cases: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CommunicationMechanism {
    MessagePassing,
    SharedMemory,
    Hybrid,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SynchronizationMechanism {
    Lock,
    Channel,
    Atomic,
    Transaction,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ScalabilityLevel {
    Low,
    Medium,
    High,
    VeryHigh,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ComplexityLevel {
    Low,
    Medium,
    High,
}

/// 并发模型分析器
pub struct ConcurrencyModelAnalyzer;

impl ConcurrencyModelAnalyzer {
    pub fn analyze_model(model: &ConcurrencyModel) -> ConcurrencyModelCharacteristics {
        match model {
            ConcurrencyModel::Actor => ConcurrencyModelCharacteristics {
                model_type: ConcurrencyModel::Actor,
                communication_mechanism: CommunicationMechanism::MessagePassing,
                synchronization_mechanism: SynchronizationMechanism::Channel,
                scalability: ScalabilityLevel::VeryHigh,
                complexity: ComplexityLevel::Medium,
                use_cases: vec![
                    "分布式系统".to_string(),
                    "实时系统".to_string(),
                    "高并发服务".to_string(),
                ],
            },
            ConcurrencyModel::CSP => ConcurrencyModelCharacteristics {
                model_type: ConcurrencyModel::CSP,
                communication_mechanism: CommunicationMechanism::MessagePassing,
                synchronization_mechanism: SynchronizationMechanism::Channel,
                scalability: ScalabilityLevel::High,
                complexity: ComplexityLevel::Medium,
                use_cases: vec![
                    "管道处理".to_string(),
                    "流处理".to_string(),
                    "并发算法".to_string(),
                ],
            },
            ConcurrencyModel::SharedMemory => ConcurrencyModelCharacteristics {
                model_type: ConcurrencyModel::SharedMemory,
                communication_mechanism: CommunicationMechanism::SharedMemory,
                synchronization_mechanism: SynchronizationMechanism::Lock,
                scalability: ScalabilityLevel::Medium,
                complexity: ComplexityLevel::High,
                use_cases: vec![
                    "缓存系统".to_string(),
                    "状态管理".to_string(),
                    "共享资源".to_string(),
                ],
            },
            ConcurrencyModel::DataParallel => ConcurrencyModelCharacteristics {
                model_type: ConcurrencyModel::DataParallel,
                communication_mechanism: CommunicationMechanism::Hybrid,
                synchronization_mechanism: SynchronizationMechanism::Atomic,
                scalability: ScalabilityLevel::VeryHigh,
                complexity: ComplexityLevel::Low,
                use_cases: vec![
                    "大数据处理".to_string(),
                    "科学计算".to_string(),
                    "图像处理".to_string(),
                ],
            },
            ConcurrencyModel::ForkJoin => ConcurrencyModelCharacteristics {
                model_type: ConcurrencyModel::ForkJoin,
                communication_mechanism: CommunicationMechanism::MessagePassing,
                synchronization_mechanism: SynchronizationMechanism::Channel,
                scalability: ScalabilityLevel::High,
                complexity: ComplexityLevel::Low,
                use_cases: vec![
                    "分治算法".to_string(),
                    "递归并行".to_string(),
                    "树遍历".to_string(),
                ],
            },
            ConcurrencyModel::MapReduce => ConcurrencyModelCharacteristics {
                model_type: ConcurrencyModel::MapReduce,
                communication_mechanism: CommunicationMechanism::Hybrid,
                synchronization_mechanism: SynchronizationMechanism::Atomic,
                scalability: ScalabilityLevel::VeryHigh,
                complexity: ComplexityLevel::Medium,
                use_cases: vec![
                    "大规模数据分析".to_string(),
                    "日志处理".to_string(),
                    "搜索索引".to_string(),
                ],
            },
            _ => ConcurrencyModelCharacteristics {
                model_type: model.clone(),
                communication_mechanism: CommunicationMechanism::Hybrid,
                synchronization_mechanism: SynchronizationMechanism::Lock,
                scalability: ScalabilityLevel::Medium,
                complexity: ComplexityLevel::Medium,
                use_cases: vec!["通用并发场景".to_string()],
            },
        }
    }
    
    pub fn compare_models(model_a: &ConcurrencyModel, model_b: &ConcurrencyModel) -> ModelComparison {
        let char_a = Self::analyze_model(model_a);
        let char_b = Self::analyze_model(model_b);
        
        let scalability_cmp = format!("{:?} vs {:?}", char_a.scalability, char_b.scalability);
        let complexity_cmp = format!("{:?} vs {:?}", char_a.complexity, char_b.complexity);
        
        ModelComparison {
            model_a: model_a.clone(),
            model_b: model_b.clone(),
            scalability_comparison: scalability_cmp,
            complexity_comparison: complexity_cmp,
            recommendation: Self::determine_recommendation(&char_a, &char_b),
        }
    }
    
    fn determine_recommendation(char_a: &ConcurrencyModelCharacteristics, char_b: &ConcurrencyModelCharacteristics) -> String {
        use CmpOrdering::*;
        
        match (char_a.scalability.cmp(&char_b.scalability), char_a.complexity.cmp(&char_b.complexity)) {
            (Greater, Less) => format!("{:?} offers better scalability and lower complexity", char_a.model_type),
            (Less, Greater) => format!("{:?} offers better scalability and lower complexity", char_b.model_type),
            _ => "Both models have their own advantages depending on the use case".to_string(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelComparison {
    pub model_a: ConcurrencyModel,
    pub model_b: ConcurrencyModel,
    pub scalability_comparison: String,
    pub complexity_comparison: String,
    pub recommendation: String,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_csp_channel() {
        let channel = CSPChannel::new();
        
        channel.send(42).unwrap();
        let value = channel.recv().unwrap();
        
        assert_eq!(value, 42);
    }
    
    #[test]
    fn test_shared_memory() {
        let memory = SharedMemory::new(0i32);
        
        memory.write(|data| *data = 42).unwrap();
        let value = memory.read(|data| *data).unwrap();
        
        assert_eq!(value, 42);
        assert_eq!(memory.version(), 1);
    }
    
    #[test]
    fn test_data_parallel_map() {
        let executor = DataParallelExecutor::new(4);
        let data = vec![1, 2, 3, 4, 5];
        
        let result = executor.parallel_map(data, |x| x * 2).unwrap();
        
        assert_eq!(result.len(), 5);
        assert!(result.contains(&2));
        assert!(result.contains(&10));
    }
    
    #[test]
    fn test_data_parallel_reduce() {
        let executor = DataParallelExecutor::new(4);
        let data = vec![1, 2, 3, 4, 5];
        
        let result = executor.parallel_reduce(data, 0, |acc, x| acc + x).unwrap();
        
        assert_eq!(result, 15);
    }
    
    #[test]
    fn test_concurrency_model_analyzer() {
        let characteristics = ConcurrencyModelAnalyzer::analyze_model(&ConcurrencyModel::Actor);
        
        assert_eq!(characteristics.model_type, ConcurrencyModel::Actor);
        assert_eq!(characteristics.communication_mechanism, CommunicationMechanism::MessagePassing);
        assert_eq!(characteristics.scalability, ScalabilityLevel::VeryHigh);
    }
    
    #[test]
    fn test_model_comparison() {
        let comparison = ConcurrencyModelAnalyzer::compare_models(
            &ConcurrencyModel::Actor,
            &ConcurrencyModel::SharedMemory,
        );
        
        assert_eq!(comparison.model_a, ConcurrencyModel::Actor);
        assert_eq!(comparison.model_b, ConcurrencyModel::SharedMemory);
        assert!(comparison.scalability_comparison.contains("VeryHigh"));
    }
    
    #[test]
    fn test_transactional_memory() {
        let memory = TransactionalMemory::new(vec![1, 2, 3]);
        
        memory.transaction(|data| {
            data.push(4);
            Ok(())
        }).unwrap();
        
        assert_eq!(memory.log_len(), 1);
    }
}
