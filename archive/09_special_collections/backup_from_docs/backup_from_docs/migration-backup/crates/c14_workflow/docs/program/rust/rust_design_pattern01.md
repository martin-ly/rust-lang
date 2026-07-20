# Rust 复杂设计模式与架构设计模式全面指南

## 目录

- [Rust 复杂设计模式与架构设计模式全面指南](#rust-复杂设计模式与架构设计模式全面指南)
  - [目录](#目录)
  - [1. 数据流模式](#1-数据流模式)
    - [1.1 数据管道与变换模式](#11-数据管道与变换模式)
    - [1.2 反应式数据流](#12-反应式数据流)
    - [1.3 数据传播与状态同步](#13-数据传播与状态同步)
  - [2. 执行流模式](#2-执行流模式)
    - [2.1 任务调度与执行器模式](#21-任务调度与执行器模式)
    - [2.2 协程与异步执行流](#22-协程与异步执行流)
    - [2.3 工作流引擎与状态机](#23-工作流引擎与状态机)
    - [2.4 Actor 模型实现](#24-actor-模型实现)
  - [3. 控制流模式](#3-控制流模式)
    - [3.1 责任链模式](#31-责任链模式)
    - [3.2 命令模式与撤销/重做](#32-命令模式与撤销重做)
    - [3.3 状态模式与有限状态机](#33-状态模式与有限状态机)
    - [3.4 观察者模式与事件发布/订阅](#34-观察者模式与事件发布订阅)
  - [4. 容错模式](#4-容错模式)
    - [4.1 重试与回退策略](#41-重试与回退策略)
    - [4.2 断路器模式](#42-断路器模式)
    - [4.3 舱壁与隔离模式](#43-舱壁与隔离模式)
    - [4.4 超时与取消模式](#44-超时与取消模式)
    - [4.5 流量控制与限流](#45-流量控制与限流)
  - [5. 一致性模式](#5-一致性模式)
    - [5.1 分布式锁](#51-分布式锁)
    - [5.2 Saga 模式与两阶段提交](#52-saga-模式与两阶段提交)
    - [5.3 最终一致性与事件溯源](#53-最终一致性与事件溯源)
    - [5.4 CQRS 模式](#54-cqrs-模式)
    - [5.5 幂等性与重复请求处理](#55-幂等性与重复请求处理)
  - [6. 综合架构模式](#6-综合架构模式)
    - [6.1 分层架构](#61-分层架构)
    - [6.2 六边形架构（端口与适配器）](#62-六边形架构端口与适配器)
    - [6.3 微服务架构模式](#63-微服务架构模式)
    - [6.4 事件驱动架构](#64-事件驱动架构)
    - [6.5 反应式架构](#65-反应式架构)
  - [7. 总结与最佳实践](#7-总结与最佳实践)
    - [7.1 数据流最佳实践](#71-数据流最佳实践)
    - [7.2 执行流最佳实践](#72-执行流最佳实践)
    - [7.3 控制流最佳实践](#73-控制流最佳实践)
    - [7.4 容错最佳实践](#74-容错最佳实践)
    - [7.5 一致性最佳实践](#75-一致性最佳实践)

## 1. 数据流模式

### 1.1 数据管道与变换模式

```rust
// 数据流水线接口
trait Pipeline<I, O> {
    fn process(&self, input: I) -> Result<O, PipelineError>;
}

// 可组合的处理阶段
trait Stage<I, O> {
    fn execute(&self, input: I) -> Result<O, StageError>;
}

// 串联处理阶段
struct SequentialPipeline<S1, S2>
where
    S1: Stage<S1::Input, S1::Output>,
    S2: Stage<S1::Output, S2::Output>,
{
    first: S1,
    second: S2,
}

impl<S1, S2> Pipeline<S1::Input, S2::Output> for SequentialPipeline<S1, S2>
where
    S1: Stage<S1::Input, S1::Output>,
    S2: Stage<S1::Output, S2::Output>,
{
    fn process(&self, input: S1::Input) -> Result<S2::Output, PipelineError> {
        let intermediate = self.first.execute(input)
            .map_err(|e| PipelineError::StageError(e, "first"))?;
            
        self.second.execute(intermediate)
            .map_err(|e| PipelineError::StageError(e, "second"))
    }
}

// 横切关注点装饰器
struct LoggingStage<S> {
    inner: S,
    logger: Arc<dyn Logger>,
}

impl<I, O, S> Stage<I, O> for LoggingStage<S>
where
    S: Stage<I, O>,
    I: Debug,
    O: Debug,
{
    fn execute(&self, input: I) -> Result<O, StageError> {
        self.logger.debug(&format!("Stage input: {:?}", input));
        let result = self.inner.execute(input);
        match &result {
            Ok(output) => self.logger.debug(&format!("Stage output: {:?}", output)),
            Err(e) => self.logger.error(&format!("Stage error: {:?}", e)),
        }
        result
    }
}

// 数据量化与批处理
struct BatchStage<S, I, O> {
    inner: S,
    batch_size: usize,
    _marker: PhantomData<(I, O)>,
}

impl<S, I, O> Stage<Vec<I>, Vec<O>> for BatchStage<S, I, O>
where
    S: Stage<I, O>,
    I: Clone,
    O: Clone,
{
    fn execute(&self, input: Vec<I>) -> Result<Vec<O>, StageError> {
        let mut results = Vec::with_capacity(input.len());
        
        for chunk in input.chunks(self.batch_size) {
            let batch_results = chunk
                .iter()
                .map(|item| self.inner.execute(item.clone()))
                .collect::<Result<Vec<_>, _>>()?;
                
            results.extend(batch_results);
        }
        
        Ok(results)
    }
}

// 数据流向分支与合并
enum Either<L, R> {
    Left(L),
    Right(R),
}

struct ConditionalPipeline<C, L, R>
where
    C: Fn(&C::Input) -> bool,
    L: Pipeline<C::Input, L::Output>,
    R: Pipeline<C::Input, R::Output>,
{
    condition: C,
    left_pipeline: L,
    right_pipeline: R,
}

impl<C, L, R> Pipeline<C::Input, Either<L::Output, R::Output>> 
    for ConditionalPipeline<C, L, R>
where
    C: Fn(&C::Input) -> bool,
    L: Pipeline<C::Input, L::Output>,
    R: Pipeline<C::Input, R::Output>,
{
    fn process(&self, input: C::Input) -> Result<Either<L::Output, R::Output>, PipelineError> {
        if (self.condition)(&input) {
            self.left_pipeline.process(input).map(Either::Left)
        } else {
            self.right_pipeline.process(input).map(Either::Right)
        }
    }
}
```

### 1.2 反应式数据流

```rust
// 数据流定义
trait DataFlow<T> {
    fn subscribe<O: Observer<T>>(&mut self, observer: O) -> Subscription;
    fn unsubscribe(&mut self, subscription: &Subscription);
}

// 数据观察者
trait Observer<T>: Send + Sync {
    fn on_next(&self, value: T);
    fn on_error(&self, error: DataFlowError);
    fn on_complete(&self);
}

// 数据流操作符
trait Operator<I, O>: Observer<I> + DataFlow<O> {}

// 映射操作符
struct MapOperator<I, O, F> 
where
    F: Fn(I) -> O + Send + Sync,
{
    transform: F,
    observers: RwLock<HashMap<SubscriptionId, Box<dyn Observer<O>>>>,
}

impl<I, O, F> Observer<I> for MapOperator<I, O, F>
where
    F: Fn(I) -> O + Send + Sync,
    I: Clone,
    O: Clone,
{
    fn on_next(&self, value: I) {
        let transformed = (self.transform)(value);
        let observers = self.observers.read().unwrap();
        
        for observer in observers.values() {
            observer.on_next(transformed.clone());
        }
    }
    
    fn on_error(&self, error: DataFlowError) {
        let observers = self.observers.read().unwrap();
        
        for observer in observers.values() {
            observer.on_error(error.clone());
        }
    }
    
    fn on_complete(&self) {
        let observers = self.observers.read().unwrap();
        
        for observer in observers.values() {
            observer.on_complete();
        }
    }
}

impl<I, O, F> DataFlow<O> for MapOperator<I, O, F>
where
    F: Fn(I) -> O + Send + Sync,
    O: Clone,
{
    fn subscribe<Obs: Observer<O>>(&mut self, observer: Obs) -> Subscription {
        let id = SubscriptionId::new();
        let mut observers = self.observers.write().unwrap();
        observers.insert(id, Box::new(observer));
        
        Subscription { id }
    }
    
    fn unsubscribe(&mut self, subscription: &Subscription) {
        let mut observers = self.observers.write().unwrap();
        observers.remove(&subscription.id);
    }
}

impl<I, O, F> Operator<I, O> for MapOperator<I, O, F>
where
    F: Fn(I) -> O + Send + Sync,
    I: Clone,
    O: Clone,
{}

// 背压机制
trait BackpressureStrategy {
    fn handle_backpressure<T>(&self, value: T) -> BackpressureAction<T>;
}

enum BackpressureAction<T> {
    Emit(T),
    Drop,
    Buffer(T),
    Latest(T),
    Error(DataFlowError),
}

struct DropOldestStrategy<T> {
    buffer: RwLock<VecDeque<T>>,
    capacity: usize,
}

impl<T: Clone> BackpressureStrategy for DropOldestStrategy<T> {
    fn handle_backpressure<U>(&self, value: U) -> BackpressureAction<U>
    where
        U: Into<T> + Clone,
    {
        let mut buffer = self.buffer.write().unwrap();
        
        if buffer.len() >= self.capacity {
            // 移除最旧的元素
            buffer.pop_front();
        }
        
        buffer.push_back(value.clone().into());
        BackpressureAction::Emit(value)
    }
}
```

### 1.3 数据传播与状态同步

```rust
// 数据版本控制
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct VersionVector<ID: Hash + Eq> {
    versions: HashMap<ID, u64>,
}

impl<ID: Hash + Eq + Clone> VersionVector<ID> {
    fn new() -> Self {
        Self {
            versions: HashMap::new(),
        }
    }
    
    fn increment(&mut self, id: ID) {
        let version = self.versions.entry(id).or_insert(0);
        *version += 1;
    }
    
    fn merge(&mut self, other: &Self) {
        for (id, &version) in &other.versions {
            let entry = self.versions.entry(id.clone()).or_insert(0);
            *entry = std::cmp::max(*entry, version);
        }
    }
    
    fn dominates(&self, other: &Self) -> bool {
        // 检查是否所有版本都大于或等于其他版本
        for (id, &other_version) in &other.versions {
            match self.versions.get(id) {
                Some(&self_version) if self_version >= other_version => {},
                _ => return false,
            }
        }
        true
    }
    
    fn concurrent_with(&self, other: &Self) -> bool {
        // 检查是否有无法比较的版本
        !self.dominates(other) && !other.dominates(self)
    }
}

// CRDT - 增长集
#[derive(Clone, Debug)]
struct GSet<T: Hash + Eq + Clone> {
    elements: HashSet<T>,
    version: VersionVector<NodeId>,
}

impl<T: Hash + Eq + Clone> GSet<T> {
    fn new(node_id: NodeId) -> Self {
        let mut version = VersionVector::new();
        version.increment(node_id);
        
        Self {
            elements: HashSet::new(),
            version,
        }
    }
    
    fn add(&mut self, node_id: NodeId, element: T) -> bool {
        let inserted = self.elements.insert(element);
        
        if inserted {
            self.version.increment(node_id);
        }
        
        inserted
    }
    
    fn contains(&self, element: &T) -> bool {
        self.elements.contains(element)
    }
    
    fn merge(&mut self, other: &Self) {
        // 合并所有元素
        for element in &other.elements {
            self.elements.insert(element.clone());
        }
        
        // 合并版本向量
        self.version.merge(&other.version);
    }
}

// 状态复制与同步
trait Replicable: Send + Sync {
    type State: Clone + Send + Sync;
    type Delta: Clone + Send + Sync;
    
    fn get_state(&self) -> Self::State;
    fn apply_delta(&mut self, delta: Self::Delta) -> Result<(), ReplicationError>;
    fn compute_delta(&self, since_version: &VersionVector<NodeId>) -> Self::Delta;
    fn version(&self) -> VersionVector<NodeId>;
}

// 状态同步协调器
struct StateReplication<T: Replicable> {
    node_id: NodeId,
    local: Arc<RwLock<T>>,
    peers: HashMap<NodeId, RemotePeer<T>>,
    sync_interval: Duration,
    gossip_factor: f32,
}

impl<T: Replicable + 'static> StateReplication<T> {
    fn new(node_id: NodeId, local: T) -> Self {
        Self {
            node_id,
            local: Arc::new(RwLock::new(local)),
            peers: HashMap::new(),
            sync_interval: Duration::from_secs(30),
            gossip_factor: 0.5, // 默认与一半的节点同步
        }
    }
    
    fn add_peer(&mut self, peer_id: NodeId, peer: RemotePeer<T>) {
        self.peers.insert(peer_id, peer);
    }
    
    fn start_sync(&self) -> JoinHandle<()> {
        // 创建同步任务
        let node_id = self.node_id.clone();
        let local = Arc::clone(&self.local);
        let peers = self.peers.clone();
        let interval = self.sync_interval;
        let gossip_factor = self.gossip_factor;
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(interval);
            
            loop {
                interval.tick().await;
                
                // 选择一部分节点进行同步
                let sync_count = (peers.len() as f32 * gossip_factor).ceil() as usize;
                let selected_peers: Vec<_> = peers.keys()
                    .choose_multiple(&mut rand::thread_rng(), sync_count)
                    .cloned()
                    .collect();
                
                for peer_id in selected_peers {
                    if let Some(peer) = peers.get(&peer_id) {
                        let local_state = {
                            let local_guard = local.read().unwrap();
                            local_guard.get_state()
                        };
                        
                        // 发送状态到对等节点
                        if let Err(e) = peer.send_state(node_id.clone(), local_state).await {
                            log::error!("Failed to sync with peer {}: {:?}", peer_id, e);
                        }
                    }
                }
            }
        })
    }
    
    async fn receive_state(&self, from: NodeId, state: T::State) -> Result<(), ReplicationError> {
        let mut local = self.local.write().unwrap();
        
        // 应用远程状态
        local.apply_delta(state)
    }
}
```

## 2. 执行流模式

### 2.1 任务调度与执行器模式

```rust
// 任务特征
trait Task: Send + 'static {
    type Output: Send + 'static;
    
    fn execute(self) -> Result<Self::Output, TaskError>;
    fn priority(&self) -> TaskPriority;
    fn dependencies(&self) -> Vec<TaskId>;
}

// 执行器接口
trait Executor: Send + Sync {
    fn submit<T: Task>(&self, task: T) -> ExecutionHandle<T::Output>;
    fn shutdown(&self) -> ShutdownHandle;
    fn metrics(&self) -> ExecutorMetrics;
}

// 线程池执行器
struct ThreadPoolExecutor {
    pool: Arc<ThreadPool>,
    queue: Arc<PriorityTaskQueue>,
    metrics: Arc<ExecutorMetrics>,
    shutdown_signal: Arc<AtomicBool>,
}

impl ThreadPoolExecutor {
    fn new(threads: usize) -> Self {
        let queue = Arc::new(PriorityTaskQueue::new());
        let metrics = Arc::new(ExecutorMetrics::default());
        let shutdown_signal = Arc::new(AtomicBool::new(false));
        
        let pool = {
            let queue = Arc::clone(&queue);
            let metrics = Arc::clone(&metrics);
            let shutdown_signal = Arc::clone(&shutdown_signal);
            
            ThreadPool::new(threads, move || {
                let queue = Arc::clone(&queue);
                let metrics = Arc::clone(&metrics);
                let shutdown_signal = Arc::clone(&shutdown_signal);
                
                move || {
                    while !shutdown_signal.load(Ordering::SeqCst) {
                        match queue.pop() {
                            Some(task) => {
                                metrics.increment_active_tasks();
                                let start = Instant::now();
                                
                                let result = task.execute();
                                let duration = start.elapsed();
                                
                                metrics.decrement_active_tasks();
                                metrics.record_execution_time(duration);
                                
                                match result {
                                    Ok(_) => metrics.increment_completed_tasks(),
                                    Err(_) => metrics.increment_failed_tasks(),
                                }
                            },
                            None => {
                                thread::sleep(Duration::from_millis(10));
                            }
                        }
                    }
                }
            })
        };
        
        Self {
            pool: Arc::new(pool),
            queue,
            metrics,
            shutdown_signal,
        }
    }
}

impl Executor for ThreadPoolExecutor {
    fn submit<T: Task>(&self, task: T) -> ExecutionHandle<T::Output> {
        let (sender, receiver) = oneshot::channel();
        
        let metrics = Arc::clone(&self.metrics);
        let wrapped_task = WrappedTask {
            inner: Box::new(move || {
                metrics.increment_active_tasks();
                let start = Instant::now();
                
                let result = task.execute();
                let duration = start.elapsed();
                
                metrics.decrement_active_tasks();
                metrics.record_execution_time(duration);
                
                match &result {
                    Ok(_) => metrics.increment_completed_tasks(),
                    Err(_) => metrics.increment_failed_tasks(),
                }
                
                let _ = sender.send(result);
            }),
            priority: task.priority(),
            dependencies: task.dependencies(),
            id: TaskId::new(),
        };
        
        self.queue.push(wrapped_task);
        
        ExecutionHandle {
            receiver,
            id: wrapped_task.id,
        }
    }
    
    fn shutdown(&self) -> ShutdownHandle {
        self.shutdown_signal.store(true, Ordering::SeqCst);
        ShutdownHandle::new()
    }
    
    fn metrics(&self) -> ExecutorMetrics {
        self.metrics.clone()
    }
}

// 工作窃取执行器
struct WorkStealingExecutor {
    local_queues: Vec<Arc<WorkQueue>>,
    workers: Vec<Worker>,
    metrics: Arc<ExecutorMetrics>,
    shutdown_signal: Arc<AtomicBool>,
}

impl WorkStealingExecutor {
    fn new(threads: usize) -> Self {
        let metrics = Arc::new(ExecutorMetrics::default());
        let shutdown_signal = Arc::new(AtomicBool::new(false));
        
        let local_queues: Vec<_> = (0..threads)
            .map(|_| Arc::new(WorkQueue::new()))
            .collect();
            
        let workers = (0..threads)
            .map(|i| {
                let own_queue = Arc::clone(&local_queues[i]);
                let queues = local_queues.clone();
                let metrics = Arc::clone(&metrics);
                let shutdown_signal = Arc::clone(&shutdown_signal);
                
                Worker::new(i, own_queue, queues, metrics, shutdown_signal)
            })
            .collect();
            
        Self {
            local_queues,
            workers,
            metrics,
            shutdown_signal,
        }
    }
    
    fn start(&mut self) {
        for worker in &mut self.workers {
            worker.start();
        }
    }
}

impl Executor for WorkStealingExecutor {
    fn submit<T: Task>(&self, task: T) -> ExecutionHandle<T::Output> {
        let (sender, receiver) = oneshot::channel();
        
        let wrapped_task = WrappedTask {
            inner: Box::new(move || {
                let result = task.execute();
                let _ = sender.send(result);
            }),
            priority: task.priority(),
            dependencies: task.dependencies(),
            id: TaskId::new(),
        };
        
        // 使用简单的哈希分配任务给不同的工作队列
        let queue_idx = wrapped_task.id.0 as usize % self.local_queues.len();
        self.local_queues[queue_idx].push(wrapped_task.clone());
        
        ExecutionHandle {
            receiver,
            id: wrapped_task.id,
        }
    }
    
    fn shutdown(&self) -> ShutdownHandle {
        self.shutdown_signal.store(true, Ordering::SeqCst);
        ShutdownHandle::new()
    }
    
    fn metrics(&self) -> ExecutorMetrics {
        self.metrics.clone()
    }
}

// 有向无环图 (DAG) 任务执行器
struct DagExecutor<E: Executor> {
    inner: E,
    task_graph: RwLock<Graph<TaskId, ()>>,
    completed_tasks: RwLock<HashSet<TaskId>>,
    waiting_tasks: RwLock<HashMap<TaskId, Box<dyn Task>>>,
}

impl<E: Executor> DagExecutor<E> {
    fn new(executor: E) -> Self {
        Self {
            inner: executor,
            task_graph: RwLock::new(Graph::new()),
            completed_tasks: RwLock::new(HashSet::new()),
            waiting_tasks: RwLock::new(HashMap::new()),
        }
    }
    
    fn submit_dag<T: Task>(&self, tasks: Vec<T>) -> Vec<ExecutionHandle<T::Output>> {
        // TODO: 实现任务 DAG 提交
        vec![]
    }
    
    fn task_completed(&self, task_id: TaskId) {
        // 标记任务已完成
        {
            let mut completed = self.completed_tasks.write().unwrap();
            completed.insert(task_id);
        }
        
        // 查找并提交准备好的任务
        let ready_tasks = {
            let graph = self.task_graph.read().unwrap();
            let completed = self.completed_tasks.read().unwrap();
            let mut waiting = self.waiting_tasks.write().unwrap();
            
            let mut ready = Vec::new();
            
            for (id, task) in waiting.iter() {
                let dependencies = task.dependencies();
                if dependencies.iter().all(|dep| completed.contains(dep)) {
                    ready.push(*id);
                }
            }
            
            // 移除并返回准备好的任务
            ready.into_iter()
                .filter_map(|id| waiting.remove(&id))
                .collect::<Vec<_>>()
        };
        
        // 提交准备好的任务
        for task in ready_tasks {
            self.inner.submit(task);
        }
    }
}
```

### 2.2 协程与异步执行流

```rust
// 异步任务接口
trait AsyncTask: Send + 'static {
    type Output: Send + 'static;
    
    fn execute(self) -> Pin<Box<dyn Future<Output = Result<Self::Output, TaskError>> + Send>>;
    fn priority(&self) -> TaskPriority;
}

// 异步执行器
struct AsyncExecutor {
    runtime: Arc<Runtime>,
    queue: Arc<AsyncQueue>,
    metrics: Arc<ExecutorMetrics>,
}

impl AsyncExecutor {
    fn new(threads: usize) -> Self {
        let runtime = Runtime::builder()
            .worker_threads(threads)
            .enable_all()
            .build()
            .unwrap();
            
        let queue = Arc::new(AsyncQueue::new());
        let metrics = Arc::new(ExecutorMetrics::default());
        
        // 启动任务处理循环
        {
            let queue = Arc::clone(&queue);
            let metrics = Arc::clone(&metrics);
            let rt = Arc::clone(&runtime);
            
            rt.spawn(async move {
                loop {
                    if let Some(task) = queue.pop().await {
                        // 提交任务到运行时
                        let metrics = Arc::clone(&metrics);
                        rt.spawn(async move {
                            metrics.increment_active_tasks();
                            let start = Instant::now();
                            
                            task.execute().await;
                            
                            let duration = start.elapsed();
                            metrics.decrement_active_tasks();
                            metrics.record_execution_time(duration);
                        });
                    } else {
                        // 如果队列为空，等待短暂时间
                        tokio::time::sleep(Duration::from_millis(1)).await;
                    }
                }
            });
        }
        
        Self {
            runtime: Arc::new(runtime),
            queue,
            metrics,
        }
    }
    
    async fn submit<T: AsyncTask>(&self, task: T) -> JoinHandle<Result<T::Output, TaskError>> {
        let (tx, rx) = oneshot::channel();
        
        let metrics = Arc::clone(&self.metrics);
        let rt = Arc::clone(&self.runtime);
        
        // 包装任务以捕获结果
        let wrapped_task = Box::new(async move {
            metrics.increment_active_tasks();
            let start = Instant::now();
            
            let result = task.execute().await;
            
            let duration = start.elapsed();
            metrics.decrement_active_tasks();
            metrics.record_execution_time(duration);
            
            match &result {
                Ok(_) => metrics.increment_completed_tasks(),
                Err(_) => metrics.increment_failed_tasks(),
            }
            
            let _ = tx.send(result);
        });
        
        // 将任务添加到队列
        self.queue.push(wrapped_task).await;
        
        // 返回可用于等待任务完成的句柄
        self.runtime.spawn(async move {
            rx.await.unwrap_or_else(|_| Err(TaskError::Cancelled))
        })
    }
}

// 协作式调度与任务让出
struct CooperativeScheduler {
    tasks: RwLock<VecDeque<CooperativeTask>>,
    current_task: AtomicUsize,
    time_slice: Duration,
}

impl CooperativeScheduler {
    fn new(time_slice: Duration) -> Self {
        Self {
            tasks: RwLock::new(VecDeque::new()),
            current_task: AtomicUsize::new(0),
            time_slice,
        }
    }
    
    fn schedule<F>(&self, future: F) -> CooperativeTaskHandle<F::Output>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        let (tx, rx) = oneshot::channel();
        
        let task = CooperativeTask {
            future: Box::pin(async move {
                let result = future.await;
                let _ = tx.send(result);
            }),
            state: AtomicCell::new(TaskState::Ready),
            last_run: AtomicCell::new(Instant::now()),
        };
        
        let mut tasks = self.tasks.write().unwrap();
        tasks.push_back(task);
        
        CooperativeTaskHandle { receiver: rx }
    }
    
    fn run(&self) {
        while !self.is_empty() {
            let mut tasks = self.tasks.write().unwrap();
            
            if let Some(mut task) = tasks.pop_front() {
                let state = task.state.load();
                
                match state {
                    TaskState::Ready => {
                        task.state.store(TaskState::Running);
                        task.last_run.store(Instant::now());
                        
                        // 执行任务直到完成或让出
                        let waker = self.create_waker_for(&task);
                        let mut cx = Context::from_waker(&waker);
                        
                        match task.future.as_mut().poll(&mut cx) {
                            Poll::Ready(_) => {
                                // 任务完成
                                task.state.store(TaskState::Completed);
                            },
                            Poll::Pending => {
                                // 任务让出或挂起
                                if task.last_run.load().elapsed() >= self.time_slice {
                                    // 时间片用完
                                    task.state.store(TaskState::Ready);
                                    tasks.push_back(task);
                                } else {
                                    // 等待某些条件
                                    task.state.store(TaskState::Waiting);
                                    tasks.push_back(task);
                                }
                            }
                        }
                    },
                    TaskState::Waiting => {
                        // 放回等待中的任务
                        tasks.push_back(task);
                    },
                    _ => {} // 忽略其他状态
                }
            }
        }
    }
    
    fn is_empty(&self) -> bool {
        let tasks = self.tasks.read().unwrap();
        tasks.iter().all(|task| {
            matches!(task.state.load(), TaskState::Completed)
        })
    }
    
    fn create_waker_for(&self, task: &CooperativeTask) -> Waker {
        // 创建一个唤醒器，用于通知调度器任务可以继续
        // 实际实现会更复杂
        task_waker::create_waker(task)
    }
}
```

### 2.3 工作流引擎与状态机

```rust
// 工作流状态机定义
trait Workflow: Send + Sync {
    type Input;
    type Output;
    type Error;
    type Context;
    
    fn start(&self, input: Self::Input, ctx: &Self::Context) -> Result<WorkflowInstanceId, Self::Error>;
    fn step(&self, instance_id: &WorkflowInstanceId, ctx: &Self::Context) -> Result<StepResult, Self::Error>;
    fn status(&self, instance_id: &WorkflowInstanceId) -> Result<WorkflowStatus, Self::Error>;
}

// 工作流步骤
trait WorkflowStep: Send + Sync {
    type Input;
    type Output;
    type Error;
    type Context;
    
    fn execute(&self, input: Self::Input, ctx: &Self::Context) -> Result<StepOutcome<Self::Output>, Self::Error>;
    fn compensate(&self, input: Self::Input, ctx: &Self::Context) -> Result<(), Self::Error>;
}

// 工作流引擎
struct WorkflowEngine<S: StateStore>
# Rust 复杂设计模式与架构设计模式全面指南（续）

## 执行流模式（续）

### 3. 工作流引擎与状态机（续）

```rust
// 工作流引擎实现
struct WorkflowEngine<S: StateStore> {
    state_store: S,
    registry: WorkflowRegistry,
    executor: Arc<dyn Executor>,
    event_emitter: Arc<dyn EventEmitter>,
    scheduler: Arc<WorkflowScheduler>,
}

impl<S: StateStore> WorkflowEngine<S> {
    fn new(
        state_store: S,
        executor: Arc<dyn Executor>,
        event_emitter: Arc<dyn EventEmitter>,
    ) -> Self {
        let scheduler = Arc::new(WorkflowScheduler::new(Arc::clone(&executor)));
        
        Self {
            state_store,
            registry: WorkflowRegistry::new(),
            executor,
            event_emitter,
            scheduler,
        }
    }
    
    fn register_workflow<W: Workflow + 'static>(&mut self, workflow: W) -> Result<(), RegistrationError> {
        self.registry.register(workflow)
    }
    
    async fn start_workflow<I>(&self, workflow_id: &str, input: I) -> Result<WorkflowInstanceId, WorkflowError>
    where
        I: Serialize + DeserializeOwned + Send + 'static,
    {
        // 查找工作流定义
        let workflow = self.registry.get(workflow_id)?;
        
        // 创建工作流上下文
        let context = WorkflowContext {
            engine: self,
            instance_id: WorkflowInstanceId::new(),
            workflow_id: workflow_id.to_string(),
        };
        
        // 序列化输入
        let input_data = serde_json::to_vec(&input)
            .map_err(|e| WorkflowError::SerializationError(e.to_string()))?;
        
        // 创建工作流实例
        let instance = WorkflowInstance {
            id: context.instance_id.clone(),
            workflow_id: workflow_id.to_string(),
            state: WorkflowState::Created,
            input: input_data,
            current_step: None,
            steps_executed: Vec::new(),
            result: None,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        
        // 保存实例状态
        self.state_store.save_instance(&instance).await?;
        
        // 发布工作流创建事件
        self.event_emitter.emit(WorkflowEvent::Created {
            instance_id: instance.id.clone(),
            workflow_id: workflow_id.to_string(),
        }).await?;
        
        // 安排工作流执行
        self.scheduler.schedule(instance.id.clone(), Default::default()).await?;
        
        Ok(instance.id)
    }
    
    async fn execute_step(&self, instance_id: &WorkflowInstanceId) -> Result<(), WorkflowError> {
        // 加载工作流实例
        let mut instance = self.state_store.load_instance(instance_id).await?;
        
        // 验证工作流状态
        if !matches!(instance.state, WorkflowState::Created | WorkflowState::Running) {
            return Err(WorkflowError::InvalidState(format!(
                "Cannot execute step in {:?} state", instance.state
            )));
        }
        
        // 获取工作流定义
        let workflow = self.registry.get(&instance.workflow_id)?;
        
        // 创建工作流上下文
        let context = WorkflowContext {
            engine: self,
            instance_id: instance.id.clone(),
            workflow_id: instance.workflow_id.clone(),
        };
        
        // 确定下一步
        let next_step = match &instance.current_step {
            Some(current) => workflow.next_step(&current.id, &current.result, &context).await?,
            None => workflow.first_step(&instance.input, &context).await?,
        };
        
        match next_step {
            Some(step) => {
                // 更新工作流状态
                instance.state = WorkflowState::Running;
                instance.current_step = Some(StepExecution {
                    id: step.id.clone(),
                    state: StepState::Pending,
                    input: step.input.clone(),
                    result: None,
                    started_at: None,
                    completed_at: None,
                });
                instance.updated_at = chrono::Utc::now();
                
                // 保存实例状态
                self.state_store.save_instance(&instance).await?;
                
                // 发布步骤开始事件
                self.event_emitter.emit(WorkflowEvent::StepStarted {
                    instance_id: instance.id.clone(),
                    step_id: step.id.clone(),
                }).await?;
                
                // 执行步骤
                let step_impl = workflow.get_step(&step.id)?;
                let result = step_impl.execute(step.input, &context).await;
                
                // 处理执行结果
                let mut instance = self.state_store.load_instance(instance_id).await?;
                if let Some(current_step) = &mut instance.current_step {
                    match result {
                        Ok(output) => {
                            // 步骤成功
                            current_step.state = StepState::Completed;
                            current_step.result = Some(output);
                            current_step.completed_at = Some(chrono::Utc::now());
                            
                            // 添加到历史记录
                            instance.steps_executed.push(current_step.clone());
                            
                            // 发布步骤完成事件
                            self.event_emitter.emit(WorkflowEvent::StepCompleted {
                                instance_id: instance.id.clone(),
                                step_id: step.id.clone(),
                            }).await?;
                            
                            // 安排下一步执行
                            self.scheduler.schedule(instance.id.clone(), Default::default()).await?;
                        },
                        Err(error) => {
                            // 步骤失败
                            current_step.state = StepState::Failed;
                            
                            // 处理错误策略
                            match workflow.error_policy(&step.id, &error, &context).await? {
                                ErrorPolicy::Retry { after, max_attempts } => {
                                    if (current_step.attempts.unwrap_or(0) + 1) < max_attempts {
                                        // 重试步骤
                                        current_step.attempts = Some(current_step.attempts.unwrap_or(0) + 1);
                                        current_step.state = StepState::Pending;
                                        
                                        // 安排重试
                                        self.scheduler.schedule_with_delay(
                                            instance.id.clone(), 
                                            after,
                                            Default::default()
                                        ).await?;
                                    } else {
                                        // 达到最大重试次数，失败工作流
                                        instance.state = WorkflowState::Failed {
                                            reason: format!("Step '{}' failed after {} retries: {}", 
                                                step.id, max_attempts, error),
                                            failed_at: chrono::Utc::now(),
                                        };
                                        
                                        // 发布工作流失败事件
                                        self.event_emitter.emit(WorkflowEvent::Failed {
                                            instance_id: instance.id.clone(),
                                            reason: error.to_string(),
                                        }).await?;
                                    }
                                },
                                ErrorPolicy::Compensate => {
                                    // 启动补偿流程
                                    instance.state = WorkflowState::Compensating {
                                        reason: error.to_string(),
                                        started_at: chrono::Utc::now(),
                                    };
                                    
                                    // 保存实例状态
                                    self.state_store.save_instance(&instance).await?;
                                    
                                    // 开始补偿
                                    self.start_compensation(instance_id).await?;
                                    return Ok(());
                                },
                                ErrorPolicy::Fail => {
                                    // 直接失败
                                    instance.state = WorkflowState::Failed {
                                        reason: error.to_string(),
                                        failed_at: chrono::Utc::now(),
                                    };
                                    
                                    // 发布工作流失败事件
                                    self.event_emitter.emit(WorkflowEvent::Failed {
                                        instance_id: instance.id.clone(),
                                        reason: error.to_string(),
                                    }).await?;
                                }
                            }
                        }
                    }
                }
                
                // 保存更新后的实例状态
                instance.updated_at = chrono::Utc::now();
                self.state_store.save_instance(&instance).await?;
            },
            None => {
                // 工作流完成
                instance.state = WorkflowState::Completed {
                    completed_at: chrono::Utc::now(),
                };
                instance.updated_at = chrono::Utc::now();
                
                // 保存实例状态
                self.state_store.save_instance(&instance).await?;
                
                // 发布工作流完成事件
                self.event_emitter.emit(WorkflowEvent::Completed {
                    instance_id: instance.id.clone(),
                }).await?;
            }
        }
        
        Ok(())
    }
    
    async fn start_compensation(&self, instance_id: &WorkflowInstanceId) -> Result<(), WorkflowError> {
        // 加载工作流实例
        let instance = self.state_store.load_instance(instance_id).await?;
        
        // 验证工作流状态
        if !matches!(instance.state, WorkflowState::Compensating { .. }) {
            return Err(WorkflowError::InvalidState(format!(
                "Cannot start compensation in {:?} state", instance.state
            )));
        }
        
        // 获取工作流定义
        let workflow = self.registry.get(&instance.workflow_id)?;
        
        // 创建工作流上下文
        let context = WorkflowContext {
            engine: self,
            instance_id: instance.id.clone(),
            workflow_id: instance.workflow_id.clone(),
        };
        
        // 反向执行补偿步骤
        for step in instance.steps_executed.iter().rev() {
            // 获取步骤实现
            let step_impl = workflow.get_step(&step.id)?;
            
            // 执行补偿逻辑
            let compensation_result = step_impl.compensate(step.input.clone(), &context).await;
            
            if let Err(error) = compensation_result {
                // 补偿失败，记录但继续其他步骤的补偿
                log::error!("Compensation failed for step {}: {}", step.id, error);
                
                // 发布补偿失败事件
                self.event_emitter.emit(WorkflowEvent::CompensationFailed {
                    instance_id: instance.id.clone(),
                    step_id: step.id.clone(),
                    reason: error.to_string(),
                }).await?;
            } else {
                // 发布补偿成功事件
                self.event_emitter.emit(WorkflowEvent::CompensationSucceeded {
                    instance_id: instance.id.clone(),
                    step_id: step.id.clone(),
                }).await?;
            }
        }
        
        // 更新工作流状态为补偿完成
        let mut instance = self.state_store.load_instance(instance_id).await?;
        instance.state = WorkflowState::Compensated {
            completed_at: chrono::Utc::now(),
        };
        instance.updated_at = chrono::Utc::now();
        
        // 保存实例状态
        self.state_store.save_instance(&instance).await?;
        
        // 发布工作流补偿完成事件
        self.event_emitter.emit(WorkflowEvent::CompensationCompleted {
            instance_id: instance.id.clone(),
        }).await?;
        
        Ok(())
    }
}

// 声明式工作流定义
struct DeclarativeWorkflow {
    id: String,
    steps: HashMap<String, Box<dyn WorkflowStep>>,
    transitions: Vec<Transition>,
}

struct Transition {
    from: Option<String>, // None 表示初始状态
    to: String,
    condition: Box<dyn Fn(&StepResult) -> bool + Send + Sync>,
}

impl Workflow for DeclarativeWorkflow {
    type Input = serde_json::Value;
    type Output = serde_json::Value;
    type Error = WorkflowError;
    type Context = WorkflowContext;
    
    async fn first_step(&self, input: &[u8], _ctx: &Self::Context) -> Result<Option<NextStep>, Self::Error> {
        // 查找没有来源的转换（初始转换）
        for transition in &self.transitions {
            if transition.from.is_none() {
                return Ok(Some(NextStep {
                    id: transition.to.clone(),
                    input: input.to_vec(),
                }));
            }
        }
        
        // 没有找到初始步骤
        Err(WorkflowError::Definition("No initial step defined".to_string()))
    }
    
    async fn next_step(&self, current_step: &str, result: &StepResult, _ctx: &Self::Context) -> Result<Option<NextStep>, Self::Error> {
        // 查找匹配当前步骤的转换
        for transition in &self.transitions {
            if let Some(from) = &transition.from {
                if from == current_step && (transition.condition)(result) {
                    let input = match result {
                        StepResult::Success(data) => data.clone(),
                        _ => Vec::new(),
                    };
                    
                    return Ok(Some(NextStep {
                        id: transition.to.clone(),
                        input,
                    }));
                }
            }
        }
        
        // 没有找到匹配的转换，工作流结束
        Ok(None)
    }
    
    fn get_step(&self, step_id: &str) -> Result<&dyn WorkflowStep, Self::Error> {
        self.steps.get(step_id)
            .map(|s| s.as_ref())
            .ok_or_else(|| WorkflowError::StepNotFound(step_id.to_string()))
    }
    
    async fn error_policy(&self, step_id: &str, error: &WorkflowError, _ctx: &Self::Context) -> Result<ErrorPolicy, Self::Error> {
        // 在实际实现中，可能会根据步骤和错误类型返回不同的策略
        Ok(ErrorPolicy::Retry {
            after: std::time::Duration::from_secs(5),
            max_attempts: 3,
        })
    }
}
```

### 2.4 Actor 模型实现

```rust
// Actor 基本接口
trait Actor: Send {
    type Message: Send;
    
    fn handle(&mut self, msg: Self::Message) -> Result<(), ActorError>;
    fn pre_start(&mut self) -> Result<(), ActorError> { Ok(()) }
    fn post_stop(&mut self) -> Result<(), ActorError> { Ok(()) }
}

// Actor 引用，用于向 Actor 发送消息
struct ActorRef<M: Send> {
    sender: mpsc::Sender<M>,
    actor_id: ActorId,
}

impl<M: Send> ActorRef<M> {
    fn send(&self, msg: M) -> Result<(), SendError> {
        self.sender.clone().try_send(msg)
            .map_err(|_| SendError::MailboxFull)
    }
    
    async fn send_async(&self, msg: M) -> Result<(), SendError> {
        self.sender.clone().send(msg).await
            .map_err(|_| SendError::Disconnected)
    }
}

// Actor 系统，管理所有 Actor
struct ActorSystem {
    actors: RwLock<HashMap<ActorId, ActorHandle>>,
    scheduler: Arc<Scheduler>,
    supervision_strategy: SupervisionStrategy,
}

impl ActorSystem {
    fn new() -> Self {
        let scheduler = Arc::new(Scheduler::new());
        
        Self {
            actors: RwLock::new(HashMap::new()),
            scheduler,
            supervision_strategy: SupervisionStrategy::RestartOnFailure,
        }
    }
    
    fn spawn<A: Actor + 'static>(&self, actor: A) -> ActorRef<A::Message> {
        self.spawn_with_options(actor, ActorOptions::default())
    }
    
    fn spawn_with_options<A: Actor + 'static>(&self, 
        mut actor: A, 
        options: ActorOptions
    ) -> ActorRef<A::Message> {
        let actor_id = ActorId::new();
        let (sender, receiver) = mpsc::channel(options.mailbox_size);
        
        // 调用启动钩子
        if let Err(e) = actor.pre_start() {
            log::error!("Actor pre_start failed: {}", e);
        }
        
        // 创建 actor 处理循环
        let scheduler = Arc::clone(&self.scheduler);
        let supervision_strategy = self.supervision_strategy.clone();
        
        let handle = tokio::spawn(async move {
            let mut receiver = receiver;
            
            loop {
                match receiver.recv().await {
                    Some(msg) => {
                        match actor.handle(msg) {
                            Ok(_) => {
                                // 消息处理成功
                            },
                            Err(e) => {
                                // 消息处理失败
                                log::error!("Actor message processing failed: {}", e);
                                
                                match supervision_strategy {
                                    SupervisionStrategy::RestartOnFailure => {
                                        // 重启 actor
                                        if let Err(e) = actor.post_stop() {
                                            log::error!("Actor post_stop failed: {}", e);
                                        }
                                        
                                        if let Err(e) = actor.pre_start() {
                                            log::error!("Actor pre_start failed: {}", e);
                                            break;
                                        }
                                    },
                                    SupervisionStrategy::StopOnFailure => {
                                        // 停止 actor
                                        if let Err(e) = actor.post_stop() {
                                            log::error!("Actor post_stop failed: {}", e);
                                        }
                                        break;
                                    },
                                    SupervisionStrategy::Resume => {
                                        // 继续处理消息
                                    }
                                }
                            }
                        }
                    },
                    None => {
                        // 发送端关闭，停止 actor
                        if let Err(e) = actor.post_stop() {
                            log::error!("Actor post_stop failed: {}", e);
                        }
                        break;
                    }
                }
            }
        });
        
        // 注册 actor
        let actor_handle = ActorHandle {
            handle,
            options,
        };
        
        let mut actors = self.actors.write().unwrap();
        actors.insert(actor_id.clone(), actor_handle);
        
        ActorRef {
            sender,
            actor_id,
        }
    }
    
    fn stop(&self, actor_ref: &ActorRef<impl Send>) -> Result<(), ActorError> {
        let mut actors = self.actors.write().unwrap();
        
        if let Some(handle) = actors.remove(&actor_ref.actor_id) {
            handle.handle.abort();
            Ok(())
        } else {
            Err(ActorError::NotFound)
        }
    }
}

// 有状态 Actor 示例
struct StatefulActor<S> {
    state: S,
    behavior: Box<dyn Fn(&mut S, ActorMessage) -> Result<(), ActorError> + Send>,
}

enum ActorMessage {
    GetState { reply_to: mpsc::Sender<State> },
    UpdateState { new_state: State },
    Stop,
}

impl<S: Send + 'static> Actor for StatefulActor<S> {
    type Message = ActorMessage;
    
    fn handle(&mut self, msg: Self::Message) -> Result<(), ActorError> {
        (self.behavior)(&mut self.state, msg)
    }
}

// Actor 监督与错误处理
#[derive(Clone)]
enum SupervisionStrategy {
    RestartOnFailure,
    StopOnFailure,
    Resume,
}

// 实现 Actor 监督者
struct Supervisor {
    children: HashMap<ActorId, ChildSpec>,
    strategy: SupervisionStrategy,
}

struct ChildSpec {
    actor_ref: ActorRef<Box<dyn Any + Send>>,
    restart_policy: RestartPolicy,
    max_restarts: usize,
    restart_count: usize,
}

enum RestartPolicy {
    Always,
    OnFailure,
    Never,
}

impl Actor for Supervisor {
    type Message = SupervisorMessage;
    
    fn handle(&mut self, msg: Self::Message) -> Result<(), ActorError> {
        match msg {
            SupervisorMessage::ChildTerminated { actor_id, reason } => {
                if let Some(child) = self.children.get_mut(&actor_id) {
                    match (reason, child.restart_policy) {
                        (TerminationReason::Normal, _) => {
                            // 正常终止，不需要重启
                            self.children.remove(&actor_id);
                        },
                        (TerminationReason::Failure(_), RestartPolicy::Never) => {
                            // 失败但策略是不重启
                            self.children.remove(&actor_id);
                        },
                        (TerminationReason::Failure(_), RestartPolicy::OnFailure) |
                        (_, RestartPolicy::Always) => {
                            // 需要重启
                            if child.restart_count < child.max_restarts {
                                child.restart_count += 1;
                                // 在实际实现中会重新创建并启动 Actor
                            } else {
                                // 达到最大重启次数
                                self.children.remove(&actor_id);
                            }
                        }
                    }
                }
                Ok(())
            },
            SupervisorMessage::AddChild { spec } => {
                self.children.insert(spec.actor_ref.actor_id.clone(), spec);
                Ok(())
            }
        }
    }
}

enum SupervisorMessage {
    ChildTerminated { actor_id: ActorId, reason: TerminationReason },
    AddChild { spec: ChildSpec },
}

enum TerminationReason {
    Normal,
    Failure(Box<dyn std::error::Error + Send>),
}
```

## 3. 控制流模式

### 3.1 责任链模式

```rust
// 处理器接口
trait Handler<T, R> {
    fn handle(&self, input: T) -> HandlerResult<T, R>;
}

// 处理结果
enum HandlerResult<T, R> {
    Done(R),
    Continue(T),
}

// 责任链
struct Chain<T, R> {
    handlers: Vec<Box<dyn Handler<T, R>>>,
}

impl<T, R> Chain<T, R> {
    fn new() -> Self {
        Self {
            handlers: Vec::new(),
        }
    }
    
    fn add_handler<H: Handler<T, R> + 'static>(&mut self, handler: H) -> &mut Self {
        self.handlers.push(Box::new(handler));
        self
    }
    
    fn execute(&self, input: T) -> Option<R> {
        let mut current = input;
        
        for handler in &self.handlers {
            match handler.handle(current) {
                HandlerResult::Done(result) => return Some(result),
                HandlerResult::Continue(next) => current = next,
            }
        }
        
        None
    }
}

// 中间件风格的处理器
trait Middleware<S: Service> {
    type Request;
    type Response;
    type Error;
    
    fn call(&self, 
        request: Self::Request, 
        service: &S
    ) -> impl Future<Output = Result<Self::Response, Self::Error>>;
}

// 服务定义
trait Service {
    type Request;
    type Response;
    type Error;
    type Future: Future<Output = Result<Self::Response, Self::Error>>;
    
    fn call(&self, req: Self::Request) -> Self::Future;
}

// 中间件链
struct MiddlewareChain<S, M> {
    service: S,
    middleware: Vec<M>,
}

impl<S, M> MiddlewareChain<S, M> {
    fn new(service: S) -> Self {
        Self {
            service,
            middleware: Vec::new(),
        }
    }
    
    fn add_middleware(&mut self, middleware: M) -> &mut Self {
        self.middleware.push(middleware);
        self
    }
}

impl<S, M, Req, Res, Err> Service for MiddlewareChain<S, M>
where
    S: Service<Request = Req, Response = Res, Error = Err>,
    M: Middleware<S, Request = Req, Response = Res, Error = Err>,
    Req: Clone,
{
    type Request = Req;
    type Response = Res;
    type Error = Err;
    type Future = Pin<Box<dyn Future<Output = Result<Res, Err>>>>;
    
    fn call(&self, req: Self::Request) -> Self::Future {
        // 在真实实现中会通过嵌套调用来构建中间件链
        Box::pin(self.service.call(req))
    }
}
```

### 3.2 命令模式与撤销/重做

```rust
// 命令接口
trait Command {
    type Context;
    type Error;
    
    fn execute(&self, ctx: &mut Self::Context) -> Result<(), Self::Error>;
    fn undo(&self, ctx: &mut Self::Context) -> Result<(), Self::Error>;
}

// 命令管理器
struct CommandManager<Ctx> {
    context: Ctx,
    history: Vec<Box<dyn Command<Context = Ctx>>>,
    redos: Vec<Box<dyn Command<Context = Ctx>>>,
}

impl<Ctx> CommandManager<Ctx> {
    fn new(context: Ctx) -> Self {
        Self {
            context,
            history: Vec::new(),
            redos: Vec::new(),
        }
    }
    
    fn execute<C: Command<Context = Ctx> + 'static>(&mut self, command: C) -> Result<(), C::Error> {
        // 执行命令
        command.execute(&mut self.context)?;
        
        // 添加到历史
        self.history.push(Box::new(command));
        
        // 清除重做堆栈
        self.redos.clear();
        
        Ok(())
    }
    
    fn undo<E>(&mut self) -> Result<(), E>
    where
        E: From<<dyn Command<Context = Ctx>>::Error>,
    {
        if let Some(command) = self.history.pop() {
            // 撤销命令
            command.undo(&mut self.context)
                .map_err(|e| E::from(e))?;
            
            // 添加到重做堆栈
            self.redos.push(command);
            
            Ok(())
        } else {
            // 没有可撤销的命令
            Ok(())
        }
    }
    
    fn redo<E>(&mut self) -> Result<(), E>
    where
        E: From<<dyn Command<Context = Ctx>>::Error>,
    {
        if let Some(command) = self.redos.pop() {
            // 重新执行命令
            command.execute(&mut self.context)
                .map_err(|e| E::from(e))?;
            
            // 添加回历史
            self.history.push(command);
            
            Ok(())
        } else {
            // 没有可重做的命令
            Ok(())
        }
    }
}

// 复合命令
struct CompositeCommand<Ctx> {
    commands: Vec<Box<dyn Command<Context = Ctx>>>,
}

impl<Ctx> CompositeCommand<Ctx> {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
        }
    }
    
    fn add_command<C: Command<Context = Ctx> + 'static>(&mut self, command: C) -> &mut Self {
        self.commands.push(Box::new(command));
        self
    }
}

impl<Ctx> Command for CompositeCommand<Ctx>
where
    Ctx: 'static,
{
    type Context = Ctx;
    type Error = Box<dyn std::error::Error + Send + Sync>;
    
    fn execute(&self, ctx: &mut Self::Context) -> Result<(), Self::Error> {
        for command in &self.commands {
            command.execute(ctx)
                .map_err(|e| Box::new(e) as Box<dyn std::error::Error + Send + Sync>)?;
        }
        Ok(())
    }
    
    fn undo(&self, ctx: &mut Self::Context) -> Result<(), Self::Error> {
        
# Rust 复杂设计模式与架构设计模式全面指南（续）

## 控制流模式（续）

### 2. 命令模式与撤销/重做（续）

```rust
    fn undo(&self, ctx: &mut Self::Context) -> Result<(), Self::Error> {
        // 反向撤销命令
        for command in self.commands.iter().rev() {
            command.undo(ctx)
                .map_err(|e| Box::new(e) as Box<dyn std::error::Error + Send + Sync>)?;
        }
        Ok(())
    }
}

// 事务性命令
struct TransactionalCommand<Ctx> {
    inner: Box<dyn Command<Context = Ctx>>,
    snapshot: Option<Ctx>,
}

impl<Ctx: Clone> TransactionalCommand<Ctx> {
    fn new<C: Command<Context = Ctx> + 'static>(command: C) -> Self {
        Self {
            inner: Box::new(command),
            snapshot: None,
        }
    }
}

impl<Ctx: Clone> Command for TransactionalCommand<Ctx> {
    type Context = Ctx;
    type Error = Box<dyn std::error::Error + Send + Sync>;
    
    fn execute(&self, ctx: &mut Self::Context) -> Result<(), Self::Error> {
        // 创建状态快照
        let mut snapshot = ctx.clone();
        
        // 执行内部命令
        match self.inner.execute(&mut snapshot) {
            Ok(_) => {
                // 命令成功执行，将快照状态应用到上下文
                *ctx = snapshot;
                Ok(())
            },
            Err(e) => {
                // 命令执行失败，保留原状态
                Err(Box::new(e) as Box<dyn std::error::Error + Send + Sync>)
            }
        }
    }
    
    fn undo(&self, ctx: &mut Self::Context) -> Result<(), Self::Error> {
        if let Some(ref snapshot) = self.snapshot {
            // 恢复到之前的快照
            *ctx = snapshot.clone();
            Ok(())
        } else {
            Err(Box::new(CommandError::NoSnapshot) as Box<dyn std::error::Error + Send + Sync>)
        }
    }
}
```

### 3.3 状态模式与有限状态机

```rust
// 状态接口
trait State<C, E> {
    fn enter(&self, context: &mut C) -> Result<(), E>;
    fn exit(&self, context: &mut C) -> Result<(), E>;
    fn handle_event(&self, context: &mut C, event: &Event) -> Result<Option<Box<dyn State<C, E>>>, E>;
}

// 有限状态机
struct StateMachine<C, E> {
    context: C,
    current_state: Box<dyn State<C, E>>,
    state_history: Vec<String>,
}

impl<C, E: std::error::Error> StateMachine<C, E> {
    fn new<S: State<C, E> + 'static>(context: C, initial_state: S) -> Result<Self, E> {
        let mut fsm = Self {
            context,
            current_state: Box::new(initial_state),
            state_history: Vec::new(),
        };
        
        // 进入初始状态
        fsm.current_state.enter(&mut fsm.context)?;
        
        // 记录状态历史
        fsm.state_history.push(std::any::type_name::<S>().to_string());
        
        Ok(fsm)
    }
    
    fn handle_event(&mut self, event: Event) -> Result<(), E> {
        // 处理事件，可能会触发状态转换
        if let Some(new_state) = self.current_state.handle_event(&mut self.context, &event)? {
            // 退出当前状态
            self.current_state.exit(&mut self.context)?;
            
            // 保存状态类型名称
            let type_name = std::any::type_name::<dyn State<C, E>>().to_string();
            self.state_history.push(type_name);
            
            // 进入新状态
            new_state.enter(&mut self.context)?;
            
            // 更新当前状态
            self.current_state = new_state;
        }
        
        Ok(())
    }
    
    fn state_history(&self) -> &[String] {
        &self.state_history
    }
}

// 层次化状态机
trait HierarchicalState<C, E>: State<C, E> {
    fn parent_state(&self) -> Option<Box<dyn HierarchicalState<C, E>>>;
}

struct HierarchicalStateMachine<C, E> {
    context: C,
    current_state: Box<dyn HierarchicalState<C, E>>,
}

impl<C, E: std::error::Error> HierarchicalStateMachine<C, E> {
    fn new<S: HierarchicalState<C, E> + 'static>(context: C, initial_state: S) -> Result<Self, E> {
        let mut hsm = Self {
            context,
            current_state: Box::new(initial_state),
        };
        
        // 进入初始状态
        hsm.current_state.enter(&mut hsm.context)?;
        
        Ok(hsm)
    }
    
    fn handle_event(&mut self, event: &Event) -> Result<(), E> {
        // 尝试让当前状态处理事件
        let mut state = &self.current_state;
        let mut state_chain = Vec::new();
        
        // 构建状态层次链，从当前状态到根状态
        while let Some(parent) = state.parent_state() {
            state_chain.push(parent);
            state = state_chain.last().unwrap();
        }
        
        // 首先让当前状态处理事件
        match self.current_state.handle_event(&mut self.context, event)? {
            Some(new_state) => {
                // 状态转换
                self.current_state.exit(&mut self.context)?;
                new_state.enter(&mut self.context)?;
                self.current_state = new_state;
                return Ok(());
            },
            None => {
                // 当前状态未处理事件，尝试父状态
                for parent_state in state_chain {
                    if let Some(new_state) = parent_state.handle_event(&mut self.context, event)? {
                        // 父状态处理了事件并触发转换
                        self.current_state.exit(&mut self.context)?;
                        new_state.enter(&mut self.context)?;
                        self.current_state = new_state;
                        return Ok(());
                    }
                }
            }
        }
        
        // 没有状态处理此事件
        Ok(())
    }
}

// 有状态对象接口
trait StatefulObject<E> {
    type State;
    
    fn current_state(&self) -> &Self::State;
    fn transition_to(&mut self, new_state: Self::State) -> Result<(), E>;
}

// 状态转换守卫
trait TransitionGuard<C, E> {
    fn can_transition(&self, context: &C, from: &str, to: &str) -> Result<bool, E>;
}

// 状态转换器
struct StateTransitioner<C, E, G: TransitionGuard<C, E>> {
    context: C,
    guard: G,
}

impl<C, E, G: TransitionGuard<C, E>> StateTransitioner<C, E, G> {
    fn new(context: C, guard: G) -> Self {
        Self { context, guard }
    }
    
    fn transition<S: StatePattern<C, E>>(&mut self, from_state: &S, to_state: S) -> Result<(), E> {
        // 获取状态名称
        let from = from_state.state_name();
        let to = to_state.state_name();
        
        // 检查转换是否允许
        if self.guard.can_transition(&self.context, from, to)? {
            // 退出当前状态
            from_state.exit(&mut self.context)?;
            
            // 进入新状态
            to_state.enter(&mut self.context)?;
            
            // 更新对象状态
            if let Some(obj) = self.context.as_stateful_object() {
                obj.transition_to(to_state.into_state())?;
            }
            
            Ok(())
        } else {
            Err(StateError::TransitionForbidden(from.to_string(), to.to_string()).into())
        }
    }
}

// 状态模式特征
trait StatePattern<C, E> {
    fn state_name(&self) -> &str;
    fn enter(&self, context: &mut C) -> Result<(), E>;
    fn exit(&self, context: &mut C) -> Result<(), E>;
    fn into_state(self) -> Box<dyn Any>;
}
```

### 3.4 观察者模式与事件发布/订阅

```rust
// 观察者接口
trait Observer<E> {
    fn notify(&self, event: &E);
}

// 被观察者接口
trait Observable<E> {
    fn add_observer(&mut self, observer: Box<dyn Observer<E>>);
    fn remove_observer(&mut self, id: ObserverId);
    fn notify_observers(&self, event: &E);
}

// 基础可观察实现
struct BaseObservable<E> {
    observers: HashMap<ObserverId, Box<dyn Observer<E>>>,
}

impl<E> BaseObservable<E> {
    fn new() -> Self {
        Self {
            observers: HashMap::new(),
        }
    }
}

impl<E> Observable<E> for BaseObservable<E> {
    fn add_observer(&mut self, observer: Box<dyn Observer<E>>) {
        let id = ObserverId::new();
        self.observers.insert(id, observer);
    }
    
    fn remove_observer(&mut self, id: ObserverId) {
        self.observers.remove(&id);
    }
    
    fn notify_observers(&self, event: &E) {
        for observer in self.observers.values() {
            observer.notify(event);
        }
    }
}

// 事件总线
struct EventBus<E> {
    subscribers: RwLock<HashMap<TypeId, Vec<Box<dyn Fn(&E) + Send + Sync>>>>,
}

impl<E: 'static> EventBus<E> {
    fn new() -> Self {
        Self {
            subscribers: RwLock::new(HashMap::new()),
        }
    }
    
    fn subscribe<T: 'static>(&self, callback: impl Fn(&T) + Send + Sync + 'static) -> SubscriptionToken {
        let type_id = TypeId::of::<T>();
        let token = SubscriptionToken::new();
        
        let wrapped = Box::new(move |event: &E| {
            if let Some(typed_event) = event.downcast_ref::<T>() {
                callback(typed_event);
            }
        });
        
        let mut subscribers = self.subscribers.write().unwrap();
        subscribers.entry(type_id).or_insert_with(Vec::new).push(wrapped);
        
        token
    }
    
    fn unsubscribe(&self, token: SubscriptionToken) {
        // 在实际实现中，需要跟踪订阅令牌和回调之间的关系
    }
    
    fn publish<T: 'static>(&self, event: T) {
        let type_id = TypeId::of::<T>();
        let subscribers = self.subscribers.read().unwrap();
        
        if let Some(callbacks) = subscribers.get(&type_id) {
            let boxed_event = Box::new(event) as Box<dyn Any>;
            for callback in callbacks {
                callback(&boxed_event);
            }
        }
    }
}

// 异步事件总线
struct AsyncEventBus<E: Send> {
    subscribers: RwLock<HashMap<TypeId, Vec<Box<dyn Fn(&E) -> Pin<Box<dyn Future<Output = ()> + Send>> + Send + Sync>>>>,
    executor: Arc<Runtime>,
}

impl<E: Send + 'static> AsyncEventBus<E> {
    fn new(executor: Arc<Runtime>) -> Self {
        Self {
            subscribers: RwLock::new(HashMap::new()),
            executor,
        }
    }
    
    fn subscribe<T: 'static, F, Fut>(&self, callback: F) -> SubscriptionToken
    where
        F: Fn(&T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = ()> + Send + 'static,
        T: Send,
    {
        let type_id = TypeId::of::<T>();
        let token = SubscriptionToken::new();
        
        let wrapped = Box::new(move |event: &E| {
            if let Some(typed_event) = event.downcast_ref::<T>() {
                let fut = callback(typed_event);
                Box::pin(fut) as Pin<Box<dyn Future<Output = ()> + Send>>
            } else {
                Box::pin(async {}) as Pin<Box<dyn Future<Output = ()> + Send>>
            }
        });
        
        let mut subscribers = self.subscribers.write().unwrap();
        subscribers.entry(type_id).or_insert_with(Vec::new).push(wrapped);
        
        token
    }
    
    fn publish<T: 'static + Send>(&self, event: T) {
        let type_id = TypeId::of::<T>();
        let subscribers = self.subscribers.read().unwrap();
        
        if let Some(callbacks) = subscribers.get(&type_id) {
            let boxed_event = Box::new(event) as Box<dyn Any>;
            
            for callback in callbacks {
                let future = callback(&boxed_event);
                self.executor.spawn(future);
            }
        }
    }
}

// 分布式事件总线
struct DistributedEventBus<E: Send> {
    local_bus: AsyncEventBus<E>,
    remote_nodes: RwLock<HashMap<NodeId, RemoteNode>>,
    serializer: Box<dyn EventSerializer<E>>,
}

impl<E: Send + 'static> DistributedEventBus<E> {
    fn new(executor: Arc<Runtime>, serializer: Box<dyn EventSerializer<E>>) -> Self {
        Self {
            local_bus: AsyncEventBus::new(executor),
            remote_nodes: RwLock::new(HashMap::new()),
            serializer,
        }
    }
    
    fn add_node(&self, node: RemoteNode) {
        let mut nodes = self.remote_nodes.write().unwrap();
        nodes.insert(node.id.clone(), node);
    }
    
    fn remove_node(&self, node_id: &NodeId) {
        let mut nodes = self.remote_nodes.write().unwrap();
        nodes.remove(node_id);
    }
    
    async fn publish<T: 'static + Send>(&self, event: T, scope: EventScope) -> Result<(), EventBusError> {
        // 发布到本地总线
        self.local_bus.publish(event);
        
        // 如果需要，发布到远程节点
        if matches!(scope, EventScope::Global | EventScope::Remote) {
            let serialized = self.serializer.serialize(Box::new(event))?;
            
            let nodes = self.remote_nodes.read().unwrap();
            for node in nodes.values() {
                if let Err(e) = node.send_event(serialized.clone()).await {
                    log::error!("Failed to send event to node {}: {}", node.id, e);
                }
            }
        }
        
        Ok(())
    }
    
    async fn handle_remote_event(&self, serialized: Vec<u8>) -> Result<(), EventBusError> {
        // 反序列化事件
        let event = self.serializer.deserialize(serialized)?;
        
        // 发布到本地总线
        self.local_bus.publish(event);
        
        Ok(())
    }
}
```

## 4. 容错模式

### 4.1 重试与回退策略

```rust
// 重试策略接口
trait RetryStrategy {
    fn should_retry(&self, attempt: u32, error: &dyn std::error::Error) -> bool;
    fn next_delay(&self, attempt: u32) -> Duration;
}

// 固定间隔重试
struct FixedIntervalRetry {
    max_attempts: u32,
    delay: Duration,
}

impl FixedIntervalRetry {
    fn new(max_attempts: u32, delay: Duration) -> Self {
        Self { max_attempts, delay }
    }
}

impl RetryStrategy for FixedIntervalRetry {
    fn should_retry(&self, attempt: u32, _: &dyn std::error::Error) -> bool {
        attempt < self.max_attempts
    }
    
    fn next_delay(&self, _: u32) -> Duration {
        self.delay
    }
}

// 指数退避重试
struct ExponentialBackoffRetry {
    max_attempts: u32,
    initial_delay: Duration,
    max_delay: Duration,
    factor: f64,
    jitter: bool,
}

impl ExponentialBackoffRetry {
    fn new(max_attempts: u32, initial_delay: Duration, max_delay: Duration, factor: f64) -> Self {
        Self {
            max_attempts,
            initial_delay,
            max_delay,
            factor,
            jitter: false,
        }
    }
    
    fn with_jitter(mut self) -> Self {
        self.jitter = true;
        self
    }
}

impl RetryStrategy for ExponentialBackoffRetry {
    fn should_retry(&self, attempt: u32, _: &dyn std::error::Error) -> bool {
        attempt < self.max_attempts
    }
    
    fn next_delay(&self, attempt: u32) -> Duration {
        let exp = self.factor.powi(attempt as i32);
        let delay = self.initial_delay.as_millis() as f64 * exp;
        let delay = delay.min(self.max_delay.as_millis() as f64) as u64;
        
        if self.jitter {
            // 添加随机抖动
            let jitter = rand::random::<f64>() * 0.3;
            let delay = delay as f64 * (1.0 - jitter);
            Duration::from_millis(delay as u64)
        } else {
            Duration::from_millis(delay)
        }
    }
}

// 重试执行器
struct Retry;

impl Retry {
    async fn run<F, Fut, T, E>(
        f: F,
        strategy: &dyn RetryStrategy,
    ) -> Result<T, E>
    where
        F: Fn() -> Fut,
        Fut: Future<Output = Result<T, E>>,
        E: std::error::Error,
    {
        let mut attempt = 0;
        
        loop {
            match f().await {
                Ok(value) => return Ok(value),
                Err(error) => {
                    attempt += 1;
                    
                    if strategy.should_retry(attempt, &error) {
                        let delay = strategy.next_delay(attempt);
                        tokio::time::sleep(delay).await;
                    } else {
                        return Err(error);
                    }
                }
            }
        }
    }
    
    async fn with_fallback<F, FB, FutF, FutFB, T, E>(
        f: F,
        fallback: FB,
    ) -> Result<T, E>
    where
        F: Fn() -> FutF,
        FutF: Future<Output = Result<T, E>>,
        FB: Fn(E) -> FutFB,
        FutFB: Future<Output = Result<T, E>>,
    {
        match f().await {
            Ok(value) => Ok(value),
            Err(error) => fallback(error).await,
        }
    }
}
```

### 4.2 断路器模式

```rust
// 断路器状态
#[derive(Clone, Copy, PartialEq, Debug)]
enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

// 断路器配置
struct CircuitBreakerConfig {
    failure_threshold: u32,
    reset_timeout: Duration,
    half_open_requests: u32,
}

// 断路器
struct CircuitBreaker {
    state: AtomicCell<CircuitState>,
    failures: AtomicU32,
    successes: AtomicU32,
    last_failure: AtomicCell<Instant>,
    config: CircuitBreakerConfig,
}

impl CircuitBreaker {
    fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: AtomicCell::new(CircuitState::Closed),
            failures: AtomicU32::new(0),
            successes: AtomicU32::new(0),
            last_failure: AtomicCell::new(Instant::now()),
            config,
        }
    }
    
    fn allow_request(&self) -> bool {
        match self.state.load() {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查是否应该进入半开状态
                let elapsed = self.last_failure.load().elapsed();
                if elapsed >= self.config.reset_timeout {
                    // 转换到半开状态
                    self.state.store(CircuitState::HalfOpen);
                    self.successes.store(0, Ordering::SeqCst);
                    self.failures.store(0, Ordering::SeqCst);
                    true
                } else {
                    false
                }
            },
            CircuitState::HalfOpen => {
                // 允许有限数量的请求通过
                let current = self.successes.load(Ordering::SeqCst) + self.failures.load(Ordering::SeqCst);
                current < self.config.half_open_requests
            }
        }
    }
    
    fn on_success(&self) {
        match self.state.load() {
            CircuitState::Closed => {
                // 重置失败计数
                self.failures.store(0, Ordering::SeqCst);
            },
            CircuitState::HalfOpen => {
                // 增加成功计数
                let successes = self.successes.fetch_add(1, Ordering::SeqCst) + 1;
                
                // 检查是否应该关闭断路器
                if successes >= self.config.half_open_requests {
                    self.state.store(CircuitState::Closed);
                    self.successes.store(0, Ordering::SeqCst);
                    self.failures.store(0, Ordering::SeqCst);
                }
            },
            CircuitState::Open => {
                // 不应该在断开状态收到成功回调
            }
        }
    }
    
    fn on_failure(&self) {
        match self.state.load() {
            CircuitState::Closed => {
                // 增加失败计数
                let failures = self.failures.fetch_add(1, Ordering::SeqCst) + 1;
                self.last_failure.store(Instant::now());
                
                // 检查是否应该打开断路器
                if failures >= self.config.failure_threshold {
                    self.state.store(CircuitState::Open);
                }
            },
            CircuitState::HalfOpen => {
                // 任何失败都应该重新打开断路器
                self.state.store(CircuitState::Open);
                self.last_failure.store(Instant::now());
                self.failures.store(0, Ordering::SeqCst);
                self.successes.store(0, Ordering::SeqCst);
            },
            CircuitState::Open => {
                // 更新最后失败时间
                self.last_failure.store(Instant::now());
            }
        }
    }
    
    fn current_state(&self) -> CircuitState {
        self.state.load()
    }
}

// 断路器守护函数
async fn with_circuit_breaker<F, Fut, T, E>(
    circuit_breaker: &CircuitBreaker,
    f: F,
) -> Result<T, CircuitBreakerError<E>>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: std::error::Error,
{
    if !circuit_breaker.allow_request() {
        return Err(CircuitBreakerError::CircuitOpen);
    }
    
    match f().await {
        Ok(value) => {
            circuit_breaker.on_success();
            Ok(value)
        },
        Err(error) => {
            circuit_breaker.on_failure();
            Err(CircuitBreakerError::OperationFailed(error))
        }
    }
}
```

### 4.3 舱壁与隔离模式

```rust
// 舱壁配置
struct BulkheadConfig {
    max_concurrent_calls: u32,
    max_queue_size: u32,
}

// 舱壁实现
struct Bulkhead {
    permits: Semaphore,
    queue: mpsc::Sender<()>,
    config: BulkheadConfig,
}

impl Bulkhead {
    fn new(config: BulkheadConfig) -> Self {
        let (queue_tx, _) = mpsc::channel(config.max_queue_size as usize);
        
        Self {
            permits: Semaphore::new(config.max_concurrent_calls as usize),
            queue: queue_tx,
            config,
        }
    }
    
    async fn acquire(&self) -> Result<BulkheadPermit<'_>, BulkheadError> {
        // 尝试将请求放入队列
        if self.queue.try_send(()).is_err() {
            return Err(BulkheadError::QueueFull);
        }
        
        // 尝试获取许可
        match self.permits.acquire().await {
            Ok(permit) => Ok(BulkheadPermit {
                _permit: permit,
                queue: self.queue.clone(),
            }),
            Err(_) => Err(BulkheadError::Rejected),
        }
    }
    
    fn metrics(&self) -> BulkheadMetrics {
        BulkheadMetrics {
            available_permits: self.permits.available_permits() as u32,
            max_permits: self.config.max_concurrent_calls,
        }
    }
}

// 舱壁许可
struct BulkheadPermit<'a> {
    _permit: SemaphorePermit<'a>,
    queue: mpsc::Sender<()>,
}

impl<'a> Drop for BulkheadPermit<'a> {
    fn drop(&mut self) {
        // 从队列中移除请求
        let _ = self.queue.try_send(());
    }
}

// 使用舱壁包装操作
async fn with_bulkhead<F, Fut, T, E>(
    bulkhead: &Bulkhead,
    f: F,
) -> Result<T, BulkheadError>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: Into<BulkheadError>,
{
    // 获取舱壁许可
    let _permit = bulkhead.acquire().await?;
    
    // 执行操作
    f().await.map_err(|e| e.into())
}

// 线程隔离模式
struct ThreadIsolation {
    thread_pool: ThreadPool,
    max_queue_size: usize,
}

impl ThreadIsolation {
    fn new(thread_count: usize, max_queue_size: usize) -> Self {
        let thread_pool = ThreadPool::builder()
            .pool_size(thread_count)
            .create()
            .expect("Failed to create thread pool");
            
        Self {
            thread_pool,
            max_queue_size,
        }
    }
    
    fn execute<F, T>(&self, f: F) -> Result<JoinHandle<T>, IsolationError>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        // 检查队列是否已满
        if self.thread_pool.queued_count() >= self.max_queue_size {
            return Err(IsolationError::QueueFull);
        }
        
        // 提交任务到独立线程池
        let (tx, rx) = std::sync::mpsc::channel();
        
        self.thread_pool.execute(move || {
            let result = f();
            let _ = tx.send(result);
        });
        
        Ok(JoinHandle::new(rx))
    }
}
```

### 4.4 超时与取消模式

```rust
// 带超时的操作执行
async fn with_timeout<F, Fut, T>(
    f: F,
    timeout: Duration,
) -> Result<T, TimeoutError>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = T>,
{
    tokio::time::timeout(timeout, f()).await
        .map_err(|_| TimeoutError::Elapsed)
}

// 可取消操作
struct CancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl CancellationToken {
    fn new() -> Self {
        Self {
            cancelled: Arc::new(
# Rust 复杂设计模式与架构设计模式全面指南（续）

## 容错模式（续）

### 4. 超时与取消模式（续）

```rust
// 可取消操作
struct CancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl CancellationToken {
    fn new() -> Self {
        Self {
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }
    
    fn clone(&self) -> Self {
        Self {
            cancelled: Arc::clone(&self.cancelled),
        }
    }
    
    fn cancel(&self) {
        self.cancelled.store(true, Ordering::SeqCst);
    }
    
    fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::SeqCst)
    }
    
    async fn when_cancelled(&self) {
        let cancelled = Arc::clone(&self.cancelled);
        tokio::task::spawn_blocking(move || {
            while !cancelled.load(Ordering::SeqCst) {
                std::thread::sleep(Duration::from_millis(10));
            }
        }).await.expect("Failed to wait for cancellation");
    }
}

// 使用取消令牌执行操作
async fn with_cancellation<F, Fut, T>(
    f: F,
    token: &CancellationToken,
) -> Result<T, CancellationError>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = T>,
{
    if token.is_cancelled() {
        return Err(CancellationError::Cancelled);
    }
    
    tokio::select! {
        result = f() => Ok(result),
        _ = token.when_cancelled() => Err(CancellationError::Cancelled),
    }
}

// 超时自动取消
async fn with_timeout_cancellation<F, Fut, T>(
    f: F,
    timeout: Duration,
) -> Result<T, CancellationError>
where
    F: FnOnce(CancellationToken) -> Fut,
    Fut: Future<Output = Result<T, CancellationError>>,
{
    let token = CancellationToken::new();
    let token_clone = token.clone();
    
    tokio::select! {
        result = f(token_clone) => result,
        _ = tokio::time::sleep(timeout) => {
            token.cancel();
            Err(CancellationError::Timeout)
        }
    }
}

// 传播式取消
struct CascadingCancellation {
    tokens: Vec<CancellationToken>,
}

impl CascadingCancellation {
    fn new() -> Self {
        Self {
            tokens: Vec::new(),
        }
    }
    
    fn add_token(&mut self, token: CancellationToken) {
        self.tokens.push(token);
    }
    
    fn create_linked_token(&mut self) -> CancellationToken {
        let token = CancellationToken::new();
        self.tokens.push(token.clone());
        token
    }
    
    fn cancel_all(&self) {
        for token in &self.tokens {
            token.cancel();
        }
    }
    
    fn is_any_cancelled(&self) -> bool {
        self.tokens.iter().any(|t| t.is_cancelled())
    }
}
```

### 4.5 流量控制与限流

```rust
// 令牌桶限流器
struct TokenBucket {
    capacity: u32,
    tokens: AtomicU32,
    refill_rate: f64,  // 每秒补充的令牌数
    last_refill: AtomicCell<Instant>,
}

impl TokenBucket {
    fn new(capacity: u32, refill_rate: f64) -> Self {
        Self {
            capacity,
            tokens: AtomicU32::new(capacity),
            refill_rate,
            last_refill: AtomicCell::new(Instant::now()),
        }
    }
    
    fn try_acquire(&self, tokens: u32) -> bool {
        self.refill();
        
        let current = self.tokens.load(Ordering::Acquire);
        if current >= tokens {
            match self.tokens.compare_exchange(
                current,
                current - tokens,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => true,
                Err(_) => false, // CAS 失败，重试
            }
        } else {
            false
        }
    }
    
    fn refill(&self) {
        let now = Instant::now();
        let last = self.last_refill.load();
        let elapsed = now.duration_since(last).as_secs_f64();
        
        if elapsed > 0.01 {  // 避免过于频繁的更新
            let new_tokens = (elapsed * self.refill_rate) as u32;
            if new_tokens > 0 {
                let current = self.tokens.load(Ordering::Acquire);
                let updated = std::cmp::min(current + new_tokens, self.capacity);
                self.tokens.store(updated, Ordering::Release);
                self.last_refill.store(now);
            }
        }
    }
}

// 漏桶限流器
struct LeakyBucket {
    capacity: u32,
    level: AtomicU32,
    leak_rate: f64,  // 每秒漏出的水滴数
    last_leak: AtomicCell<Instant>,
}

impl LeakyBucket {
    fn new(capacity: u32, leak_rate: f64) -> Self {
        Self {
            capacity,
            level: AtomicU32::new(0),
            leak_rate,
            last_leak: AtomicCell::new(Instant::now()),
        }
    }
    
    fn try_add(&self, amount: u32) -> bool {
        self.leak();
        
        let current = self.level.load(Ordering::Acquire);
        if current + amount <= self.capacity {
            match self.level.compare_exchange(
                current,
                current + amount,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => true,
                Err(_) => false, // CAS 失败，重试
            }
        } else {
            false
        }
    }
    
    fn leak(&self) {
        let now = Instant::now();
        let last = self.last_leak.load();
        let elapsed = now.duration_since(last).as_secs_f64();
        
        if elapsed > 0.01 {  // 避免过于频繁的更新
            let leaked = (elapsed * self.leak_rate) as u32;
            if leaked > 0 {
                let current = self.level.load(Ordering::Acquire);
                let updated = current.saturating_sub(leaked);
                self.level.store(updated, Ordering::Release);
                self.last_leak.store(now);
            }
        }
    }
}

// 滑动窗口限流器
struct SlidingWindowRateLimiter {
    window_size: Duration,
    max_requests: u32,
    windows: RwLock<VecDeque<(Instant, u32)>>,
}

impl SlidingWindowRateLimiter {
    fn new(window_size: Duration, max_requests: u32) -> Self {
        Self {
            window_size,
            max_requests,
            windows: RwLock::new(VecDeque::new()),
        }
    }
    
    fn try_acquire(&self) -> bool {
        let now = Instant::now();
        
        // 清理过期窗口
        {
            let mut windows = self.windows.write().unwrap();
            while let Some((timestamp, _)) = windows.front() {
                if now.duration_since(*timestamp) > self.window_size {
                    windows.pop_front();
                } else {
                    break;
                }
            }
        }
        
        // 计算当前请求总数
        let current_count = {
            let windows = self.windows.read().unwrap();
            windows.iter().map(|(_, count)| count).sum::<u32>()
        };
        
        if current_count < self.max_requests {
            // 可以接受请求
            let mut windows = self.windows.write().unwrap();
            if let Some((_, count)) = windows.back_mut() {
                // 增加最后一个窗口的计数
                *count += 1;
            } else {
                // 创建新窗口
                windows.push_back((now, 1));
            }
            true
        } else {
            false
        }
    }
}

// 限流中间件
struct RateLimitMiddleware<S, L> {
    inner: S,
    limiter: L,
}

impl<S, L, Req> Service<Req> for RateLimitMiddleware<S, L>
where
    S: Service<Req>,
    L: RateLimiter,
{
    type Response = S::Response;
    type Error = RateLimitError<S::Error>;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>>>>;
    
    fn call(&self, request: Req) -> Self::Future {
        if !self.limiter.try_acquire() {
            return Box::pin(future::ready(Err(RateLimitError::RateLimited)));
        }
        
        let future = self.inner.call(request);
        
        Box::pin(async move {
            future.await.map_err(RateLimitError::InnerError)
        })
    }
}

// 分布式限流器
struct DistributedRateLimiter {
    local_limiter: Box<dyn RateLimiter>,
    redis_client: Arc<Redis>,
    key: String,
    max_rate: u32,
    window: Duration,
}

impl DistributedRateLimiter {
    fn new(
        local_limiter: Box<dyn RateLimiter>,
        redis_client: Arc<Redis>,
        key: &str,
        max_rate: u32,
        window: Duration,
    ) -> Self {
        Self {
            local_limiter,
            redis_client,
            key: key.to_string(),
            max_rate,
            window,
        }
    }
    
    async fn try_acquire(&self) -> Result<bool, DistributedRateLimiterError> {
        // 首先通过本地限流器
        if !self.local_limiter.try_acquire() {
            return Ok(false);
        }
        
        // 然后通过分布式限流器
        let now = Utc::now().timestamp_millis() as u64;
        let window_start = now - self.window.as_millis() as u64;
        
        // 使用 Redis 的 ZREMRANGEBYSCORE 和 ZCARD 命令
        // 1. 移除过期的请求
        // 2. 添加新请求
        // 3. 计算当前窗口内的请求数
        let count: u32 = self.redis_client
            .with_async_connection(|mut conn| {
                Box::pin(async move {
                    // 移除过期的请求
                    redis::pipe()
                        .zremrangebyscore(&self.key, 0, window_start)
                        .ignore()
                        .zadd(&self.key, now.to_string(), now)
                        .ignore()
                        .zcard(&self.key)
                        .query_async(&mut conn)
                        .await
                })
            })
            .await
            .map_err(|e| DistributedRateLimiterError::Redis(e.to_string()))?;
            
        // 设置过期时间
        self.redis_client
            .with_async_connection(|mut conn| {
                Box::pin(async move {
                    redis::cmd("EXPIRE")
                        .arg(&self.key)
                        .arg(self.window.as_secs() * 2) // 设置适当的过期时间
                        .query_async::<_, ()>(&mut conn)
                        .await
                })
            })
            .await
            .map_err(|e| DistributedRateLimiterError::Redis(e.to_string()))?;
            
        // 检查是否超过限制
        Ok(count <= self.max_rate)
    }
}
```

## 5. 一致性模式

### 5.1 分布式锁

```rust
// 分布式锁接口
trait DistributedLock: Send + Sync {
    async fn acquire(&self, key: &str, ttl: Duration) -> Result<LockGuard, LockError>;
    async fn extend(&self, guard: &LockGuard, ttl: Duration) -> Result<(), LockError>;
    async fn release(&self, guard: LockGuard) -> Result<(), LockError>;
}

// 锁守卫
struct LockGuard {
    key: String,
    value: String,
    lock: Arc<dyn DistributedLock>,
}

impl Drop for LockGuard {
    fn drop(&mut self) {
        // 创建一个新的运行时处理锁释放
        let rt = Runtime::new().unwrap();
        let lock = Arc::clone(&self.lock);
        let guard = LockGuard {
            key: self.key.clone(),
            value: self.value.clone(),
            lock: Arc::clone(&self.lock),
        };
        
        rt.block_on(async {
            if let Err(e) = lock.release(guard).await {
                log::error!("Failed to release lock: {}", e);
            }
        });
    }
}

// Redis 实现的分布式锁
struct RedisLock {
    client: Arc<Redis>,
    retry_count: u32,
    retry_delay: Duration,
}

impl RedisLock {
    fn new(client: Arc<Redis>) -> Self {
        Self {
            client,
            retry_count: 3,
            retry_delay: Duration::from_millis(100),
        }
    }
    
    fn with_retry_options(mut self, count: u32, delay: Duration) -> Self {
        self.retry_count = count;
        self.retry_delay = delay;
        self
    }
}

impl DistributedLock for RedisLock {
    async fn acquire(&self, key: &str, ttl: Duration) -> Result<LockGuard, LockError> {
        let lock_value = Uuid::new_v4().to_string();
        let lock_key = format!("lock:{}", key);
        let expiry = ttl.as_millis() as usize;
        
        // 尝试获取锁
        for _ in 0..self.retry_count {
            let result: Option<String> = self.client
                .with_async_connection(|mut conn| {
                    let lock_key = lock_key.clone();
                    let lock_value = lock_value.clone();
                    Box::pin(async move {
                        // SET 命令使用 NX 选项和过期时间
                        redis::cmd("SET")
                            .arg(&lock_key)
                            .arg(&lock_value)
                            .arg("NX")
                            .arg("PX")
                            .arg(expiry)
                            .query_async(&mut conn)
                            .await
                    })
                })
                .await
                .map_err(|e| LockError::Backend(e.to_string()))?;
                
            if result.is_some() {
                // 锁获取成功
                return Ok(LockGuard {
                    key: lock_key,
                    value: lock_value,
                    lock: Arc::new(self.clone()),
                });
            }
            
            // 等待后重试
            tokio::time::sleep(self.retry_delay).await;
        }
        
        Err(LockError::AcquisitionFailed)
    }
    
    async fn extend(&self, guard: &LockGuard, ttl: Duration) -> Result<(), LockError> {
        let expiry = ttl.as_millis() as usize;
        
        // 使用 Lua 脚本延长锁
        let script = r#"
            if redis.call('get', KEYS[1]) == ARGV[1] then
                return redis.call('pexpire', KEYS[1], ARGV[2])
            else
                return 0
            end
        "#;
        
        let result: i32 = self.client
            .with_async_connection(|mut conn| {
                let script = script.to_string();
                let key = guard.key.clone();
                let value = guard.value.clone();
                Box::pin(async move {
                    redis::cmd("EVAL")
                        .arg(&script)
                        .arg(1)
                        .arg(&key)
                        .arg(&value)
                        .arg(expiry)
                        .query_async(&mut conn)
                        .await
                })
            })
            .await
            .map_err(|e| LockError::Backend(e.to_string()))?;
            
        if result == 1 {
            Ok(())
        } else {
            Err(LockError::LockLost)
        }
    }
    
    async fn release(&self, guard: LockGuard) -> Result<(), LockError> {
        // 使用 Lua 脚本释放锁
        let script = r#"
            if redis.call('get', KEYS[1]) == ARGV[1] then
                return redis.call('del', KEYS[1])
            else
                return 0
            end
        "#;
        
        let result: i32 = self.client
            .with_async_connection(|mut conn| {
                let script = script.to_string();
                let key = guard.key.clone();
                let value = guard.value.clone();
                Box::pin(async move {
                    redis::cmd("EVAL")
                        .arg(&script)
                        .arg(1)
                        .arg(&key)
                        .arg(&value)
                        .query_async(&mut conn)
                        .await
                })
            })
            .await
            .map_err(|e| LockError::Backend(e.to_string()))?;
            
        if result == 1 {
            Ok(())
        } else {
            Err(LockError::ReleaseFailed)
        }
    }
}

// 自动续约锁
struct AutoRenewLock {
    inner: Arc<dyn DistributedLock>,
    renew_interval: Duration,
    ttl: Duration,
}

impl AutoRenewLock {
    fn new(lock: Arc<dyn DistributedLock>, ttl: Duration, renew_interval: Duration) -> Self {
        Self {
            inner: lock,
            renew_interval,
            ttl,
        }
    }
    
    async fn acquire(&self, key: &str) -> Result<AutoRenewGuard, LockError> {
        let guard = self.inner.acquire(key, self.ttl).await?;
        
        // 创建自动续约守卫
        let auto_guard = AutoRenewGuard {
            guard,
            lock: Arc::clone(&self.inner),
            renew_interval: self.renew_interval,
            ttl: self.ttl,
            stop_signal: Arc::new(AtomicBool::new(false)),
        };
        
        // 启动自动续约任务
        auto_guard.start_renew_task();
        
        Ok(auto_guard)
    }
}

struct AutoRenewGuard {
    guard: LockGuard,
    lock: Arc<dyn DistributedLock>,
    renew_interval: Duration,
    ttl: Duration,
    stop_signal: Arc<AtomicBool>,
}

impl AutoRenewGuard {
    fn start_renew_task(&self) {
        let lock = Arc::clone(&self.lock);
        let guard = self.guard.clone();
        let interval = self.renew_interval;
        let ttl = self.ttl;
        let stop_signal = Arc::clone(&self.stop_signal);
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(interval);
            
            loop {
                interval.tick().await;
                
                if stop_signal.load(Ordering::SeqCst) {
                    break;
                }
                
                match lock.extend(&guard, ttl).await {
                    Ok(_) => {
                        log::debug!("Lock extended: {}", guard.key);
                    },
                    Err(e) => {
                        log::error!("Failed to extend lock: {}", e);
                        break;
                    }
                }
            }
        });
    }
}

impl Drop for AutoRenewGuard {
    fn drop(&mut self) {
        // 停止续约任务
        self.stop_signal.store(true, Ordering::SeqCst);
        
        // 释放锁在 LockGuard 的 Drop 实现中处理
    }
}
```

### 5.2 Saga 模式与两阶段提交

```rust
// Saga 模式 - 步骤接口
trait SagaStep {
    type Context;
    type Error;
    
    async fn execute(&self, ctx: &Self::Context) -> Result<(), Self::Error>;
    async fn compensate(&self, ctx: &Self::Context) -> Result<(), Self::Error>;
}

// Saga 协调器
struct Saga<C, E> {
    steps: Vec<Box<dyn SagaStep<Context = C, Error = E>>>,
    executed_steps: Vec<usize>,
    context: C,
}

impl<C, E: std::error::Error> Saga<C, E> {
    fn new(context: C) -> Self {
        Self {
            steps: Vec::new(),
            executed_steps: Vec::new(),
            context,
        }
    }
    
    fn add_step<S: SagaStep<Context = C, Error = E> + 'static>(&mut self, step: S) -> &mut Self {
        self.steps.push(Box::new(step));
        self
    }
    
    async fn execute(&mut self) -> Result<(), SagaError<E>> {
        // 执行所有步骤
        for (idx, step) in self.steps.iter().enumerate() {
            match step.execute(&self.context).await {
                Ok(_) => {
                    // 步骤成功执行
                    self.executed_steps.push(idx);
                },
                Err(error) => {
                    // 步骤失败，开始补偿
                    self.compensate().await?;
                    return Err(SagaError::StepFailed(error));
                }
            }
        }
        
        Ok(())
    }
    
    async fn compensate(&self) -> Result<(), SagaError<E>> {
        // 逆序执行补偿
        let mut compensation_errors = Vec::new();
        
        for &idx in self.executed_steps.iter().rev() {
            match self.steps[idx].compensate(&self.context).await {
                Ok(_) => {
                    // 补偿成功
                },
                Err(error) => {
                    // 补偿失败，记录错误但继续其他补偿
                    compensation_errors.push(error);
                }
            }
        }
        
        if compensation_errors.is_empty() {
            Ok(())
        } else {
            Err(SagaError::CompensationFailed(compensation_errors))
        }
    }
}

// 两阶段提交协调器
struct TwoPhaseCommit<R, E> {
    resources: Vec<Box<dyn TransactionResource<Error = E>>>,
    timeout: Duration,
}

impl<R, E: std::error::Error> TwoPhaseCommit<R, E> {
    fn new(timeout: Duration) -> Self {
        Self {
            resources: Vec::new(),
            timeout,
        }
    }
    
    fn add_resource<T: TransactionResource<Error = E> + 'static>(&mut self, resource: T) -> &mut Self {
        self.resources.push(Box::new(resource));
        self
    }
    
    async fn execute<F, Fut>(&self, transaction: F) -> Result<(), TwoPhaseCommitError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<(), E>>,
    {
        // 阶段 1: 准备
        let mut prepared = Vec::new();
        
        for resource in &self.resources {
            match timeout(self.timeout, resource.prepare()).await {
                Ok(Ok(_)) => {
                    // 资源准备就绪
                    prepared.push(resource);
                },
                Ok(Err(e)) => {
                    // 资源准备失败，中止所有已准备的资源
                    self.abort(&prepared).await?;
                    return Err(TwoPhaseCommitError::PrepareFailed(e));
                },
                Err(_) => {
                    // 超时
                    self.abort(&prepared).await?;
                    return Err(TwoPhaseCommitError::Timeout);
                }
            }
        }
        
        // 执行事务
        match timeout(self.timeout, transaction()).await {
            Ok(Ok(_)) => {
                // 阶段 2: 提交
                for resource in &self.resources {
                    if let Err(e) = timeout(self.timeout, resource.commit()).await {
                        // 提交失败，记录错误但继续提交其他资源
                        log::error!("Failed to commit resource: {}", e);
                    }
                }
                
                Ok(())
            },
            Ok(Err(e)) => {
                // 事务执行失败，中止所有资源
                self.abort(&self.resources).await?;
                Err(TwoPhaseCommitError::TransactionFailed(e))
            },
            Err(_) => {
                // 超时
                self.abort(&self.resources).await?;
                Err(TwoPhaseCommitError::Timeout)
            }
        }
    }
    
    async fn abort(&self, resources: &[&Box<dyn TransactionResource<Error = E>>]) -> Result<(), TwoPhaseCommitError<E>> {
        let mut abort_errors = Vec::new();
        
        for resource in resources {
            if let Err(e) = timeout(self.timeout, resource.abort()).await {
                abort_errors.push(e.into());
            }
        }
        
        if abort_errors.is_empty() {
            Ok(())
        } else {
            Err(TwoPhaseCommitError::AbortFailed(abort_errors))
        }
    }
}
```

### 5.3 最终一致性与事件溯源

```rust
// 事件接口
trait Event: Send + Sync + 'static {
    fn event_type(&self) -> &'static str;
    fn serialize(&self) -> Result<Vec<u8>, SerializationError>;
}

// 事件存储
trait EventStore: Send + Sync {
    async fn append_events<E: Event>(&self, stream_id: &str, events: &[E], expected_version: Option<u64>) -> Result<u64, EventStoreError>;
    async fn read_stream(&self, stream_id: &str, start: u64, count: usize) -> Result<Vec<EventRecord>, EventStoreError>;
}

// 事件记录
struct EventRecord {
    stream_id: String,
    version: u64,
    event_type: String,
    data: Vec<u8>,
    metadata: HashMap<String, String>,
    timestamp: DateTime<Utc>,
}

// 聚合根
trait AggregateRoot: Send + Sync {
    type Id: AsRef<str>;
    type Event: Event;
    type Error;
    
    fn id(&self) -> &Self::Id;
    fn version(&self) -> u64;
    fn apply(&mut self, event: Self::Event) -> Result<(), Self::Error>;
}

// 事件源存储库
struct EventSourcedRepository<A, E, S>
where
    A: AggregateRoot<Event = E>,
    E: Event,
    S: EventStore,
{
    event_store: S,
    _marker: PhantomData<(A, E)>,
}

impl<A, E, S> EventSourcedRepository<A, E, S>
where
    A: AggregateRoot<Event = E>,
    E: Event,
    S: EventStore,
{
    fn new(event_store: S) -> Self {
        Self {
            event_store,
            _marker: PhantomData,
        }
    }
    
    async fn load(&self, id: &A::Id) -> Result<Option<A>, RepositoryError<A::Error>> {
        // 从事件存储读取所有事件
        let events = self.event_store.read_stream(id.as_ref(), 0, u64::MAX as usize)
            .await
            .map_err(RepositoryError::StoreError)?;
            
        if events.is_empty() {
            return Ok(None);
        }
        
        // 反序列化事件并应用到聚合根
        let mut aggregate = A::new();
        
        for record in events {
            let event = E::deserialize(&record.data)
                .map_err(RepositoryError::DeserializationError)?;
                
            aggregate.apply(event)
                .map_err(RepositoryError::AggregateError)?;
        }
        
        Ok(Some(aggregate))
    }
    
    async fn save(&self, aggregate: &mut A, events: &[E]) -> Result<(), RepositoryError<A::Error>> {
        if events.is_empty() {
            return Ok(());
        }
        
        // 将事件追加到存储
        let new_version = self.event_store.append_events(
            aggregate.id().as_ref(), 
            events, 
# Rust 复杂设计模式与架构设计模式全面指南（续）

## 一致性模式（续）

### 3. 最终一致性与事件溯源（续）

```rust
    async fn save(&self, aggregate: &mut A, events: &[E]) -> Result<(), RepositoryError<A::Error>> {
        if events.is_empty() {
            return Ok(());
        }
        
        // 将事件追加到存储
        let new_version = self.event_store.append_events(
            aggregate.id().as_ref(), 
            events, 
            Some(aggregate.version())
        )
        .await
        .map_err(RepositoryError::StoreError)?;
        
        // 应用事件到聚合根
        for event in events {
            aggregate.apply(event.clone())
                .map_err(RepositoryError::AggregateError)?;
        }
        
        // 更新聚合根版本
        aggregate.set_version(new_version);
        
        Ok(())
    }
}

// 事件发布器
trait EventPublisher<E: Event> {
    async fn publish(&self, event: E) -> Result<(), PublishError>;
    async fn publish_all(&self, events: Vec<E>) -> Result<(), PublishError>;
}

// 事件处理器
trait EventHandler<E: Event> {
    async fn handle(&self, event: E) -> Result<(), HandlerError>;
}

// 事件处理器注册表
struct EventHandlerRegistry<E: Event> {
    handlers: RwLock<HashMap<&'static str, Vec<Box<dyn EventHandler<E>>>>>,
}

impl<E: Event> EventHandlerRegistry<E> {
    fn new() -> Self {
        Self {
            handlers: RwLock::new(HashMap::new()),
        }
    }
    
    fn register<H: EventHandler<E> + 'static>(&self, event_type: &'static str, handler: H) {
        let mut handlers = self.handlers.write().unwrap();
        handlers.entry(event_type).or_default().push(Box::new(handler));
    }
    
    async fn dispatch(&self, event: E) -> Result<(), DispatchError> {
        let event_type = event.event_type();
        let handlers = self.handlers.read().unwrap();
        
        if let Some(handlers) = handlers.get(event_type) {
            for handler in handlers {
                if let Err(e) = handler.handle(event.clone()).await {
                    return Err(DispatchError::HandlerError(e));
                }
            }
        }
        
        Ok(())
    }
}

// 最终一致性服务 - 提供更新和查询功能
struct EventuallyConsistentService<E: Event, S: EventStore, P: EventPublisher<E>> {
    event_store: S,
    event_publisher: P,
    _marker: PhantomData<E>,
}

impl<E: Event, S: EventStore, P: EventPublisher<E>> EventuallyConsistentService<E, S, P> {
    fn new(event_store: S, event_publisher: P) -> Self {
        Self {
            event_store,
            event_publisher,
            _marker: PhantomData,
        }
    }
    
    async fn execute_command<A, C, R>(
        &self,
        id: &A::Id,
        command: C,
    ) -> Result<R, ServiceError<A::Error>>
    where
        A: AggregateRoot<Event = E>,
        C: Command<Aggregate = A, Result = R>,
    {
        // 加载聚合根
        let repository = EventSourcedRepository::new(&self.event_store);
        let mut aggregate = repository.load(id).await?
            .unwrap_or_else(|| A::new(id.clone()));
            
        // 执行命令
        let (result, events) = command.execute(&aggregate)
            .map_err(ServiceError::CommandError)?;
            
        // 保存事件
        repository.save(&mut aggregate, &events).await?;
        
        // 发布事件
        self.event_publisher.publish_all(events).await
            .map_err(ServiceError::PublishError)?;
            
        Ok(result)
    }
}
```

### 5.4 CQRS 模式

```rust
// 命令
trait Command {
    type Aggregate;
    type Result;
    type Error;
    
    fn execute(self, aggregate: &Self::Aggregate) -> Result<(Self::Result, Vec<Self::Aggregate::Event>), Self::Error>;
}

// 查询
trait Query {
    type Result;
    type Error;
    
    async fn execute(self, store: &dyn QueryStore) -> Result<Self::Result, Self::Error>;
}

// 查询存储接口
trait QueryStore: Send + Sync {
    async fn get<T: DeserializeOwned>(&self, key: &str) -> Result<Option<T>, QueryStoreError>;
    async fn query<Q: QueryPredicate>(&self, query: Q) -> Result<Vec<Q::Item>, QueryStoreError>;
}

// 查询谓词
trait QueryPredicate {
    type Item: DeserializeOwned;
    
    fn matches(&self, item: &Self::Item) -> bool;
    fn collection(&self) -> &str;
}

// 命令总线
struct CommandBus<A> {
    handlers: RwLock<HashMap<TypeId, Box<dyn Fn(Box<dyn Any>) -> Pin<Box<dyn Future<Output = Result<Box<dyn Any>, Box<dyn std::error::Error>>>>>>>,
    _marker: PhantomData<A>,
}

impl<A: AggregateRoot + 'static> CommandBus<A> {
    fn new() -> Self {
        Self {
            handlers: RwLock::new(HashMap::new()),
            _marker: PhantomData,
        }
    }
    
    fn register<C, H, R, E>(&self, handler: H)
    where
        C: Command<Aggregate = A, Result = R, Error = E> + 'static,
        H: Fn(C) -> Pin<Box<dyn Future<Output = Result<R, E>>>> + Send + Sync + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        let type_id = TypeId::of::<C>();
        
        let boxed_handler = Box::new(move |command: Box<dyn Any>| {
            let command = *command.downcast::<C>().expect("Command type mismatch");
            
            Box::pin(async move {
                match handler(command).await {
                    Ok(result) => Ok(Box::new(result) as Box<dyn Any>),
                    Err(e) => Err(Box::new(e) as Box<dyn std::error::Error>),
                }
            }) as Pin<Box<dyn Future<Output = Result<Box<dyn Any>, Box<dyn std::error::Error>>>>>
        });
        
        let mut handlers = self.handlers.write().unwrap();
        handlers.insert(type_id, boxed_handler);
    }
    
    async fn dispatch<C, R, E>(&self, command: C) -> Result<R, CommandBusError<E>>
    where
        C: Command<Aggregate = A, Result = R, Error = E> + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        let type_id = TypeId::of::<C>();
        
        let handler = {
            let handlers = self.handlers.read().unwrap();
            handlers.get(&type_id)
                .cloned()
                .ok_or_else(|| CommandBusError::HandlerNotFound(type_name::<C>()))?
        };
        
        let boxed_command = Box::new(command);
        
        match handler(boxed_command).await {
            Ok(result) => {
                result.downcast::<R>()
                    .map(|r| *r)
                    .map_err(|_| CommandBusError::ResultTypeMismatch)
            },
            Err(e) => {
                if let Some(typed_error) = e.downcast_ref::<E>() {
                    Err(CommandBusError::CommandError(typed_error.clone()))
                } else {
                    Err(CommandBusError::UnexpectedError(e.to_string()))
                }
            }
        }
    }
}

// 查询总线
struct QueryBus {
    handlers: RwLock<HashMap<TypeId, Box<dyn Fn(Box<dyn Any>) -> Pin<Box<dyn Future<Output = Result<Box<dyn Any>, Box<dyn std::error::Error>>>>>>>,
}

impl QueryBus {
    fn new() -> Self {
        Self {
            handlers: RwLock::new(HashMap::new()),
        }
    }
    
    fn register<Q, H, R, E>(&self, handler: H)
    where
        Q: Query<Result = R, Error = E> + 'static,
        H: Fn(Q) -> Pin<Box<dyn Future<Output = Result<R, E>>>> + Send + Sync + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        let type_id = TypeId::of::<Q>();
        
        let boxed_handler = Box::new(move |query: Box<dyn Any>| {
            let query = *query.downcast::<Q>().expect("Query type mismatch");
            
            Box::pin(async move {
                match handler(query).await {
                    Ok(result) => Ok(Box::new(result) as Box<dyn Any>),
                    Err(e) => Err(Box::new(e) as Box<dyn std::error::Error>),
                }
            }) as Pin<Box<dyn Future<Output = Result<Box<dyn Any>, Box<dyn std::error::Error>>>>>
        });
        
        let mut handlers = self.handlers.write().unwrap();
        handlers.insert(type_id, boxed_handler);
    }
    
    async fn dispatch<Q, R, E>(&self, query: Q) -> Result<R, QueryBusError<E>>
    where
        Q: Query<Result = R, Error = E> + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        let type_id = TypeId::of::<Q>();
        
        let handler = {
            let handlers = self.handlers.read().unwrap();
            handlers.get(&type_id)
                .cloned()
                .ok_or_else(|| QueryBusError::HandlerNotFound(type_name::<Q>()))?
        };
        
        let boxed_query = Box::new(query);
        
        match handler(boxed_query).await {
            Ok(result) => {
                result.downcast::<R>()
                    .map(|r| *r)
                    .map_err(|_| QueryBusError::ResultTypeMismatch)
            },
            Err(e) => {
                if let Some(typed_error) = e.downcast_ref::<E>() {
                    Err(QueryBusError::QueryError(typed_error.clone()))
                } else {
                    Err(QueryBusError::UnexpectedError(e.to_string()))
                }
            }
        }
    }
}

// 投影器接口 - 用于从事件构建读模型
trait Projector<E: Event> {
    type Error;
    
    async fn project(&self, event: E) -> Result<(), Self::Error>;
    async fn rebuild(&self) -> Result<(), Self::Error>;
}

// 基于内存的简单投影器实现
struct InMemoryProjector<E: Event, S: QueryStore> {
    event_store: Arc<dyn EventStore>,
    query_store: S,
    _marker: PhantomData<E>,
}

impl<E: Event, S: QueryStore> InMemoryProjector<E, S> {
    fn new(event_store: Arc<dyn EventStore>, query_store: S) -> Self {
        Self {
            event_store,
            query_store,
            _marker: PhantomData,
        }
    }
}

impl<E: Event, S: QueryStore> Projector<E> for InMemoryProjector<E, S> {
    type Error = ProjectionError;
    
    async fn project(&self, event: E) -> Result<(), Self::Error> {
        // 根据事件类型更新查询存储
        match event.event_type() {
            "ItemCreated" => {
                if let Some(item) = event.as_any().downcast_ref::<ItemCreatedEvent>() {
                    // 创建新项目
                    let model = ItemReadModel {
                        id: item.id.clone(),
                        name: item.name.clone(),
                        created_at: item.timestamp,
                        updated_at: item.timestamp,
                    };
                    
                    self.query_store.store(&format!("items:{}", item.id), &model).await
                        .map_err(|e| ProjectionError::StoreError(e.to_string()))?;
                }
            },
            "ItemUpdated" => {
                if let Some(item) = event.as_any().downcast_ref::<ItemUpdatedEvent>() {
                    // 更新现有项目
                    let item_key = format!("items:{}", item.id);
                    
                    if let Some(mut model) = self.query_store.get::<ItemReadModel>(&item_key).await
                        .map_err(|e| ProjectionError::StoreError(e.to_string()))? {
                        
                        model.name = item.new_name.clone();
                        model.updated_at = item.timestamp;
                        
                        self.query_store.store(&item_key, &model).await
                            .map_err(|e| ProjectionError::StoreError(e.to_string()))?;
                    }
                }
            },
            _ => {
                // 忽略其他事件类型
            }
        }
        
        Ok(())
    }
    
    async fn rebuild(&self) -> Result<(), Self::Error> {
        // 清除现有投影
        self.query_store.clear("items").await
            .map_err(|e| ProjectionError::StoreError(e.to_string()))?;
            
        // 从事件存储读取所有事件并重新投影
        let all_events = self.event_store.read_all(0, u64::MAX as usize).await
            .map_err(|e| ProjectionError::EventStoreError(e.to_string()))?;
            
        for record in all_events {
            let event = E::deserialize(&record.data)
                .map_err(|e| ProjectionError::DeserializationError(e.to_string()))?;
                
            self.project(event).await?;
        }
        
        Ok(())
    }
}

// CQRS 服务
struct CqrsService<A: AggregateRoot + 'static> {
    command_bus: CommandBus<A>,
    query_bus: QueryBus,
    event_publisher: Arc<dyn EventPublisher<A::Event>>,
}

impl<A: AggregateRoot + 'static> CqrsService<A> {
    fn new(event_publisher: Arc<dyn EventPublisher<A::Event>>) -> Self {
        Self {
            command_bus: CommandBus::new(),
            query_bus: QueryBus::new(),
            event_publisher,
        }
    }
    
    fn register_command_handler<C, H, R, E>(&self, handler: H)
    where
        C: Command<Aggregate = A, Result = R, Error = E> + 'static,
        H: Fn(C) -> Pin<Box<dyn Future<Output = Result<R, E>>>> + Send + Sync + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        self.command_bus.register(handler);
    }
    
    fn register_query_handler<Q, H, R, E>(&self, handler: H)
    where
        Q: Query<Result = R, Error = E> + 'static,
        H: Fn(Q) -> Pin<Box<dyn Future<Output = Result<R, E>>>> + Send + Sync + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        self.query_bus.register(handler);
    }
    
    async fn execute_command<C, R, E>(&self, command: C) -> Result<R, CqrsServiceError<E>>
    where
        C: Command<Aggregate = A, Result = R, Error = E> + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        let result = self.command_bus.dispatch(command).await
            .map_err(CqrsServiceError::CommandError)?;
            
        // 发布事件
        // 在实际实现中，可能需要从命令处理程序获取生成的事件
        
        Ok(result)
    }
    
    async fn execute_query<Q, R, E>(&self, query: Q) -> Result<R, CqrsServiceError<E>>
    where
        Q: Query<Result = R, Error = E> + 'static,
        R: 'static,
        E: std::error::Error + 'static,
    {
        self.query_bus.dispatch(query).await
            .map_err(CqrsServiceError::QueryError)
    }
}
```

### 5.5 幂等性与重复请求处理

```rust
// 幂等性键生成器
trait IdempotencyKeyGenerator {
    fn generate_key<T: Hash>(&self, request: &T) -> String;
}

// 基于请求内容的幂等性键生成器
struct ContentBasedKeyGenerator {
    namespace: String,
}

impl ContentBasedKeyGenerator {
    fn new(namespace: &str) -> Self {
        Self {
            namespace: namespace.to_string(),
        }
    }
}

impl IdempotencyKeyGenerator for ContentBasedKeyGenerator {
    fn generate_key<T: Hash>(&self, request: &T) -> String {
        let mut hasher = DefaultHasher::new();
        request.hash(&mut hasher);
        let hash = hasher.finish();
        
        format!("{}:{:x}", self.namespace, hash)
    }
}

// 幂等性存储
trait IdempotencyStore: Send + Sync {
    async fn record_request<T: Serialize>(&self, key: &str, response: &T) -> Result<bool, IdempotencyError>;
    async fn get_response<T: DeserializeOwned>(&self, key: &str) -> Result<Option<T>, IdempotencyError>;
    async fn clear_expired(&self, max_age: Duration) -> Result<u64, IdempotencyError>;
}

// Redis 实现的幂等性存储
struct RedisIdempotencyStore {
    client: Arc<Redis>,
    expiry: Duration,
}

impl RedisIdempotencyStore {
    fn new(client: Arc<Redis>, expiry: Duration) -> Self {
        Self {
            client,
            expiry,
        }
    }
}

impl IdempotencyStore for RedisIdempotencyStore {
    async fn record_request<T: Serialize>(&self, key: &str, response: &T) -> Result<bool, IdempotencyError> {
        let serialized = serde_json::to_string(response)
            .map_err(|e| IdempotencyError::Serialization(e.to_string()))?;
            
        let expiry_secs = self.expiry.as_secs() as usize;
        
        let result: bool = self.client
            .with_async_connection(|mut conn| {
                let key = key.to_string();
                let serialized = serialized.clone();
                Box::pin(async move {
                    // 使用 SET NX 命令
                    redis::cmd("SET")
                        .arg(&key)
                        .arg(&serialized)
                        .arg("NX")
                        .arg("EX")
                        .arg(expiry_secs)
                        .query_async(&mut conn)
                        .await
                })
            })
            .await
            .map_err(|e| IdempotencyError::Storage(e.to_string()))?;
            
        Ok(result)
    }
    
    async fn get_response<T: DeserializeOwned>(&self, key: &str) -> Result<Option<T>, IdempotencyError> {
        let result: Option<String> = self.client
            .with_async_connection(|mut conn| {
                let key = key.to_string();
                Box::pin(async move {
                    redis::cmd("GET")
                        .arg(&key)
                        .query_async(&mut conn)
                        .await
                })
            })
            .await
            .map_err(|e| IdempotencyError::Storage(e.to_string()))?;
            
        match result {
            Some(data) => {
                let response = serde_json::from_str(&data)
                    .map_err(|e| IdempotencyError::Deserialization(e.to_string()))?;
                Ok(Some(response))
            },
            None => Ok(None),
        }
    }
    
    async fn clear_expired(&self, max_age: Duration) -> Result<u64, IdempotencyError> {
        // Redis 会自动清除过期的键
        Ok(0)
    }
}

// 幂等性处理器
struct IdempotencyHandler<S: IdempotencyStore, G: IdempotencyKeyGenerator> {
    store: S,
    key_generator: G,
}

impl<S: IdempotencyStore, G: IdempotencyKeyGenerator> IdempotencyHandler<S, G> {
    fn new(store: S, key_generator: G) -> Self {
        Self {
            store,
            key_generator,
        }
    }
    
    async fn handle<Req, Resp, F, Fut, E>(&self, request: Req, handler: F) -> Result<Resp, IdempotencyHandlerError<E>>
    where
        Req: Hash + Serialize,
        Resp: Serialize + DeserializeOwned,
        F: FnOnce(Req) -> Fut,
        Fut: Future<Output = Result<Resp, E>>,
        E: std::error::Error,
    {
        // 生成幂等性键
        let key = self.key_generator.generate_key(&request);
        
        // 检查是否已处理过请求
        if let Some(response) = self.store.get_response::<Resp>(&key).await
            .map_err(IdempotencyHandlerError::IdempotencyError)? {
            // 返回缓存的响应
            return Ok(response);
        }
        
        // 处理请求
        let response = handler(request).await
            .map_err(IdempotencyHandlerError::HandlerError)?;
            
        // 记录响应
        self.store.record_request(&key, &response).await
            .map_err(IdempotencyHandlerError::IdempotencyError)?;
            
        Ok(response)
    }
}

// 使用装饰器模式实现幂等性服务
struct IdempotentService<S, I: IdempotencyStore, G: IdempotencyKeyGenerator> {
    inner: S,
    idempotency_handler: IdempotencyHandler<I, G>,
}

impl<S, I: IdempotencyStore, G: IdempotencyKeyGenerator> IdempotentService<S, I, G> {
    fn new(inner: S, idempotency_handler: IdempotencyHandler<I, G>) -> Self {
        Self {
            inner,
            idempotency_handler,
        }
    }
}

// 实现 Service 特征
impl<S, I, G, Req> Service<Req> for IdempotentService<S, I, G>
where
    S: Service<Req>,
    I: IdempotencyStore,
    G: IdempotencyKeyGenerator,
    Req: Hash + Serialize + Clone,
    S::Response: Serialize + DeserializeOwned,
    S::Error: std::error::Error,
{
    type Response = S::Response;
    type Error = IdempotencyHandlerError<S::Error>;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>>>>;
    
    fn call(&self, request: Req) -> Self::Future {
        let handler = self.idempotency_handler.clone();
        let inner = self.inner.clone();
        
        Box::pin(async move {
            handler.handle(request.clone(), move |req| inner.call(req)).await
        })
    }
}
```

## 6. 综合架构模式

### 6.1 分层架构

```rust
// 领域层 - 定义核心业务模型和规则
mod domain {
    // 实体和值对象
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct EntityId(pub String);
    
    #[derive(Clone, Debug)]
    pub struct Entity {
        pub id: EntityId,
        pub name: String,
        pub value: i32,
    }
    
    // 领域服务
    pub trait DomainService {
        fn validate_entity(&self, entity: &Entity) -> Result<(), DomainError>;
        fn calculate_value(&self, entity: &Entity) -> i32;
    }
    
    // 领域事件
    #[derive(Clone, Debug)]
    pub enum DomainEvent {
        EntityCreated(Entity),
        EntityUpdated { id: EntityId, old_value: i32, new_value: i32 },
        EntityDeleted(EntityId),
    }
    
    // 领域错误
    #[derive(Debug, thiserror::Error)]
    pub enum DomainError {
        #[error("Invalid entity: {0}")]
        InvalidEntity(String),
        
        #[error("Entity not found: {0}")]
        NotFound(String),
        
        #[error("Operation not allowed: {0}")]
        OperationNotAllowed(String),
    }
    
    // 领域策略和规则
    pub mod rules {
        use super::*;
        
        pub fn validate_entity_name(name: &str) -> Result<(), DomainError> {
            if name.is_empty() {
                return Err(DomainError::InvalidEntity("Name cannot be empty".to_string()));
            }
            
            if name.len() > 100 {
                return Err(DomainError::InvalidEntity("Name too long".to_string()));
            }
            
            Ok(())
        }
        
        pub fn validate_entity_value(value: i32) -> Result<(), DomainError> {
            if value < 0 {
                return Err(DomainError::InvalidEntity("Value cannot be negative".to_string()));
            }
            
            Ok(())
        }
    }
}

// 应用层 - 协调领域对象来执行特定用例
mod application {
    use super::domain::*;
    use std::sync::Arc;
    
    // 应用服务
    pub trait EntityService {
        async fn create_entity(&self, name: String, value: i32) -> Result<Entity, ApplicationError>;
        async fn update_entity(&self, id: EntityId, name: Option<String>, value: Option<i32>) -> Result<Entity, ApplicationError>;
        async fn delete_entity(&self, id: EntityId) -> Result<(), ApplicationError>;
        async fn get_entity(&self, id: EntityId) -> Result<Entity, ApplicationError>;
        async fn list_entities(&self) -> Result<Vec<Entity>, ApplicationError>;
    }
    
    // 应用错误
    #[derive(Debug, thiserror::Error)]
    pub enum ApplicationError {
        #[error("Domain error: {0}")]
        DomainError(#[from] DomainError),
        
        #[error("Repository error: {0}")]
        RepositoryError(String),
        
        #[error("Service error: {0}")]
        ServiceError(String),
    }
    
    // 实现应用服务
    pub struct EntityServiceImpl<R, D> {
        repository: Arc<R>,
        domain_service: Arc<D>,
        event_publisher: Arc<dyn EventPublisher>,
    }
    
    // 事件发布器
    pub trait EventPublisher: Send + Sync {
        fn publish(&self, event: DomainEvent) -> BoxFuture<'static, Result<(), PublishError>>;
    }
    
    // 存储库
    pub trait EntityRepository: Send + Sync {
        fn save(&self, entity: Entity) -> BoxFuture<'static, Result<(), RepositoryError>>;
        fn find_by_id(&self, id: &EntityId) -> BoxFuture<'static, Result<Option<Entity>, RepositoryError>>;
        fn delete(&self, id: &EntityId) -> BoxFuture<'static, Result<(), RepositoryError>>;
        fn find_all(&self) -> BoxFuture<'static, Result<Vec<Entity>, RepositoryError>>;
    }
    
    impl<R, D> EntityService for EntityServiceImpl<R, D>
    where
        R: EntityRepository + 'static,
        D: DomainService + 'static,
    {
        async fn create_entity(&self, name: String, value: i32) -> Result<Entity, ApplicationError> {
            // 创建实体
            let id = EntityId(Uuid::new_v4().to_string());
            let entity = Entity { id: id.clone(), name, value };
            
            // 验证实体
            self.domain_service.validate_entity(&entity)?;
            
            // 保存实体
            self.repository.save(entity.clone()).await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?;
                
            // 发布事件
            self.event_publisher.publish(DomainEvent::EntityCreated(entity.clone()
# Rust 复杂设计模式与架构设计模式全面指南（续）

## 综合架构模式（续）

### 1. 分层架构（续）

```rust
    impl<R, D> EntityService for EntityServiceImpl<R, D>
    where
        R: EntityRepository + 'static,
        D: DomainService + 'static,
    {
        async fn create_entity(&self, name: String, value: i32) -> Result<Entity, ApplicationError> {
            // 创建实体
            let id = EntityId(Uuid::new_v4().to_string());
            let entity = Entity { id: id.clone(), name, value };
            
            // 验证实体
            self.domain_service.validate_entity(&entity)?;
            
            // 保存实体
            self.repository.save(entity.clone()).await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?;
                
            // 发布事件
            self.event_publisher.publish(DomainEvent::EntityCreated(entity.clone())).await
                .map_err(|e| ApplicationError::ServiceError(e.to_string()))?;
                
            Ok(entity)
        }
        
        async fn update_entity(&self, id: EntityId, name: Option<String>, value: Option<i32>) -> Result<Entity, ApplicationError> {
            // 查找实体
            let mut entity = self.repository.find_by_id(&id).await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?
                .ok_or_else(|| ApplicationError::DomainError(DomainError::NotFound(id.0.clone())))?;
                
            let old_value = entity.value;
            
            // 更新字段
            if let Some(name) = name {
                entity.name = name;
            }
            
            if let Some(value) = value {
                entity.value = value;
            }
            
            // 验证实体
            self.domain_service.validate_entity(&entity)?;
            
            // 保存实体
            self.repository.save(entity.clone()).await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?;
                
            // 发布事件
            if old_value != entity.value {
                self.event_publisher.publish(DomainEvent::EntityUpdated {
                    id: id.clone(),
                    old_value,
                    new_value: entity.value,
                }).await
                .map_err(|e| ApplicationError::ServiceError(e.to_string()))?;
            }
            
            Ok(entity)
        }
        
        async fn delete_entity(&self, id: EntityId) -> Result<(), ApplicationError> {
            // 检查实体是否存在
            let exists = self.repository.find_by_id(&id).await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?
                .is_some();
                
            if !exists {
                return Err(ApplicationError::DomainError(DomainError::NotFound(id.0.clone())));
            }
            
            // 删除实体
            self.repository.delete(&id).await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?;
                
            // 发布事件
            self.event_publisher.publish(DomainEvent::EntityDeleted(id)).await
                .map_err(|e| ApplicationError::ServiceError(e.to_string()))?;
                
            Ok(())
        }
        
        async fn get_entity(&self, id: EntityId) -> Result<Entity, ApplicationError> {
            self.repository.find_by_id(&id).await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?
                .ok_or_else(|| ApplicationError::DomainError(DomainError::NotFound(id.0.clone())))
        }
        
        async fn list_entities(&self) -> Result<Vec<Entity>, ApplicationError> {
            self.repository.find_all().await
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))
        }
    }
}

// 基础设施层 - 提供技术实现
mod infrastructure {
    use super::application::*;
    use super::domain::*;
    use async_trait::async_trait;
    use std::collections::HashMap;
    use std::sync::{Arc, RwLock};
    
    // 内存存储库实现
    pub struct InMemoryEntityRepository {
        entities: RwLock<HashMap<String, Entity>>,
    }
    
    impl InMemoryEntityRepository {
        pub fn new() -> Self {
            Self {
                entities: RwLock::new(HashMap::new()),
            }
        }
    }
    
    #[async_trait]
    impl EntityRepository for InMemoryEntityRepository {
        async fn save(&self, entity: Entity) -> Result<(), RepositoryError> {
            let mut entities = self.entities.write()
                .map_err(|_| RepositoryError::LockError)?;
                
            entities.insert(entity.id.0.clone(), entity);
            Ok(())
        }
        
        async fn find_by_id(&self, id: &EntityId) -> Result<Option<Entity>, RepositoryError> {
            let entities = self.entities.read()
                .map_err(|_| RepositoryError::LockError)?;
                
            Ok(entities.get(&id.0).cloned())
        }
        
        async fn delete(&self, id: &EntityId) -> Result<(), RepositoryError> {
            let mut entities = self.entities.write()
                .map_err(|_| RepositoryError::LockError)?;
                
            entities.remove(&id.0);
            Ok(())
        }
        
        async fn find_all(&self) -> Result<Vec<Entity>, RepositoryError> {
            let entities = self.entities.read()
                .map_err(|_| RepositoryError::LockError)?;
                
            Ok(entities.values().cloned().collect())
        }
    }
    
    // 领域服务实现
    pub struct DomainServiceImpl;
    
    impl DomainService for DomainServiceImpl {
        fn validate_entity(&self, entity: &Entity) -> Result<(), DomainError> {
            rules::validate_entity_name(&entity.name)?;
            rules::validate_entity_value(entity.value)?;
            Ok(())
        }
        
        fn calculate_value(&self, entity: &Entity) -> i32 {
            // 一些业务逻辑计算
            entity.value * 2
        }
    }
    
    // 事件发布器实现
    pub struct EventPublisherImpl {
        handlers: RwLock<Vec<Box<dyn Fn(DomainEvent) -> BoxFuture<'static, ()> + Send + Sync>>>,
    }
    
    impl EventPublisherImpl {
        pub fn new() -> Self {
            Self {
                handlers: RwLock::new(Vec::new()),
            }
        }
        
        pub fn register_handler<F, Fut>(&self, handler: F)
        where
            F: Fn(DomainEvent) -> Fut + Send + Sync + 'static,
            Fut: Future<Output = ()> + Send + 'static,
        {
            let mut handlers = self.handlers.write().unwrap();
            
            let boxed_handler = Box::new(move |event: DomainEvent| {
                Box::pin(handler(event)) as BoxFuture<'static, ()>
            });
            
            handlers.push(boxed_handler);
        }
    }
    
    #[async_trait]
    impl EventPublisher for EventPublisherImpl {
        async fn publish(&self, event: DomainEvent) -> Result<(), PublishError> {
            let handlers = self.handlers.read()
                .map_err(|_| PublishError::LockError)?;
                
            for handler in handlers.iter() {
                handler(event.clone()).await;
            }
            
            Ok(())
        }
    }
}

// 接口层 - 处理外部交互
mod interfaces {
    use super::application::*;
    use super::domain::*;
    use axum::{
        extract::{Path, Json},
        routing::{get, post, put, delete},
        Router,
    };
    use serde::{Deserialize, Serialize};
    use std::sync::Arc;
    
    // API 请求和响应模型
    #[derive(Deserialize)]
    pub struct CreateEntityRequest {
        pub name: String,
        pub value: i32,
    }
    
    #[derive(Deserialize)]
    pub struct UpdateEntityRequest {
        pub name: Option<String>,
        pub value: Option<i32>,
    }
    
    #[derive(Serialize)]
    pub struct EntityResponse {
        pub id: String,
        pub name: String,
        pub value: i32,
    }
    
    // 转换函数
    fn entity_to_response(entity: Entity) -> EntityResponse {
        EntityResponse {
            id: entity.id.0,
            name: entity.name,
            value: entity.value,
        }
    }
    
    // 控制器构建函数
    pub fn build_router<S: EntityService + Send + Sync + 'static>(
        entity_service: Arc<S>,
    ) -> Router {
        Router::new()
            .route("/entities", get(list_entities::<S>))
            .route("/entities", post(create_entity::<S>))
            .route("/entities/:id", get(get_entity::<S>))
            .route("/entities/:id", put(update_entity::<S>))
            .route("/entities/:id", delete(delete_entity::<S>))
            .with_state(entity_service)
    }
    
    // 路由处理函数
    async fn list_entities<S: EntityService + Send + Sync>(
        State(service): State<Arc<S>>,
    ) -> Result<Json<Vec<EntityResponse>>, AppError> {
        let entities = service.list_entities().await
            .map_err(AppError::from)?;
            
        Ok(Json(entities.into_iter().map(entity_to_response).collect()))
    }
    
    async fn get_entity<S: EntityService + Send + Sync>(
        State(service): State<Arc<S>>,
        Path(id): Path<String>,
    ) -> Result<Json<EntityResponse>, AppError> {
        let entity = service.get_entity(EntityId(id)).await
            .map_err(AppError::from)?;
            
        Ok(Json(entity_to_response(entity)))
    }
    
    async fn create_entity<S: EntityService + Send + Sync>(
        State(service): State<Arc<S>>,
        Json(request): Json<CreateEntityRequest>,
    ) -> Result<Json<EntityResponse>, AppError> {
        let entity = service.create_entity(request.name, request.value).await
            .map_err(AppError::from)?;
            
        Ok(Json(entity_to_response(entity)))
    }
    
    async fn update_entity<S: EntityService + Send + Sync>(
        State(service): State<Arc<S>>,
        Path(id): Path<String>,
        Json(request): Json<UpdateEntityRequest>,
    ) -> Result<Json<EntityResponse>, AppError> {
        let entity = service.update_entity(EntityId(id), request.name, request.value).await
            .map_err(AppError::from)?;
            
        Ok(Json(entity_to_response(entity)))
    }
    
    async fn delete_entity<S: EntityService + Send + Sync>(
        State(service): State<Arc<S>>,
        Path(id): Path<String>,
    ) -> Result<(), AppError> {
        service.delete_entity(EntityId(id)).await
            .map_err(AppError::from)?;
            
        Ok(())
    }
}
```

### 6.2 六边形架构（端口与适配器）

```rust
// 领域核心
mod domain {
    // 实体和值对象
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct UserId(pub String);
    
    #[derive(Clone, Debug)]
    pub struct User {
        pub id: UserId,
        pub username: String,
        pub email: String,
        pub active: bool,
    }
    
    // 领域异常
    #[derive(Debug, thiserror::Error)]
    pub enum DomainError {
        #[error("Invalid user: {0}")]
        InvalidUser(String),
        
        #[error("User not found: {0}")]
        NotFound(String),
    }
    
    // 领域服务
    pub struct UserDomainService;
    
    impl UserDomainService {
        pub fn validate_user(&self, user: &User) -> Result<(), DomainError> {
            // 验证用户名
            if user.username.is_empty() {
                return Err(DomainError::InvalidUser("Username cannot be empty".to_string()));
            }
            
            // 验证邮箱
            if !user.email.contains('@') {
                return Err(DomainError::InvalidUser("Invalid email format".to_string()));
            }
            
            Ok(())
        }
    }
}

// 端口 - 定义应用与外部世界交互的契约
mod ports {
    use super::domain::*;
    use async_trait::async_trait;
    
    // 主端口 (应用向外提供的接口)
    #[async_trait]
    pub trait UserServicePort {
        async fn get_user(&self, id: UserId) -> Result<User, UserServiceError>;
        async fn create_user(&self, username: String, email: String) -> Result<User, UserServiceError>;
        async fn update_user(&self, id: UserId, username: Option<String>, email: Option<String>, active: Option<bool>) -> Result<User, UserServiceError>;
        async fn delete_user(&self, id: UserId) -> Result<(), UserServiceError>;
        async fn list_users(&self) -> Result<Vec<User>, UserServiceError>;
    }
    
    // 辅助端口 (应用需要外部提供的接口)
    #[async_trait]
    pub trait UserRepositoryPort {
        async fn find_by_id(&self, id: &UserId) -> Result<Option<User>, RepositoryError>;
        async fn save(&self, user: User) -> Result<(), RepositoryError>;
        async fn delete(&self, id: &UserId) -> Result<(), RepositoryError>;
        async fn find_all(&self) -> Result<Vec<User>, RepositoryError>;
    }
    
    #[async_trait]
    pub trait NotificationPort {
        async fn send_user_created_notification(&self, user: &User) -> Result<(), NotificationError>;
        async fn send_user_updated_notification(&self, user: &User) -> Result<(), NotificationError>;
    }
    
    // 错误类型
    #[derive(Debug, thiserror::Error)]
    pub enum UserServiceError {
        #[error("Domain error: {0}")]
        DomainError(#[from] DomainError),
        
        #[error("Repository error: {0}")]
        RepositoryError(#[from] RepositoryError),
        
        #[error("Notification error: {0}")]
        NotificationError(#[from] NotificationError),
    }
    
    #[derive(Debug, thiserror::Error)]
    pub enum RepositoryError {
        #[error("Entity not found: {0}")]
        NotFound(String),
        
        #[error("Database error: {0}")]
        DatabaseError(String),
        
        #[error("Connection error: {0}")]
        ConnectionError(String),
    }
    
    #[derive(Debug, thiserror::Error)]
    pub enum NotificationError {
        #[error("Failed to send notification: {0}")]
        SendFailed(String),
        
        #[error("Invalid notification: {0}")]
        Invalid(String),
    }
}

// 应用服务 - 使用端口实现业务逻辑
mod application {
    use super::domain::*;
    use super::ports::*;
    use async_trait::async_trait;
    use std::sync::Arc;
    
    pub struct UserService {
        user_repository: Arc<dyn UserRepositoryPort>,
        notification_service: Arc<dyn NotificationPort>,
        domain_service: UserDomainService,
    }
    
    impl UserService {
        pub fn new(
            user_repository: Arc<dyn UserRepositoryPort>,
            notification_service: Arc<dyn NotificationPort>,
        ) -> Self {
            Self {
                user_repository,
                notification_service,
                domain_service: UserDomainService,
            }
        }
    }
    
    #[async_trait]
    impl UserServicePort for UserService {
        async fn get_user(&self, id: UserId) -> Result<User, UserServiceError> {
            let user = self.user_repository.find_by_id(&id).await?
                .ok_or_else(|| DomainError::NotFound(id.0.clone()))?;
                
            Ok(user)
        }
        
        async fn create_user(&self, username: String, email: String) -> Result<User, UserServiceError> {
            let id = UserId(uuid::Uuid::new_v4().to_string());
            let user = User { id: id.clone(), username, email, active: true };
            
            // 验证用户
            self.domain_service.validate_user(&user)?;
            
            // 保存用户
            self.user_repository.save(user.clone()).await?;
            
            // 发送通知
            self.notification_service.send_user_created_notification(&user).await?;
            
            Ok(user)
        }
        
        async fn update_user(&self, id: UserId, username: Option<String>, email: Option<String>, active: Option<bool>) -> Result<User, UserServiceError> {
            // 获取现有用户
            let mut user = self.get_user(id.clone()).await?;
            
            // 更新字段
            if let Some(username) = username {
                user.username = username;
            }
            
            if let Some(email) = email {
                user.email = email;
            }
            
            if let Some(active) = active {
                user.active = active;
            }
            
            // 验证用户
            self.domain_service.validate_user(&user)?;
            
            // 保存用户
            self.user_repository.save(user.clone()).await?;
            
            // 发送通知
            self.notification_service.send_user_updated_notification(&user).await?;
            
            Ok(user)
        }
        
        async fn delete_user(&self, id: UserId) -> Result<(), UserServiceError> {
            // 检查用户是否存在
            self.get_user(id.clone()).await?;
            
            // 删除用户
            self.user_repository.delete(&id).await?;
            
            Ok(())
        }
        
        async fn list_users(&self) -> Result<Vec<User>, UserServiceError> {
            let users = self.user_repository.find_all().await?;
            Ok(users)
        }
    }
}

// 适配器 - 实现与外部系统的集成
mod adapters {
    use super::domain::*;
    use super::ports::*;
    use async_trait::async_trait;
    use std::collections::HashMap;
    use std::sync::{Arc, RwLock};
    
    // 持久化适配器 - 内存存储
    pub struct InMemoryUserRepository {
        users: RwLock<HashMap<String, User>>,
    }
    
    impl InMemoryUserRepository {
        pub fn new() -> Self {
            Self {
                users: RwLock::new(HashMap::new()),
            }
        }
    }
    
    #[async_trait]
    impl UserRepositoryPort for InMemoryUserRepository {
        async fn find_by_id(&self, id: &UserId) -> Result<Option<User>, RepositoryError> {
            let users = self.users.read()
                .map_err(|_| RepositoryError::DatabaseError("Failed to acquire read lock".to_string()))?;
                
            Ok(users.get(&id.0).cloned())
        }
        
        async fn save(&self, user: User) -> Result<(), RepositoryError> {
            let mut users = self.users.write()
                .map_err(|_| RepositoryError::DatabaseError("Failed to acquire write lock".to_string()))?;
                
            users.insert(user.id.0.clone(), user);
            Ok(())
        }
        
        async fn delete(&self, id: &UserId) -> Result<(), RepositoryError> {
            let mut users = self.users.write()
                .map_err(|_| RepositoryError::DatabaseError("Failed to acquire write lock".to_string()))?;
                
            users.remove(&id.0);
            Ok(())
        }
        
        async fn find_all(&self) -> Result<Vec<User>, RepositoryError> {
            let users = self.users.read()
                .map_err(|_| RepositoryError::DatabaseError("Failed to acquire read lock".to_string()))?;
                
            Ok(users.values().cloned().collect())
        }
    }
    
    // PostgreSQL 适配器
    pub struct PostgresUserRepository {
        pool: Arc<PgPool>,
    }
    
    impl PostgresUserRepository {
        pub fn new(pool: Arc<PgPool>) -> Self {
            Self { pool }
        }
    }
    
    #[async_trait]
    impl UserRepositoryPort for PostgresUserRepository {
        async fn find_by_id(&self, id: &UserId) -> Result<Option<User>, RepositoryError> {
            let record = sqlx::query!(
                "SELECT id, username, email, active FROM users WHERE id = $1",
                id.0
            )
            .fetch_optional(&*self.pool)
            .await
            .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
            
            match record {
                Some(r) => Ok(Some(User {
                    id: UserId(r.id),
                    username: r.username,
                    email: r.email,
                    active: r.active,
                })),
                None => Ok(None),
            }
        }
        
        async fn save(&self, user: User) -> Result<(), RepositoryError> {
            sqlx::query!(
                r#"
                INSERT INTO users (id, username, email, active)
                VALUES ($1, $2, $3, $4)
                ON CONFLICT (id) DO UPDATE
                SET username = $2, email = $3, active = $4
                "#,
                user.id.0,
                user.username,
                user.email,
                user.active
            )
            .execute(&*self.pool)
            .await
            .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
            
            Ok(())
        }
        
        async fn delete(&self, id: &UserId) -> Result<(), RepositoryError> {
            sqlx::query!("DELETE FROM users WHERE id = $1", id.0)
                .execute(&*self.pool)
                .await
                .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
                
            Ok(())
        }
        
        async fn find_all(&self) -> Result<Vec<User>, RepositoryError> {
            let records = sqlx::query!("SELECT id, username, email, active FROM users")
                .fetch_all(&*self.pool)
                .await
                .map_err(|e| RepositoryError::DatabaseError(e.to_string()))?;
                
            let users = records.into_iter()
                .map(|r| User {
                    id: UserId(r.id),
                    username: r.username,
                    email: r.email,
                    active: r.active,
                })
                .collect();
                
            Ok(users)
        }
    }
    
    // 通知适配器 - 邮件发送
    pub struct EmailNotificationService {
        email_client: Arc<EmailClient>,
    }
    
    impl EmailNotificationService {
        pub fn new(email_client: Arc<EmailClient>) -> Self {
            Self { email_client }
        }
    }
    
    #[async_trait]
    impl NotificationPort for EmailNotificationService {
        async fn send_user_created_notification(&self, user: &User) -> Result<(), NotificationError> {
            let email = Email {
                to: user.email.clone(),
                subject: "Welcome to our platform".to_string(),
                body: format!("Hello {}, your account has been created.", user.username),
            };
            
            self.email_client.send_email(email).await
                .map_err(|e| NotificationError::SendFailed(e.to_string()))
        }
        
        async fn send_user_updated_notification(&self, user: &User) -> Result<(), NotificationError> {
            let email = Email {
                to: user.email.clone(),
                subject: "Your account has been updated".to_string(),
                body: format!("Hello {}, your account details have been updated.", user.username),
            };
            
            self.email_client.send_email(email).await
                .map_err(|e| NotificationError::SendFailed(e.to_string()))
        }
    }
    
    // HTTP 适配器 - REST API
    pub struct UserApiController {
        user_service: Arc<dyn UserServicePort>,
    }
    
    impl UserApiController {
        pub fn new(user_service: Arc<dyn UserServicePort>) -> Self {
            Self { user_service }
        }
        
        pub fn routes(&self) -> Router {
            Router::new()
                .route("/api/users", get(self.list_users))
                .route("/api/users", post(self.create_user))
                .route("/api/users/:id", get(self.get_user))
                .route("/api/users/:id", put(self.update_user))
                .route("/api/users/:id", delete(self.delete_user))
        }
        
        async fn list_users(&self) -> Result<Json<Vec<UserResponse>>, ApiError> {
            let users = self.user_service.list_users().await?;
            let responses = users.into_iter().map(user_to_response).collect();
            Ok(Json(responses))
        }
        
        async fn get_user(&self, Path(id): Path<String>) -> Result<Json<UserResponse>, ApiError> {
            let user = self.user_service.get_user(UserId(id)).await?;
            Ok(Json(user_to_response(user)))
        }
        
        async fn create_user(&self, Json(req): Json<CreateUserRequest>) -> Result<Json<UserResponse>, ApiError> {
            let user = self.user_service.create_user(req.username, req.email).await?;
            Ok(Json(user_to_response(user)))
        }
        
        async fn update_user(&self, Path(id): Path<String>, Json(req): Json<UpdateUserRequest>) -> Result<Json<UserResponse>, ApiError> {
            let user = self.user_service.update_user(UserId(id), req.username, req.email, req.active).await?;
            Ok(Json(user_to_response(user)))
        }
        
        async fn delete_user(&self, Path(id): Path<String>) -> Result<StatusCode, ApiError> {
            self.user_service.delete_user(UserId(id)).await?;
            Ok(StatusCode::NO_CONTENT)
        }
    }
}
```

### 6.3 微服务架构模式

```rust
// 微服务基础设施
mod infrastructure {
    use async_trait::async_trait;
    use std::sync::Arc;
    
    // 服务发现接口
    #[async_trait]
    pub trait ServiceDiscovery: Send + Sync {
        async fn register_service(&self, service: ServiceInfo) -> Result<(), DiscoveryError>;
        async fn deregister_service(&self, service_id: &str) -> Result<(), DiscoveryError>;
        async fn discover_service(&self, service_name: &str) -> Result<Vec<ServiceInfo>, DiscoveryError>;
    }
    
    // 服务信息
    #[derive(Clone, Debug)]
    pub struct ServiceInfo {
        pub id: String,
        pub name: String,
        pub address: String,
        pub port: u16,
        pub health_check_url: String,
        pub tags: Vec<String>,
        pub metadata: HashMap<String, String>,
    }
    
    // 配置接口
    #[async_trait]
    pub trait ConfigProvider: Send + Sync {
        async fn get_config(&self, key: &str) -> Result<String, ConfigError>;
        async fn watch_config(&self, key: &str, callback: Arc<dyn Fn(String) + Send + Sync>) -> Result<WatchHandle, ConfigError>;
    }
    
    // 分布式跟踪接口
    pub trait Tracer: Send + Sync {
        fn start_span(&self, name: &str) -> Span;
        fn inject_context(&self, carrier: &mut dyn TracingCarrier);
        fn extract_context(&self, carrier: &dyn TracingCarrier) -> SpanContext;
    }
    
    // 熔断器接口
    pub trait CircuitBreaker: Send + Sync {
        fn execute<F, R, E>(&self, f: F) -> Result<R, CircuitBreakerError<E>>
        where
            F: FnOnce() -> Result<R, E>,
            E: std::error::Error;
    }
    
    // 消息代理接口
    #[async_trait]
    pub trait MessageBroker: Send + Sync {
        async fn publish<T: Serialize + Send>(&self, topic: &str, message: T) -> Result<(), MessageBrokerError>;
        async fn subscribe<T: DeserializeOwned + Send + 'static>(&self, topic: &str, handler: Box<dyn Fn(T) -> BoxF
# Rust 复杂设计模式与架构设计模式全面指南（续）

## 综合架构模式（续）

### 3. 微服务架构模式（续）

```rust
    // 消息代理接口
    #[async_trait]
    pub trait MessageBroker: Send + Sync {
        async fn publish<T: Serialize + Send>(&self, topic: &str, message: T) -> Result<(), MessageBrokerError>;
        async fn subscribe<T: DeserializeOwned + Send + 'static>(&self, topic: &str, handler: Box<dyn Fn(T) -> BoxFuture<'static, ()> + Send + Sync>) -> Result<SubscriptionHandle, MessageBrokerError>;
    }
    
    // 健康检查接口
    #[async_trait]
    pub trait HealthCheck: Send + Sync {
        async fn check_health(&self) -> HealthStatus;
    }
    
    #[derive(Debug, Clone, PartialEq)]
    pub enum HealthStatus {
        Healthy,
        Unhealthy { reason: String },
        Unknown,
    }
    
    // Consul 服务发现实现
    pub struct ConsulServiceDiscovery {
        client: Arc<ConsulClient>,
        agent_address: String,
    }
    
    impl ConsulServiceDiscovery {
        pub fn new(agent_address: &str) -> Self {
            let client = Arc::new(ConsulClient::new(agent_address));
            Self {
                client,
                agent_address: agent_address.to_string(),
            }
        }
    }
    
    #[async_trait]
    impl ServiceDiscovery for ConsulServiceDiscovery {
        async fn register_service(&self, service: ServiceInfo) -> Result<(), DiscoveryError> {
            let registration = AgentServiceRegistration {
                id: Some(service.id.clone()),
                name: service.name,
                address: Some(service.address),
                port: Some(service.port),
                check: Some(AgentServiceCheck {
                    http: Some(service.health_check_url),
                    interval: Some("10s".to_string()),
                    timeout: Some("5s".to_string()),
                    ..Default::default()
                }),
                tags: Some(service.tags),
                meta: Some(service.metadata),
                ..Default::default()
            };
            
            self.client.agent().register(registration).await
                .map_err(|e| DiscoveryError::RegistrationFailed(e.to_string()))
        }
        
        async fn deregister_service(&self, service_id: &str) -> Result<(), DiscoveryError> {
            self.client.agent().deregister(service_id).await
                .map_err(|e| DiscoveryError::DeregistrationFailed(e.to_string()))
        }
        
        async fn discover_service(&self, service_name: &str) -> Result<Vec<ServiceInfo>, DiscoveryError> {
            let services = self.client.catalog().services().await
                .map_err(|e| DiscoveryError::DiscoveryFailed(e.to_string()))?;
                
            if let Some(service_entries) = services.get(service_name) {
                let mut result = Vec::new();
                
                for entry in service_entries {
                    let node_services = self.client.catalog().get_service(service_name, entry).await
                        .map_err(|e| DiscoveryError::DiscoveryFailed(e.to_string()))?;
                        
                    for node_service in node_services {
                        let service_info = ServiceInfo {
                            id: node_service.service_id,
                            name: node_service.service_name,
                            address: node_service.service_address,
                            port: node_service.service_port,
                            health_check_url: format!("http://{}:{}/health", node_service.service_address, node_service.service_port),
                            tags: node_service.service_tags,
                            metadata: node_service.service_meta,
                        };
                        
                        result.push(service_info);
                    }
                }
                
                Ok(result)
            } else {
                Ok(Vec::new())
            }
        }
    }
    
    // Kafka 消息代理实现
    pub struct KafkaMessageBroker {
        producer: Arc<FutureProducer>,
        consumer_config: ClientConfig,
    }
    
    impl KafkaMessageBroker {
        pub fn new(bootstrap_servers: &str, client_id: &str) -> Result<Self, MessageBrokerError> {
            let producer: FutureProducer = ClientConfig::new()
                .set("bootstrap.servers", bootstrap_servers)
                .set("client.id", client_id)
                .set("message.timeout.ms", "5000")
                .create()
                .map_err(|e| MessageBrokerError::ConnectionFailed(e.to_string()))?;
                
            let consumer_config = ClientConfig::new()
                .set("bootstrap.servers", bootstrap_servers)
                .set("client.id", client_id)
                .set("group.id", client_id)
                .set("enable.auto.commit", "true")
                .set("auto.offset.reset", "earliest");
                
            Ok(Self {
                producer: Arc::new(producer),
                consumer_config,
            })
        }
    }
    
    #[async_trait]
    impl MessageBroker for KafkaMessageBroker {
        async fn publish<T: Serialize + Send>(&self, topic: &str, message: T) -> Result<(), MessageBrokerError> {
            let payload = serde_json::to_vec(&message)
                .map_err(|e| MessageBrokerError::SerializationFailed(e.to_string()))?;
                
            let record = FutureRecord::to(topic)
                .payload(&payload);
                
            self.producer.send(record, Duration::from_secs(0)).await
                .map(|_| ())
                .map_err(|(e, _)| MessageBrokerError::PublishFailed(e.to_string()))
        }
        
        async fn subscribe<T: DeserializeOwned + Send + 'static>(&self, topic: &str, handler: Box<dyn Fn(T) -> BoxFuture<'static, ()> + Send + Sync>) -> Result<SubscriptionHandle, MessageBrokerError> {
            let consumer: StreamConsumer = self.consumer_config.clone()
                .create()
                .map_err(|e| MessageBrokerError::ConnectionFailed(e.to_string()))?;
                
            consumer.subscribe(&[topic])
                .map_err(|e| MessageBrokerError::SubscriptionFailed(e.to_string()))?;
                
            let subscription_id = Uuid::new_v4().to_string();
            
            // 启动消费任务
            let handle = tokio::spawn(async move {
                let mut stream = consumer.stream();
                
                while let Some(message) = stream.next().await {
                    match message {
                        Ok(msg) => {
                            if let Some(payload) = msg.payload() {
                                match serde_json::from_slice::<T>(payload) {
                                    Ok(deserialized) => {
                                        handler(deserialized).await;
                                    },
                                    Err(e) => {
                                        eprintln!("Failed to deserialize message: {}", e);
                                    }
                                }
                            }
                        },
                        Err(e) => {
                            eprintln!("Error while consuming from Kafka: {}", e);
                        }
                    }
                }
            });
            
            Ok(SubscriptionHandle { id: subscription_id, handle: Some(handle) })
        }
    }

    // 分布式追踪实现 (Jaeger)
    pub struct JaegerTracer {
        tracer: opentelemetry_jaeger::Tracer,
    }
    
    impl JaegerTracer {
        pub fn new(service_name: &str, agent_endpoint: &str) -> Result<Self, TracerError> {
            let tracer = opentelemetry_jaeger::new_pipeline()
                .with_service_name(service_name)
                .with_agent_endpoint(agent_endpoint)
                .install_batch(opentelemetry::runtime::Tokio)
                .map_err(|e| TracerError::InitializationFailed(e.to_string()))?;
                
            Ok(Self { tracer })
        }
    }
    
    impl Tracer for JaegerTracer {
        fn start_span(&self, name: &str) -> Span {
            self.tracer.start(name)
        }
        
        fn inject_context(&self, carrier: &mut dyn TracingCarrier) {
            let context = self.tracer.context();
            let propagator = TraceContextPropagator::new();
            propagator.inject_context(&context, carrier);
        }
        
        fn extract_context(&self, carrier: &dyn TracingCarrier) -> SpanContext {
            let propagator = TraceContextPropagator::new();
            propagator.extract(carrier)
        }
    }
}

// 用户服务微服务
mod user_service {
    use super::infrastructure::*;
    use async_trait::async_trait;
    use std::sync::Arc;
    
    // 用户领域模型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct User {
        pub id: String,
        pub username: String,
        pub email: String,
        pub created_at: DateTime<Utc>,
        pub updated_at: DateTime<Utc>,
    }
    
    // 用户仓储接口
    #[async_trait]
    pub trait UserRepository: Send + Sync {
        async fn find_by_id(&self, id: &str) -> Result<Option<User>, RepositoryError>;
        async fn find_by_username(&self, username: &str) -> Result<Option<User>, RepositoryError>;
        async fn save(&self, user: User) -> Result<User, RepositoryError>;
        async fn delete(&self, id: &str) -> Result<(), RepositoryError>;
        async fn find_all(&self, page: usize, page_size: usize) -> Result<(Vec<User>, usize), RepositoryError>;
    }
    
    // 用户事件
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum UserEvent {
        UserCreated(User),
        UserUpdated(User),
        UserDeleted { id: String },
    }
    
    // 用户服务接口
    #[async_trait]
    pub trait UserService: Send + Sync {
        async fn get_user(&self, id: &str) -> Result<User, UserServiceError>;
        async fn create_user(&self, username: String, email: String) -> Result<User, UserServiceError>;
        async fn update_user(&self, id: &str, username: Option<String>, email: Option<String>) -> Result<User, UserServiceError>;
        async fn delete_user(&self, id: &str) -> Result<(), UserServiceError>;
        async fn list_users(&self, page: usize, page_size: usize) -> Result<(Vec<User>, usize), UserServiceError>;
    }
    
    // 用户服务实现
    pub struct UserServiceImpl {
        repository: Arc<dyn UserRepository>,
        message_broker: Arc<dyn MessageBroker>,
        tracer: Arc<dyn Tracer>,
        circuit_breaker: Arc<dyn CircuitBreaker>,
    }
    
    impl UserServiceImpl {
        pub fn new(
            repository: Arc<dyn UserRepository>,
            message_broker: Arc<dyn MessageBroker>,
            tracer: Arc<dyn Tracer>,
            circuit_breaker: Arc<dyn CircuitBreaker>,
        ) -> Self {
            Self {
                repository,
                message_broker,
                tracer,
                circuit_breaker,
            }
        }
    }
    
    #[async_trait]
    impl UserService for UserServiceImpl {
        async fn get_user(&self, id: &str) -> Result<User, UserServiceError> {
            let span = self.tracer.start_span("user_service.get_user");
            let _guard = span.enter();
            
            // 使用断路器执行操作
            let result = self.circuit_breaker.execute(move || {
                async move {
                    self.repository.find_by_id(id).await
                        .map_err(UserServiceError::from)
                }
            }).await?;
            
            match result {
                Some(user) => Ok(user),
                None => Err(UserServiceError::NotFound(format!("User not found: {}", id))),
            }
        }
        
        async fn create_user(&self, username: String, email: String) -> Result<User, UserServiceError> {
            let span = self.tracer.start_span("user_service.create_user");
            let _guard = span.enter();
            
            // 检查用户名是否已存在
            if let Some(_) = self.repository.find_by_username(&username).await? {
                return Err(UserServiceError::AlreadyExists(format!("Username already taken: {}", username)));
            }
            
            // 创建新用户
            let now = Utc::now();
            let user = User {
                id: Uuid::new_v4().to_string(),
                username,
                email,
                created_at: now,
                updated_at: now,
            };
            
            // 保存用户
            let saved_user = self.repository.save(user.clone()).await?;
            
            // 发布事件
            self.message_broker.publish("user-events", UserEvent::UserCreated(saved_user.clone())).await?;
            
            Ok(saved_user)
        }
        
        async fn update_user(&self, id: &str, username: Option<String>, email: Option<String>) -> Result<User, UserServiceError> {
            let span = self.tracer.start_span("user_service.update_user");
            let _guard = span.enter();
            
            // 获取现有用户
            let mut user = self.get_user(id).await?;
            
            // 更新字段
            if let Some(username) = username {
                // 检查新用户名是否已被占用
                if let Some(existing) = self.repository.find_by_username(&username).await? {
                    if existing.id != user.id {
                        return Err(UserServiceError::AlreadyExists(format!("Username already taken: {}", username)));
                    }
                }
                user.username = username;
            }
            
            if let Some(email) = email {
                user.email = email;
            }
            
            // 更新时间戳
            user.updated_at = Utc::now();
            
            // 保存用户
            let updated_user = self.repository.save(user).await?;
            
            // 发布事件
            self.message_broker.publish("user-events", UserEvent::UserUpdated(updated_user.clone())).await?;
            
            Ok(updated_user)
        }
        
        async fn delete_user(&self, id: &str) -> Result<(), UserServiceError> {
            let span = self.tracer.start_span("user_service.delete_user");
            let _guard = span.enter();
            
            // 检查用户是否存在
            let _ = self.get_user(id).await?;
            
            // 删除用户
            self.repository.delete(id).await?;
            
            // 发布事件
            self.message_broker.publish("user-events", UserEvent::UserDeleted { id: id.to_string() }).await?;
            
            Ok(())
        }
        
        async fn list_users(&self, page: usize, page_size: usize) -> Result<(Vec<User>, usize), UserServiceError> {
            let span = self.tracer.start_span("user_service.list_users");
            let _guard = span.enter();
            
            let result = self.repository.find_all(page, page_size).await?;
            Ok(result)
        }
    }
    
    // 用户服务 gRPC API
    pub struct UserGrpcService {
        user_service: Arc<dyn UserService>,
    }
    
    #[tonic::async_trait]
    impl user_proto::user_service_server::UserService for UserGrpcService {
        async fn get_user(&self, request: tonic::Request<user_proto::GetUserRequest>) -> Result<tonic::Response<user_proto::UserResponse>, tonic::Status> {
            let req = request.into_inner();
            
            match self.user_service.get_user(&req.id).await {
                Ok(user) => {
                    let response = user_proto::UserResponse {
                        id: user.id,
                        username: user.username,
                        email: user.email,
                        created_at: Some(prost_types::Timestamp::from(user.created_at)),
                        updated_at: Some(prost_types::Timestamp::from(user.updated_at)),
                    };
                    
                    Ok(tonic::Response::new(response))
                },
                Err(e) => {
                    Err(tonic::Status::from_error(Box::new(e)))
                }
            }
        }
        
        async fn create_user(&self, request: tonic::Request<user_proto::CreateUserRequest>) -> Result<tonic::Response<user_proto::UserResponse>, tonic::Status> {
            let req = request.into_inner();
            
            match self.user_service.create_user(req.username, req.email).await {
                Ok(user) => {
                    let response = user_proto::UserResponse {
                        id: user.id,
                        username: user.username,
                        email: user.email,
                        created_at: Some(prost_types::Timestamp::from(user.created_at)),
                        updated_at: Some(prost_types::Timestamp::from(user.updated_at)),
                    };
                    
                    Ok(tonic::Response::new(response))
                },
                Err(e) => {
                    Err(tonic::Status::from_error(Box::new(e)))
                }
            }
        }
        
        // 其他 RPC 方法实现...
    }
}

// 订单服务微服务
mod order_service {
    use super::infrastructure::*;
    use super::user_service::User;
    use async_trait::async_trait;
    use std::sync::Arc;
    
    // 订单领域模型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct Order {
        pub id: String,
        pub user_id: String,
        pub items: Vec<OrderItem>,
        pub total_amount: Decimal,
        pub status: OrderStatus,
        pub created_at: DateTime<Utc>,
        pub updated_at: DateTime<Utc>,
    }
    
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct OrderItem {
        pub product_id: String,
        pub quantity: u32,
        pub price: Decimal,
    }
    
    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
    pub enum OrderStatus {
        Created,
        Paid,
        Shipped,
        Delivered,
        Canceled,
    }
    
    // 订单仓储接口
    #[async_trait]
    pub trait OrderRepository: Send + Sync {
        async fn find_by_id(&self, id: &str) -> Result<Option<Order>, RepositoryError>;
        async fn find_by_user_id(&self, user_id: &str) -> Result<Vec<Order>, RepositoryError>;
        async fn save(&self, order: Order) -> Result<Order, RepositoryError>;
        async fn update_status(&self, id: &str, status: OrderStatus) -> Result<Order, RepositoryError>;
    }
    
    // 用户服务客户端
    #[async_trait]
    pub trait UserServiceClient: Send + Sync {
        async fn get_user(&self, id: &str) -> Result<User, ServiceError>;
    }
    
    // gRPC 用户服务客户端实现
    pub struct UserServiceGrpcClient {
        client: user_proto::user_service_client::UserServiceClient<tonic::transport::Channel>,
        circuit_breaker: Arc<dyn CircuitBreaker>,
    }
    
    impl UserServiceGrpcClient {
        pub async fn new(address: &str, circuit_breaker: Arc<dyn CircuitBreaker>) -> Result<Self, ServiceError> {
            let client = user_proto::user_service_client::UserServiceClient::connect(address.to_string())
                .await
                .map_err(|e| ServiceError::ConnectionFailed(e.to_string()))?;
                
            Ok(Self {
                client,
                circuit_breaker,
            })
        }
    }
    
    #[async_trait]
    impl UserServiceClient for UserServiceGrpcClient {
        async fn get_user(&self, id: &str) -> Result<User, ServiceError> {
            let mut client = self.client.clone();
            
            // 使用断路器执行远程调用
            let result = self.circuit_breaker.execute(move || {
                async move {
                    let request = tonic::Request::new(user_proto::GetUserRequest {
                        id: id.to_string(),
                    });
                    
                    let response = client.get_user(request).await
                        .map_err(|e| ServiceError::RemoteCallFailed(e.to_string()))?;
                        
                    let user_proto = response.into_inner();
                    
                    let created_at = user_proto.created_at
                        .ok_or_else(|| ServiceError::InvalidResponse("Missing created_at".to_string()))?
                        .into();
                        
                    let updated_at = user_proto.updated_at
                        .ok_or_else(|| ServiceError::InvalidResponse("Missing updated_at".to_string()))?
                        .into();
                        
                    let user = User {
                        id: user_proto.id,
                        username: user_proto.username,
                        email: user_proto.email,
                        created_at,
                        updated_at,
                    };
                    
                    Ok(user)
                }
            }).await?;
            
            Ok(result)
        }
    }
    
    // 订单事件
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum OrderEvent {
        OrderCreated(Order),
        OrderStatusChanged { id: String, old_status: OrderStatus, new_status: OrderStatus },
    }
    
    // 订单服务接口
    #[async_trait]
    pub trait OrderService: Send + Sync {
        async fn create_order(&self, user_id: &str, items: Vec<OrderItem>) -> Result<Order, OrderServiceError>;
        async fn get_order(&self, id: &str) -> Result<Order, OrderServiceError>;
        async fn get_user_orders(&self, user_id: &str) -> Result<Vec<Order>, OrderServiceError>;
        async fn update_order_status(&self, id: &str, status: OrderStatus) -> Result<Order, OrderServiceError>;
    }
    
    // 用户事件处理器
    pub struct UserEventHandler {
        repository: Arc<dyn OrderRepository>,
    }
    
    impl UserEventHandler {
        pub fn new(repository: Arc<dyn OrderRepository>) -> Self {
            Self { repository }
        }
        
        pub async fn handle_user_event(&self, event: user_service::UserEvent) {
            match event {
                user_service::UserEvent::UserDeleted { id } => {
                    // 当用户被删除时，将其所有订单标记为取消
                    match self.repository.find_by_user_id(&id).await {
                        Ok(orders) => {
                            for order in orders {
                                if order.status != OrderStatus::Canceled {
                                    if let Err(e) = self.repository.update_status(&order.id, OrderStatus::Canceled).await {
                                        log::error!("Failed to cancel order {} after user deletion: {}", order.id, e);
                                    }
                                }
                            }
                        },
                        Err(e) => {
                            log::error!("Failed to find orders for deleted user {}: {}", id, e);
                        }
                    }
                },
                // 处理其他用户事件...
                _ => {}
            }
        }
    }
}
```

### 6.4 事件驱动架构

```rust
// 事件驱动基础设施
mod event_infrastructure {
    use async_trait::async_trait;
    use std::sync::Arc;
    
    // 事件接口
    pub trait Event: Send + Sync + Clone + 'static {
        fn event_type(&self) -> &'static str;
        fn timestamp(&self) -> DateTime<Utc>;
    }
    
    // 事件头部信息
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct EventMetadata {
        pub event_id: String,
        pub event_type: String,
        pub timestamp: DateTime<Utc>,
        pub correlation_id: Option<String>,
        pub causation_id: Option<String>,
        pub source: String,
    }
    
    // 包装的事件
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct EnvelopedEvent<T> {
        pub metadata: EventMetadata,
        pub payload: T,
    }
    
    impl<T> EnvelopedEvent<T> {
        pub fn new(event_type: &str, source: &str, payload: T) -> Self {
            Self {
                metadata: EventMetadata {
                    event_id: Uuid::new_v4().to_string(),
                    event_type: event_type.to_string(),
                    timestamp: Utc::now(),
                    correlation_id: None,
                    causation_id: None,
                    source: source.to_string(),
                },
                payload,
            }
        }
        
        pub fn with_correlation_id(mut self, correlation_id: &str) -> Self {
            self.metadata.correlation_id = Some(correlation_id.to_string());
            self
        }
        
        pub fn with_causation_id(mut self, causation_id: &str) -> Self {
            self.metadata.causation_id = Some(causation_id.to_string());
            self
        }
    }
    
    // 事件发布器
    #[async_trait]
    pub trait EventPublisher: Send + Sync {
        async fn publish<T: Serialize + Send + Sync>(&self, event: EnvelopedEvent<T>) -> Result<(), EventPublishError>;
    }
    
    // 事件订阅器
    #[async_trait]
    pub trait EventSubscriber: Send + Sync {
        async fn subscribe<T: DeserializeOwned + Send + Sync + 'static>(&self, event_type: &str, handler: Box<dyn Fn(EnvelopedEvent<T>) -> BoxFuture<'static, ()> + Send + Sync>) -> Result<SubscriptionHandle, EventSubscribeError>;
    }
    
    // Kafka 事件总线
    pub struct KafkaEventBus {
        producer: Arc<FutureProducer>,
        consumer_config: ClientConfig,
        topic_prefix: String,
    }
    
    impl KafkaEventBus {
        pub fn new(bootstrap_servers: &str, client_id: &str, topic_prefix: &str) -> Result<Self, EventBusError> {
            let producer: FutureProducer = ClientConfig::new()
                .set("bootstrap.servers", bootstrap_servers)
                .set("client.id", format!("{}-producer", client_id))
                .set("message.timeout.ms", "5000")
                .create()
                .map_err(|e| EventBusError::ConnectionFailed(e.to_string()))?;
                
            let consumer_config = ClientConfig::new()
                .set("bootstrap.servers", bootstrap_servers)
                .set("client.id", format!("{}-consumer", client_id))
                .set("group.id", client_id)
                .set("enable.auto.commit", "true")
                .set("auto.offset.reset", "earliest");
                
            Ok(Self {
                producer: Arc::new(producer),
                consumer_config,
                topic_prefix: topic_prefix.to_string(),
            })
        }
        
        fn get_topic_name(&self, event_type: &str) -> String {
            format!("{}.{}", self.topic_prefix, event_type)
        }
    }
    
    #[async_trait]
    impl EventPublisher for KafkaEventBus {
        async fn publish<T: Serialize + Send + Sync>(&self, event: EnvelopedEvent<T>) -> Result<(), EventPublishError> {
            let topic = self.get_topic_name(&event.metadata.event_type);
            
            let payload = serde_json::to_vec(&event)
                .map_err(|e| EventPublishError::SerializationFailed(e.to_string()))?;
                
            let record = FutureRecord::to(&topic)
                .key(&event.metadata.event_id)
                .payload(&payload);
                
            self.producer.send(record, Duration::from_secs(0)).await
                .map(|_| ())
                .map_err(|(e, _)| EventPublishError::PublishFailed(e.to_string()))
        }
    }
    
    #[async_trait]
    impl EventSubscriber for KafkaEventBus {
        async fn subscribe<T: DeserializeOwned + Send + Sync + 'static>(&self, event_type: &str, handler: Box<dyn Fn(EnvelopedEvent<T>) -> BoxFuture<'static, ()> + Send + Sync>) -> Result<SubscriptionHandle, EventSubscribeError> {
            let topic = self.get_topic_name(event_type);
            
            let consumer: StreamConsumer = self.consumer_config.clone()
                .create()
                .map_err(|e| EventSubscribeError::ConnectionFailed(e.to_string()))?;
# Rust 复杂设计模式与架构设计模式全面指南（续）

## 综合架构模式（续）

### 4. 事件驱动架构（续）

```rust
    #[async_trait]
    impl EventSubscriber for KafkaEventBus {
        async fn subscribe<T: DeserializeOwned + Send + Sync + 'static>(&self, event_type: &str, handler: Box<dyn Fn(EnvelopedEvent<T>) -> BoxFuture<'static, ()> + Send + Sync>) -> Result<SubscriptionHandle, EventSubscribeError> {
            let topic = self.get_topic_name(event_type);
            
            let consumer: StreamConsumer = self.consumer_config.clone()
                .create()
                .map_err(|e| EventSubscribeError::ConnectionFailed(e.to_string()))?;
                
            consumer.subscribe(&[&topic])
                .map_err(|e| EventSubscribeError::SubscriptionFailed(e.to_string()))?;
                
            let subscription_id = Uuid::new_v4().to_string();
            
            // 启动消费任务
            let handle = tokio::spawn(async move {
                let mut stream = consumer.stream();
                
                while let Some(message) = stream.next().await {
                    match message {
                        Ok(msg) => {
                            if let Some(payload) = msg.payload() {
                                match serde_json::from_slice::<EnvelopedEvent<T>>(payload) {
                                    Ok(event) => {
                                        handler(event).await;
                                    },
                                    Err(e) => {
                                        log::error!("Failed to deserialize event: {}", e);
                                    }
                                }
                            }
                            
                            // 手动提交 offset
                            if let Err(e) = consumer.commit_message(&msg, CommitMode::Async) {
                                log::error!("Failed to commit offset: {}", e);
                            }
                        },
                        Err(e) => {
                            log::error!("Error while consuming from Kafka: {}", e);
                        }
                    }
                }
            });
            
            Ok(SubscriptionHandle { id: subscription_id, handle: Some(handle) })
        }
    }
    
    // 事件存储
    #[async_trait]
    pub trait EventStore: Send + Sync {
        async fn append_events<T: Serialize + Send + Sync>(&self, stream_id: &str, expected_version: Option<u64>, events: Vec<EnvelopedEvent<T>>) -> Result<u64, EventStoreError>;
        async fn read_stream<T: DeserializeOwned + Send + Sync>(&self, stream_id: &str, start: u64, count: Option<usize>) -> Result<Vec<EnvelopedEvent<T>>, EventStoreError>;
        async fn read_all<T: DeserializeOwned + Send + Sync>(&self, start: u64, count: Option<usize>) -> Result<Vec<EnvelopedEvent<T>>, EventStoreError>;
    }
    
    // 事件处理器
    pub trait EventHandler<T: DeserializeOwned + Send + Sync>: Send + Sync {
        fn handle(&self, event: EnvelopedEvent<T>) -> BoxFuture<'static, Result<(), EventHandlerError>>;
    }
    
    // 事件处理器注册表
    pub struct EventHandlerRegistry {
        handlers: RwLock<HashMap<String, Vec<Box<dyn Fn(Vec<u8>) -> BoxFuture<'static, Result<(), EventHandlerError>> + Send + Sync>>>>,
    }
    
    impl EventHandlerRegistry {
        pub fn new() -> Self {
            Self {
                handlers: RwLock::new(HashMap::new()),
            }
        }
        
        pub fn register<T, H>(&self, event_type: &str, handler: H)
        where
            T: DeserializeOwned + Send + Sync + 'static,
            H: EventHandler<T> + 'static,
        {
            let mut handlers = self.handlers.write().unwrap();
            
            let boxed_handler = Box::new(move |payload: Vec<u8>| {
                let handler = handler.clone();
                Box::pin(async move {
                    let event = serde_json::from_slice::<EnvelopedEvent<T>>(&payload)
                        .map_err(|e| EventHandlerError::DeserializationFailed(e.to_string()))?;
                        
                    handler.handle(event).await
                }) as BoxFuture<'static, Result<(), EventHandlerError>>
            });
            
            handlers.entry(event_type.to_string())
                .or_insert_with(Vec::new)
                .push(boxed_handler);
        }
        
        pub async fn dispatch(&self, event_type: &str, payload: Vec<u8>) -> Result<(), EventHandlerError> {
            let handlers = {
                let handlers_map = self.handlers.read().unwrap();
                handlers_map.get(event_type)
                    .cloned()
                    .unwrap_or_default()
            };
            
            for handler in handlers {
                handler(payload.clone()).await?;
            }
            
            Ok(())
        }
    }
}

// 命令查询职责分离 (CQRS) 与事件溯源
mod cqrs_eventsourcing {
    use super::event_infrastructure::*;
    use async_trait::async_trait;
    use std::sync::Arc;
    
    // 聚合根接口
    pub trait AggregateRoot: Send + Sync {
        type Id: ToString + Send + Sync;
        type State: Default + Clone + Send + Sync;
        type Event: Serialize + DeserializeOwned + Clone + Send + Sync;
        type Command;
        type Error: std::error::Error + Send + Sync;
        
        fn id(&self) -> &Self::Id;
        fn version(&self) -> u64;
        fn state(&self) -> &Self::State;
        
        fn handle_command(&self, command: Self::Command) -> Result<Vec<Self::Event>, Self::Error>;
        fn apply_event(&mut self, event: Self::Event);
    }
    
    // 事件溯源存储库
    pub struct EventSourcedRepository<A, T, S>
    where
        A: AggregateRoot<Event = T>,
        T: Serialize + DeserializeOwned + Clone + Send + Sync + 'static,
        S: EventStore,
    {
        event_store: S,
        event_publisher: Arc<dyn EventPublisher>,
        _marker: PhantomData<A>,
    }
    
    impl<A, T, S> EventSourcedRepository<A, T, S>
    where
        A: AggregateRoot<Event = T>,
        T: Serialize + DeserializeOwned + Clone + Send + Sync + 'static,
        S: EventStore,
    {
        pub fn new(event_store: S, event_publisher: Arc<dyn EventPublisher>) -> Self {
            Self {
                event_store,
                event_publisher,
                _marker: PhantomData,
            }
        }
        
        pub async fn load(&self, id: &A::Id) -> Result<Option<A>, RepositoryError> {
            let stream_id = format!("{}-{}", std::any::type_name::<A>(), id.to_string());
            
            // 从事件流中读取所有事件
            let events = self.event_store.read_stream::<T>(&stream_id, 0, None).await
                .map_err(|e| RepositoryError::EventStoreError(e.to_string()))?;
                
            if events.is_empty() {
                return Ok(None);
            }
            
            // 重构聚合根
            let mut aggregate = A::default();
            
            for event in events {
                aggregate.apply_event(event.payload);
            }
            
            Ok(Some(aggregate))
        }
        
        pub async fn save(&self, aggregate: &A, events: Vec<T>) -> Result<(), RepositoryError> {
            if events.is_empty() {
                return Ok(());
            }
            
            let stream_id = format!("{}-{}", std::any::type_name::<A>(), aggregate.id().to_string());
            
            // 包装事件
            let enveloped_events: Vec<_> = events.into_iter()
                .map(|event| {
                    EnvelopedEvent::new(
                        std::any::type_name::<T>(),
                        std::any::type_name::<A>(),
                        event
                    )
                })
                .collect();
                
            // 追加到事件流
            self.event_store.append_events(&stream_id, Some(aggregate.version()), enveloped_events.clone()).await
                .map_err(|e| RepositoryError::EventStoreError(e.to_string()))?;
                
            // 发布事件
            for event in enveloped_events {
                self.event_publisher.publish(event).await
                    .map_err(|e| RepositoryError::EventPublishError(e.to_string()))?;
            }
            
            Ok(())
        }
    }
    
    // 命令处理器
    #[async_trait]
    pub trait CommandHandler<C, A>: Send + Sync
    where
        A: AggregateRoot,
    {
        async fn handle(&self, command: C) -> Result<(), CommandHandlerError<A::Error>>;
    }
    
    // 命令总线
    pub struct CommandBus {
        handlers: RwLock<HashMap<TypeId, Box<dyn Fn(Box<dyn Any>) -> BoxFuture<'static, Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send + Sync>>>,
    }
    
    impl CommandBus {
        pub fn new() -> Self {
            Self {
                handlers: RwLock::new(HashMap::new()),
            }
        }
        
        pub fn register<C, H, A>(&self, handler: H)
        where
            C: 'static + Send + Sync,
            H: CommandHandler<C, A> + 'static,
            A: AggregateRoot + 'static,
        {
            let type_id = TypeId::of::<C>();
            
            let boxed_handler = Box::new(move |command: Box<dyn Any>| {
                let handler = handler.clone();
                let command = *command.downcast::<C>().expect("Command type mismatch");
                
                Box::pin(async move {
                    handler.handle(command).await
                        .map_err(|e| Box::new(e) as Box<dyn std::error::Error + Send + Sync>)
                }) as BoxFuture<'static, Result<(), Box<dyn std::error::Error + Send + Sync>>>
            });
            
            let mut handlers = self.handlers.write().unwrap();
            handlers.insert(type_id, boxed_handler);
        }
        
        pub async fn dispatch<C: 'static + Send + Sync>(&self, command: C) -> Result<(), CommandBusError> {
            let type_id = TypeId::of::<C>();
            
            let handler = {
                let handlers = self.handlers.read().unwrap();
                handlers.get(&type_id)
                    .cloned()
                    .ok_or_else(|| CommandBusError::HandlerNotFound(std::any::type_name::<C>().to_string()))?
            };
            
            let boxed_command = Box::new(command);
            
            handler(boxed_command).await
                .map_err(|e| CommandBusError::HandlerError(e.to_string()))
        }
    }
    
    // 查询模型
    pub struct QueryModel<T> {
        data: Arc<RwLock<T>>,
    }
    
    impl<T: Default + Clone + Send + Sync + 'static> QueryModel<T> {
        pub fn new() -> Self {
            Self {
                data: Arc::new(RwLock::new(T::default())),
            }
        }
        
        pub fn read<R, F>(&self, f: F) -> Result<R, QueryModelError>
        where
            F: FnOnce(&T) -> R,
        {
            let data = self.data.read()
                .map_err(|_| QueryModelError::LockError("Failed to acquire read lock".to_string()))?;
                
            Ok(f(&data))
        }
        
        pub fn update<F>(&self, f: F) -> Result<(), QueryModelError>
        where
            F: FnOnce(&mut T),
        {
            let mut data = self.data.write()
                .map_err(|_| QueryModelError::LockError("Failed to acquire write lock".to_string()))?;
                
            f(&mut data);
            Ok(())
        }
    }
    
    // 投影器 - 将事件应用到查询模型
    #[async_trait]
    pub trait Projector<E, T>: Send + Sync
    where
        E: DeserializeOwned + Send + Sync + 'static,
        T: Default + Clone + Send + Sync + 'static,
    {
        fn query_model(&self) -> &QueryModel<T>;
        
        async fn handle_event(&self, event: EnvelopedEvent<E>) -> Result<(), ProjectorError>;
        
        async fn rebuild(&self, event_store: &dyn EventStore) -> Result<(), ProjectorError>;
    }
    
    // 银行账户聚合根示例
    #[derive(Default, Clone)]
    pub struct BankAccount {
        id: String,
        owner: String,
        balance: Decimal,
        version: u64,
        is_closed: bool,
    }
    
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub enum BankAccountEvent {
        AccountCreated { id: String, owner: String },
        MoneyDeposited { amount: Decimal },
        MoneyWithdrawn { amount: Decimal },
        AccountClosed,
    }
    
    #[derive(Debug)]
    pub enum BankAccountCommand {
        CreateAccount { id: String, owner: String },
        Deposit { amount: Decimal },
        Withdraw { amount: Decimal },
        CloseAccount,
    }
    
    #[derive(Debug, thiserror::Error)]
    pub enum BankAccountError {
        #[error("Account already exists")]
        AccountAlreadyExists,
        
        #[error("Insufficient funds: requested {requested}, available {available}")]
        InsufficientFunds { requested: Decimal, available: Decimal },
        
        #[error("Account is closed")]
        AccountClosed,
        
        #[error("Invalid operation: {0}")]
        InvalidOperation(String),
    }
    
    impl AggregateRoot for BankAccount {
        type Id = String;
        type State = Self;
        type Event = BankAccountEvent;
        type Command = BankAccountCommand;
        type Error = BankAccountError;
        
        fn id(&self) -> &Self::Id {
            &self.id
        }
        
        fn version(&self) -> u64 {
            self.version
        }
        
        fn state(&self) -> &Self::State {
            self
        }
        
        fn handle_command(&self, command: Self::Command) -> Result<Vec<Self::Event>, Self::Error> {
            match command {
                BankAccountCommand::CreateAccount { id, owner } => {
                    // 检查账户是否已存在
                    if !self.id.is_empty() {
                        return Err(BankAccountError::AccountAlreadyExists);
                    }
                    
                    Ok(vec![BankAccountEvent::AccountCreated { id, owner }])
                },
                BankAccountCommand::Deposit { amount } => {
                    // 检查账户是否已关闭
                    if self.is_closed {
                        return Err(BankAccountError::AccountClosed);
                    }
                    
                    // 验证金额
                    if amount <= Decimal::ZERO {
                        return Err(BankAccountError::InvalidOperation("Deposit amount must be positive".to_string()));
                    }
                    
                    Ok(vec![BankAccountEvent::MoneyDeposited { amount }])
                },
                BankAccountCommand::Withdraw { amount } => {
                    // 检查账户是否已关闭
                    if self.is_closed {
                        return Err(BankAccountError::AccountClosed);
                    }
                    
                    // 验证金额
                    if amount <= Decimal::ZERO {
                        return Err(BankAccountError::InvalidOperation("Withdrawal amount must be positive".to_string()));
                    }
                    
                    // 检查余额
                    if self.balance < amount {
                        return Err(BankAccountError::InsufficientFunds {
                            requested: amount,
                            available: self.balance,
                        });
                    }
                    
                    Ok(vec![BankAccountEvent::MoneyWithdrawn { amount }])
                },
                BankAccountCommand::CloseAccount => {
                    // 检查账户是否已关闭
                    if self.is_closed {
                        return Err(BankAccountError::AccountClosed);
                    }
                    
                    Ok(vec![BankAccountEvent::AccountClosed])
                }
            }
        }
        
        fn apply_event(&mut self, event: Self::Event) {
            match event {
                BankAccountEvent::AccountCreated { id, owner } => {
                    self.id = id;
                    self.owner = owner;
                    self.balance = Decimal::ZERO;
                    self.is_closed = false;
                },
                BankAccountEvent::MoneyDeposited { amount } => {
                    self.balance += amount;
                },
                BankAccountEvent::MoneyWithdrawn { amount } => {
                    self.balance -= amount;
                },
                BankAccountEvent::AccountClosed => {
                    self.is_closed = true;
                }
            }
            
            self.version += 1;
        }
    }
    
    // 银行账户命令处理器
    pub struct BankAccountCommandHandler {
        repository: Arc<EventSourcedRepository<BankAccount, BankAccountEvent, impl EventStore>>,
    }
    
    impl BankAccountCommandHandler {
        pub fn new(repository: Arc<EventSourcedRepository<BankAccount, BankAccountEvent, impl EventStore>>) -> Self {
            Self { repository }
        }
    }
    
    #[async_trait]
    impl CommandHandler<BankAccountCommand, BankAccount> for BankAccountCommandHandler {
        async fn handle(&self, command: BankAccountCommand) -> Result<(), CommandHandlerError<BankAccountError>> {
            match &command {
                BankAccountCommand::CreateAccount { id, .. } => {
                    // 创建新账户
                    let mut account = BankAccount::default();
                    
                    // 执行命令
                    let events = account.handle_command(command)
                        .map_err(CommandHandlerError::DomainError)?;
                        
                    // 保存事件
                    self.repository.save(&account, events).await
                        .map_err(CommandHandlerError::RepositoryError)?;
                },
                _ => {
                    // 加载现有账户
                    let id = match &command {
                        BankAccountCommand::CreateAccount { id, .. } => id,
                        BankAccountCommand::Deposit { .. } => id,
                        BankAccountCommand::Withdraw { .. } => id,
                        BankAccountCommand::CloseAccount => id,
                    };
                    
                    let mut account = self.repository.load(id).await
                        .map_err(CommandHandlerError::RepositoryError)?
                        .ok_or_else(|| CommandHandlerError::AggregateNotFound(id.clone()))?;
                        
                    // 执行命令
                    let events = account.handle_command(command)
                        .map_err(CommandHandlerError::DomainError)?;
                        
                    // 保存事件
                    self.repository.save(&account, events).await
                        .map_err(CommandHandlerError::RepositoryError)?;
                }
            }
            
            Ok(())
        }
    }
    
    // 银行账户查询模型
    #[derive(Default, Clone)]
    pub struct BankAccountQueryModel {
        accounts: HashMap<String, BankAccountDto>,
    }
    
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct BankAccountDto {
        pub id: String,
        pub owner: String,
        pub balance: Decimal,
        pub is_closed: bool,
        pub transaction_count: usize,
        pub last_updated: DateTime<Utc>,
    }
    
    // 银行账户投影器
    pub struct BankAccountProjector {
        query_model: QueryModel<BankAccountQueryModel>,
    }
    
    impl BankAccountProjector {
        pub fn new() -> Self {
            Self {
                query_model: QueryModel::new(),
            }
        }
    }
    
    #[async_trait]
    impl Projector<BankAccountEvent, BankAccountQueryModel> for BankAccountProjector {
        fn query_model(&self) -> &QueryModel<BankAccountQueryModel> {
            &self.query_model
        }
        
        async fn handle_event(&self, event: EnvelopedEvent<BankAccountEvent>) -> Result<(), ProjectorError> {
            self.query_model.update(|model| {
                let account_id = match &event.payload {
                    BankAccountEvent::AccountCreated { id, .. } => id,
                    _ => {
                        // 从事件元数据中提取账户 ID
                        let stream_id = event.metadata.source.clone();
                        let parts: Vec<&str> = stream_id.split('-').collect();
                        if parts.len() >= 2 {
                            parts[1]
                        } else {
                            return; // 无法确定账户 ID
                        }
                    }
                };
                
                let account = model.accounts.entry(account_id.clone())
                    .or_insert_with(|| BankAccountDto {
                        id: account_id.clone(),
                        owner: String::new(),
                        balance: Decimal::ZERO,
                        is_closed: false,
                        transaction_count: 0,
                        last_updated: Utc::now(),
                    });
                    
                match event.payload {
                    BankAccountEvent::AccountCreated { owner, .. } => {
                        account.owner = owner;
                    },
                    BankAccountEvent::MoneyDeposited { amount } => {
                        account.balance += amount;
                        account.transaction_count += 1;
                    },
                    BankAccountEvent::MoneyWithdrawn { amount } => {
                        account.balance -= amount;
                        account.transaction_count += 1;
                    },
                    BankAccountEvent::AccountClosed => {
                        account.is_closed = true;
                    }
                }
                
                account.last_updated = event.metadata.timestamp;
            })?;
            
            Ok(())
        }
        
        async fn rebuild(&self, event_store: &dyn EventStore) -> Result<(), ProjectorError> {
            // 清空当前模型
            self.query_model.update(|model| {
                model.accounts.clear();
            })?;
            
            // 从事件存储中读取所有事件
            let events = event_store.read_all::<BankAccountEvent>(0, None).await
                .map_err(|e| ProjectorError::EventStoreError(e.to_string()))?;
                
            // 按时间顺序应用事件
            for event in events {
                self.handle_event(event).await?;
            }
            
            Ok(())
        }
    }
    
    // 查询处理器
    pub struct BankAccountQueryHandler {
        query_model: Arc<QueryModel<BankAccountQueryModel>>,
    }
    
    impl BankAccountQueryHandler {
        pub fn new(query_model: Arc<QueryModel<BankAccountQueryModel>>) -> Self {
            Self { query_model }
        }
        
        pub fn get_account(&self, id: &str) -> Result<Option<BankAccountDto>, QueryError> {
            self.query_model.read(|model| {
                model.accounts.get(id).cloned()
            }).map_err(|e| QueryError::ModelError(e.to_string()))
        }
        
        pub fn list_accounts(&self) -> Result<Vec<BankAccountDto>, QueryError> {
            self.query_model.read(|model| {
                model.accounts.values().cloned().collect()
            }).map_err(|e| QueryError::ModelError(e.to_string()))
        }
        
        pub fn get_total_balance(&self) -> Result<Decimal, QueryError> {
            self.query_model.read(|model| {
                model.accounts.values()
                    .filter(|a| !a.is_closed)
                    .map(|a| a.balance)
                    .sum()
            }).map_err(|e| QueryError::ModelError(e.to_string()))
        }
    }
}
```

### 6.5 反应式架构

```rust
// 反应式基础设施
mod reactive_infrastructure {
    use async_trait::async_trait;
    use futures::{Stream, StreamExt};
    use std::sync::Arc;
    
    // 反应式发布者
    #[async_trait]
    pub trait Publisher<T: Clone + Send + Sync + 'static>: Send + Sync {
        async fn publish(&self, item: T) -> Result<(), PublishError>;
        fn subscribe(&self) -> Box<dyn Stream<Item = T> + Send + Unpin>;
    }
    
    // 基于内存的发布者实现
    pub struct InMemoryPublisher<T: Clone + Send + Sync + 'static> {
        tx: tokio::sync::broadcast::Sender<T>,
    }
    
    impl<T: Clone + Send + Sync + 'static> InMemoryPublisher<T> {
        pub fn new(buffer: usize) -> Self {
            let (tx, _) = tokio::sync::broadcast::channel(buffer);
            Self { tx }
        }
    }
    
    #[async_trait]
    impl<T: Clone + Send + Sync + 'static> Publisher<T> for InMemoryPublisher<T> {
        async fn publish(&self, item: T) -> Result<(), PublishError> {
            self.tx.send(item)
                .map_err(|_| PublishError::NoSubscribers)
                .map(|_| ())
        }
        
        fn subscribe(&self) -> Box<dyn Stream<Item = T> + Send + Unpin> {
            let rx = self.tx.subscribe();
            
            Box::new(tokio_stream::wrappers::BroadcastStream::new(rx)
                .filter_map(|result| async move {
                    match result {
                        Ok(item) => Some(item),
                        Err(_) => None,
                    }
                }))
        }
    }
    
    // 反应式处理器
    #[async_trait]
    pub trait Processor<I, O>: Send + Sync {
        async fn process(&self, input: I) -> Result<O, ProcessorError>;
    }
    
    // 流处理器
    pub trait StreamProcessor<I, O>: Send + Sync
    where
        I: Send + 'static,
        O: Send + 'static,
    {
        fn process(&self, input: impl Stream<Item = I> + Send + Unpin) -> Box<dyn Stream<Item = Result<O, ProcessorError>> + Send + Unpin>;
    }
    
    // 映射处理器
    pub struct MapProcessor<I, O, F>
    where
        F: Fn(I) -> Result<O, ProcessorError> + Send + Sync + 'static,
        I: Send + 'static,
        O: Send + 'static,
    {
        mapper: F,
        _marker: PhantomData<(I, O)>,
    }
    
    impl<I, O, F> MapProcessor<I, O, F>
    where
        F: Fn(I) -> Result<O, ProcessorError> + Send + Sync + 'static,
        I: Send + 'static,
        O: Send + 'static,
    {
        pub fn new(mapper: F) -> Self {
            Self {
                mapper,
                _marker: PhantomData,
            }
        }
    }
    
    impl<I, O, F> StreamProcessor<I, O> for MapProcessor<I, O, F>
    where
        F: Fn(I) -> Result<O, ProcessorError> + Send + Sync + 'static,
        I: Send + 'static,
        O: Send + 'static,
    {
        fn process(&self, input: impl Stream<Item = I> + Send + Unpin) -> Box<dyn Stream<Item = Result<O, ProcessorError>> + Send + Unpin> {
            let mapper = self.mapper.clone();
            
            Box::new(input.map(move |item| {
                mapper(item)
            }))
        }
    }
    
    // 过滤处理器
    pub struct FilterProcessor<I, F>
    where
        F: Fn(&I) -> bool + Send + Sync + 'static,
        I: Send + 'static,
    {
        predicate: F,
        _marker: PhantomData<I>,
    }
    
    impl<I, F> FilterProcessor<I, F>
    where
        F: Fn(&I) -> bool + Send + Sync + 'static,
        I: Send + 'static,
    {
        pub fn new(predicate: F) -> Self {
            Self {
                predicate,
                _marker: PhantomData,
            }
        }
    }
    
    impl<I, F> StreamProcessor<I, I> for FilterProcessor<I, F>
    where
        F: Fn(&I) -> bool + Send + Sync + 'static,
        I: Clone + Send + 'static,
    {
        fn process(&self, input: impl Stream<Item = I> + Send + Unpin) -> Box<dyn Stream<Item = Result<I, ProcessorError>> + Send + Unpin> {
            let predicate = self.predicate.clone();
            
            Box::new(input.filter_map(move |item| {
                let should_keep = predicate(&item);
                async move {
                    if should_keep {
                        Some(Ok(item))
                    } else {
                        None
                    }
                }
            }))
        }
    }
    
    // 异步映射处理器
    pub struct AsyncMapProcessor<I, O, F, Fut>
    where
        F: Fn(I) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<O, ProcessorError>> + Send + 'static,
        I: Send + 'static,
        O: Send + 'static,
    {
        mapper: F,
        _marker: PhantomData<(I, O, Fut)>,
    }
    
    impl<I, O, F, Fut> AsyncMapProcessor<I, O, F, Fut>
    where
        F: Fn(I) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<O, ProcessorError>> + Send + 'static,
        I: Send + 'static,
        O: Send + 'static,
    {
        pub fn new(mapper: F) -> Self {
            Self {
                mapper,
                _marker: PhantomData,
            }
        }
    }
    
    impl<I, O, F, Fut> StreamProcessor<I, O> for AsyncMapProcessor<I, O, F, Fut>
    where
        F: Fn(I) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<O, ProcessorError>> + Send + 'static,
        I: Send + 'static,
        O: Send + 'static,
    {
        fn process(&self, input: impl Stream<Item = I> + Send + Unpin) -> Box<dyn Stream<Item = Result<O, ProcessorError>> + Send + Unpin> {
            let mapper = self.mapper.clone();
            
            Box::new(input.then(move |item| {
                let mapper_clone = mapper.clone();
                async move {
                    mapper_clone(item).await
                }
            }))
        }
    }
    
    // 反应式管道
    pub struct Pipeline<I, O> {
        stages: Vec<Box<dyn StreamProcessor<I, O>>>,
    }
    
    impl<I, O> Pipeline<I, O>
    where
        I: Clone + Send + Sync + 'static,
        O: Clone + Send + Sync + 'static,
    {
        pub fn new() -> Self {
            Self {
                stages: Vec::new(),
            }
        }
        
        pub fn add_stage<P>(&mut self, processor: P) -> &mut Self
        where
            P: StreamProcessor<I, O> + 'static,
        {
            self.stages.push(Box::new(processor));
            self
        }
        
        pub fn build(&self) -> impl StreamProcessor<I, O> {
            // 创建复合处理器
            let stages = self.stages.clone();
            
            let processor = move |input: impl Stream<Item = I> + Send + Unpin| {
                let mut current = input;
                
                for stage in &stages {
                    current = stage.process(current);
                }
                
                current
            };
            
            Box::new(PipelineProcessor { processor: Box::new(processor) })
        }
    }
    
    struct PipelineProcessor<I, O> {
        processor: Box<dyn Fn(impl Stream<Item = I> + Send + Unpin) -> impl Stream<Item = Result<O, ProcessorError>> + Send + Unpin + 'static>,
    }
    
    impl<I, O> StreamProcessor<I, O> for PipelineProcessor<I, O>
    where
        I: Send + 'static,
        O: Send + 'static,
    {
        fn process(&self, input: impl Stream<Item = I> + Send + Unpin) -> Box<dyn Stream<Item = Result<O, ProcessorError>> + Send + Unpin> {
            Box::new((self.processor)(input))
        }
    }
    
    // 反应式源和接收器
    #[async_trait]
    pub trait Source<T: Send + 'static>: Send + Sync {
        fn source(&self) -> Box<dyn Stream<Item = T> + Send + Unpin>;
    }
    
    #[async_trait]
    pub trait Sink<T: Send + 'static>: Send + Sync {
        async fn send(&self, item: T) -> Result<(), SinkError>;
    }
    
    // 反应式系统类
    pub struct ReactiveSystem<I, O, S, K>
    where
        I: Send + 'static,
        O: Send + 'static,
        S: Source<I> + 'static,
        K: Sink<O> + 'static,
    {
        source: S,
        processor: Box<dyn StreamProcessor<I, O>>,
        sink: K,
    }
    
    impl<I, O, S, K> ReactiveSystem<I, O, S, K>
    where
        I: Send + 'static,
        O: Send + 'static,
        S: Source<I> + 'static,
        K: Sink<O> + 'static,
    {
        pub fn new(source: S, processor: Box<dyn StreamProcessor<I, O>>, sink: K) -> Self {
            Self {
                source,
                processor,
                sink,
            }
        }
        
        pub async fn run(&self) -> Result<(), ReactiveSystemError> {
            let input_stream = self.source.source();
            let output_stream = self.processor.process(input_stream);
            
            let sink = self.sink.clone();
            
            output_stream
                .for_each(|result| async {
                    match result {
                        Ok(item) => {
                            if let Err(e) = sink.send(item).await {
                                log::error!("Failed to send to sink: {}", e);
                            }
                        },
                        Err(e) => {
                            log::error!("Processor error: {}", e);
                        }
                    }
                })
                .await;
                
            Ok(())
        }
    }
}

// 反应式数据处理示例
mod reactive_data_processing {
    use super::reactive_infrastructure::*;
    use async_trait::async_trait;
    use std::sync::Arc;
    
    // 传感器数据模型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct SensorReading {
        pub sensor_id: String,
        pub timestamp: DateTime<Utc>,
        pub temperature: f64,
        pub humidity: Option<f64>,
        pub pressure: Option<f64>,
    }
    
    // 警报模型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct Alert {
        pub id: String,
        pub sensor_id: String,
        pub timestamp: DateTime<Utc>,
        pub alert_type: AlertType,
        pub message: String,
        pub severity: AlertSeverity,
    }
    
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum AlertType {
        HighTemperature,
        LowTemperature,
        HighHumidity,
        LowHumidity,
        SensorMalfunction,
    }
    
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum AlertSeverity {
        Info,
        Warning,
        Critical,
    }
    
    // Kafka 传感器数据源
    pub struct KafkaSensorSource {
        consumer: StreamConsumer,
    }
    
    impl KafkaSensorSource {
        pub fn new(bootstrap_servers: &str, group_id: &str, topic: &str) -> Result<Self, SourceError> {
            let consumer: StreamConsumer = ClientConfig::new()
                .set("bootstrap.servers", bootstrap_servers)
                .set("group.id", group_id)
                .set("enable.auto.commit", "true")
                .set("auto.offset.reset", "earliest")
                .create()
                .map_err(|e| SourceError::ConnectionFailed(e.to_string()))?;
                
            consumer.subscribe(&[topic])
                .map_err(|e| SourceError::SubscriptionFailed(e.to_string()))?;
                
            Ok(Self { consumer })
        }
    }
    
    impl Source<SensorReading> for KafkaSensorSource {
        fn source(&self) -> Box<dyn Stream<Item = SensorReading> + Send + Unpin> {
            let stream = self.consumer.stream().filter_map(|message_result| async {
                match message_result {
                    Ok(message) => {
                        if let Some(payload) = message.payload() {
                            match serde_json::from_slice::<SensorReading>(payload) {
                                Ok(reading) => Some(reading),
                                Err(e) => {
                                    log::error!("Failed to deserialize sensor reading: {}", e);
                                    None
                                }
                            }
                        } else {
                            None
                        }
                    },
                    Err(e) => {
                        log::error!("Error receiving Kafka message: {}", e);
                        None
                    }
                }
            });
            
            Box::new(stream)
        }
    }
    
    // 警报处理器
    pub struct AlertProcessor {
        high_temp_threshold: f64,
        low_temp_threshold: f64,
        high_humidity_threshold: f64,
        low_humidity_threshold: f64,
    }
    
    impl AlertProcessor {
        pub fn new(
            high_temp_threshold: f64,
            low_temp_threshold: f64,
            high_humidity_threshold: f64,
            low_humidity_threshold: f64,
        ) -> Self {
            Self {
                high_temp_threshold,
                low_temp_threshold,
                high_humidity_threshold,
                low_humidity_threshold,
            }
        }
        
        fn check_temperature(&self, reading: &SensorReading) -> Option<Alert> {
            if reading.temperature > self.high_temp_threshold {
                Some(Alert {
                    id: Uuid::new_v4().to_string(),
                    sensor_id: reading.sensor_id.clone(),
                    timestamp: Utc::now(),
                    alert_type: AlertType::HighTemperature,
                    message: format!("High temperature detected: {:.1}°C", reading.temperature),
                    severity: AlertSeverity::Warning,
                })
            } else if reading.temperature < self.low_temp_threshold {
                Some(Alert {
                    id: Uuid::new_v4().to_string(),
                    sensor_id: reading.sensor_id.clone(),
                    timestamp: Utc::now(),
                    alert_type: AlertType::LowTemperature,
                    message: format!("Low temperature detected: {:.1}°C", reading.temperature),
                    severity: AlertSeverity::Warning,
                })
            } else {
                None
            }
        }
        
        fn check_humidity(&self, reading: &SensorReading) -> Option<Alert> {
            if let Some(humidity) = reading.humidity {
                if humidity > self.high_humidity_threshold {
                    Some(Alert {
                        id: Uuid::new_v4().to_string(),
                        sensor_id: reading.sensor_id.clone(),
                        timestamp: Utc::now(),
                        alert_type: AlertType::HighHumidity,
                        message: format!("High humidity detected: {:.1}%", humidity),
                        severity: AlertSeverity::Info,
                    })
                } else if humidity < self.low_humidity_threshold {
                    Some(Alert {
                        id: Uuid::new_v4().to_string(),
                        sensor_id: reading.sensor_id.clone(),
                        timestamp: Utc::now(),
                        alert_type: AlertType::LowHumidity,
                        message: format!("Low humidity detected: {:.1}%", humidity),
                        severity: AlertSeverity::Info,
                    })
                } else {
                    None
                }
            } else {
                None
            }
        }
        
        fn check_sensor_health(&self, reading: &SensorReading) -> Option<Alert> {
            if reading.humidity.is_none() && reading.pressure.is_none() {
                Some(Alert {
                    id: Uuid::new_v4().to_string(),
                    sensor_id: reading.sensor_id.clone(),
                    timestamp: Utc::now(),
                    alert_type: AlertType::SensorMalfunction,
                    message: format!("Sensor may be malfunctioning: missing humidity and pressure data"),
                    severity: AlertSeverity::Critical,
                })
            } else {
                None
            }
        }
    }
    
    impl StreamProcessor<SensorReading, Vec<Alert>> for AlertProcessor {
        fn process(&self, input: impl Stream<Item = SensorReading> + Send + Unpin) -> Box<dyn Stream<Item = Result<Vec<Alert>, ProcessorError>> + Send + Unpin> {
            let processor = self.clone();
            
            let stream = input.map(move |reading| {
                let mut alerts = Vec::new();
                
                // 检查温度告警
                if let Some(alert) = processor.check_temperature(&reading) {
                    alerts.push(alert);
                }
                
                // 检查湿度告警
                if let Some(alert) = processor.check_humidity(&reading) {
                    alerts.push(alert);
                }
                
                // 检查传感器健康状况
                if let Some(alert) = processor.check_sensor_health(&reading) {
                    alerts.push(alert);
                }
                
                Ok(alerts)
            });
            
            Box::new(stream)
        }
    }
    
    // 过滤非空告警
    pub struct NonEmptyAlertFilter;
    
    impl StreamProcessor<Vec<Alert>, Vec<Alert>> for NonEmptyAlertFilter {
        fn process(&self, input: impl Stream<Item = Vec<Alert>> + Send + Unpin) -> Box<dyn Stream<Item = Result<Vec<Alert>, ProcessorError>> + Send + Unpin> {
            let stream = input.filter_map(|alerts| async move {
                if alerts.is_empty() {
                    None
                } else {
                    Some(Ok(alerts))
                }
            });
            
            Box::new(stream)
        }
    }
    
    // 告警聚合器
    pub struct AlertAggregator {
        window_size: Duration,
    }
    
    impl AlertAggregator {
        pub fn new(window_size: Duration) -> Self {
            Self { window_size }
        }
    }
    
    impl StreamProcessor<Vec<Alert>, AggregatedAlerts> for AlertAggregator {
        fn process(&self, input: impl Stream<Item = Vec<Alert>> + Send + Unpin) -> Box<dyn Stream<Item = Result<AggregatedAlerts, ProcessorError>> + Send + Unpin> {
            let window_size = self.window_size;
            
            let stream = input
                .map(|alerts| alerts.into_iter().flatten().collect::<Vec<_>>())
                .chunks_timeout(usize::MAX, window_size)
                .map(move |chunks| {
                    let alerts = chunks.into_iter().flatten().collect::<Vec<_>>();
                    
                    let mut aggregated = AggregatedAlerts {
                        window_start: Utc::now() - window_size,
                        window_end: Utc::now(),
                        total_alerts: alerts.len(),
                        alerts_by_severity: HashMap::new(),
                        alerts_by_type: HashMap::new(),
                        alerts_by_sensor: HashMap::new(),
                        alerts,
                    };
                    
                    // 聚合告警
                    for alert in &aggregated.alerts {
                        // 按严重程度分组
                        *aggregated.alerts_by_severity.entry(alert.severity.clone()).or_insert(0) += 1;
                        
                        // 按类型分组
                        *aggregated.alerts_by_type.entry(alert.alert_type.clone()).or_insert(0) += 1;
                        
                        // 按传感器分组
                        *aggregated.alerts_by_sensor.entry(alert.sensor_id.clone()).or_insert(0) += 1;
                    }
                    
                    Ok(aggregated)
                });
                
            Box::new(stream)
        }
    }
    
    #[derive(Clone, Debug)]
    pub struct AggregatedAlerts {
        pub window_start: DateTime<Utc>,
        pub window_end: DateTime<Utc>,
        pub total_alerts: usize,
        pub alerts_by_severity: HashMap<AlertSeverity, usize>,
        pub alerts_by_type: HashMap<AlertType, usize>,
        pub alerts_by_sensor: HashMap<String, usize>,
        pub alerts: Vec<Alert>,
    }
    
    // 数据库告警接收器
    pub struct DatabaseAlertSink {
        pool: Arc<Pool>,
    }
    
    impl DatabaseAlertSink {
        pub fn new(pool: Arc<Pool>) -> Self {
            Self { pool }
        }
    }
    
    #[async_trait]
    impl Sink<AggregatedAlerts> for DatabaseAlertSink {
        async fn send(&self, aggregated: AggregatedAlerts) -> Result<(), SinkError> {
            // 获取数据库连接
            let mut conn = self.pool.get().await
                .map_err(|e| SinkError::ConnectionFailed(e.to_string()))?;
                
            // 开始事务
            let tx = conn.begin().await
                .map_err(|e| SinkError::TransactionFailed(e.to_string()))?;
                
            // 插入聚合记录
            sqlx::query!(
                r#"
                INSERT INTO alert_aggregations (
                    window_start, window_end, total_alerts, critical_alerts, 
                    warning_alerts, info_alerts, created_at
                )
                VALUES ($1, $2, $3, $4, $5, $6, $7)
                RETURNING id
                "#,
                aggregated.window_start,
                aggregated.window_end,
                aggregated.total_alerts as i32,
                aggregated.alerts_by_severity.get(&AlertSeverity::Critical).unwrap_or(&0) as i32,
                aggregated.alerts_by_severity.get(&AlertSeverity::Warning).unwrap_or(&0) as i32,
                aggregated.alerts_by_severity.get(&AlertSeverity::Info).unwrap_or(&0) as i32,
                Utc::now(),
            )
            .fetch_one(&mut *tx)
            .await
            .map_err(|e| SinkError::ExecutionFailed(e.to_string()))?;
            
            // 插入各个告警
            for alert in &aggregated.alerts {
                sqlx::query!(
                    r#"
                    INSERT INTO alerts (
                        id, sensor_id, timestamp, alert_type, message, severity, created_at
                    )
                    VALUES ($1, $2, $3, $4, $5, $6, $7)
                    "#,
                    alert.id,
                    alert.sensor_id,
                    alert.timestamp,
                    alert.alert_type as AlertType,
                    alert.message,
                    alert.severity as AlertSeverity,
                    Utc::now(),
                )
                .execute(&mut *tx)
                .await
                .map_err(|e| SinkError::ExecutionFailed(e.to_string()))?;
            }
            
            // 提交事务
            tx.commit().await
                .map_err(|e| SinkError::TransactionFailed(e.to_string()))?;
                
            Ok(())
        }
    }
    
    // 日志告警接收器
    pub struct LogAlertSink;
    
    #[async_trait]
    impl Sink<AggregatedAlerts> for LogAlertSink {
        async fn send(&self, aggregated: AggregatedAlerts) -> Result<(), SinkError> {
            log::info!(
                "Alert Summary: {} alerts between {} and {}",
                aggregated.total_alerts,
                aggregated.window_start,
                aggregated.window_end
            );
            
            log::info!("By severity: {:?}", aggregated.alerts_by_severity);
            log::info!("By type: {:?}", aggregated.alerts_by_type);
            log::info!("By sensor: {:?}", aggregated.alerts_by_sensor);
            
            for alert in &aggregated.alerts {
                match alert.severity {
                    AlertSeverity::Critical => log::error!("{}: {}", alert.id, alert.message),
                    AlertSeverity::Warning => log::warn!("{}: {}", alert.id, alert.message),
                    AlertSeverity::Info => log::info!("{}: {}", alert.id, alert.message),
                }
            }
            
            Ok(())
        }
    }
    
    // 构建反应式数据处理系统
    pub fn build_sensor_alert_system(
        bootstrap_servers: &str,
        topic: &str,
        high_temp_threshold: f64,
        low_temp_threshold: f64,
        high_humidity_threshold: f64,
        low_humidity_threshold: f64,
        window_size: Duration,
        db_pool: Arc<Pool>,
    ) -> Result<ReactiveSystem<SensorReading, AggregatedAlerts, KafkaSensorSource, DatabaseAlertSink>, SystemError> {
        // 创建数据源
        let source = KafkaSensorSource::new(bootstrap_servers, "sensor-alert-system", topic)?;
        
        // 创建处理器管道
        let alert_processor = AlertProcessor::new(
            high_temp_threshold,
            low_temp_threshold,
            high_humidity_threshold,
            low_humidity_threshold,
        );
        
        let non_empty_filter = NonEmptyAlertFilter;
        let aggregator = AlertAggregator::new(window_size);
        
        let processor = Pipeline::new()
            .add_stage(alert_processor)
            .add_stage(non_empty_filter)
            .add_stage(aggregator)
            .build();
            
        // 创建接收器
        let sink = DatabaseAlertSink::new(db_pool);
        
        // 构建反应式系统
        let system = ReactiveSystem::new(source, Box::new(processor), sink);
        
        Ok(system)
    }
}
```

## 7. 总结与最佳实践

通过本指南，我们探索了 Rust 中的复杂设计模式和架构设计模式，涵盖了数据流、执行流、控制流、容错和一致性等多个方面。以下是一些关键的最佳实践总结：

### 7.1 数据流最佳实践

1. **使用 trait 界定数据转换边界**：为数据流转换创建明确的 trait 界面，使数据处理环节更清晰和可测试。

2. **采用响应式编程处理异步数据流**：利用 Rust 的异步编程能力和 Stream 特征实现高效的数据处理管道。

3. **明确所有权和借用**：数据流经过处理环节时，需要明确所有权转移，或者使用引用共享数据，避免不必要的复制。

4. **使用类型系统保证数据转换安全**：利用 Rust 的强类型系统确保在编译时捕获数据转换错误，而不是运行时。

5. **设计可组合的流处理组件**：创建可重用的数据处理单元，以便轻松构建复杂的数据处理流水线。

### 7.2 执行流最佳实践

1. **分离调度与执行**：将任务调度和实际执行解耦，为不同的执行环境提供灵活性。

2. **使用类型状态实现安全的工作流转换**：利用 Rust 的类型系统确保工作流状态转换的正确性。

3. **结合 trait 和泛型实现可扩展的执行引擎**：使用 trait 抽象执行环节，允许多种执行策略实现。

4. **追踪工作流生命周期**：设计明确的生命周期模型，包括创建、执行、暂停、恢复和终止阶段。

5. **使用 Actor 模式处理并发**：采用 Actor 模型管理状态和消息传递，简化并发控制。

### 7.3 控制流最佳实践

1. **使用责任链模式分离关注点**：通过责任链处理连续的操作，使每个处理环节专注于单一职责。

2. **实现可撤销/重做的命令模式**：使用命令模式封装操作，支持事务性执行。

3. **使用有限状态机建模复杂系统行为**：明确定义系统状态和转换规则，使状态变化更可预测。

4. **采用观察者模式实现松耦合**：使系统组件间通过事件通信而非直接依赖，提高灵活性。

5. **定义清晰的错误处理策略**：设计层次化的错误类型和传播机制，使错误处理更有条理。

### 7.4 容错最佳实践

1. **实现优雅的重试机制**：使用指数退避等策略，避免在失败情况下立即重试。

2. **使用断路器防止级联失败**：采用断路器模式，在系统部分故障时保护整体系统。

3. **通过舱壁模式隔离故障**：限制资源使用和故障传播范围，防止单点故障影响整个系统。

4. **设计超时策略保证响应性**：为操作设置合适的超时，避免资源长时间占用。

5. **实现可控制的流量**：使用速率限制器控制系统负载，在高压力下保持系统稳定。

### 7.5 一致性最佳实践

1. **使用分布式锁协调访问**：在分布式环境中采用可靠的锁机制协调资源访问。

2. **实现补偿事务保证业务一致性**：通过 Saga 模式处理长时间运行的事务，支持故障情况下的回滚。

3. **采用事件溯源保持数据历史**：记录所有状态变更事件，支持系统状态重建和审计。

4. **分离命令和查询责任**：使用 CQRS 模式优化读写操作，提高系统性能和可伸缩性。

5. **确保操作幂等性**：设计支持重复执行的接口，增强系统的容错能力。

通过合理组合这些模式和最佳实践，可以构建出健壮、高性能且可维护的 Rust 系统。关键是根据具体的业务需求和系统特性，选择合适的设计模式，并利用 Rust 的类型系统和所有权模型确保实现的安全性和正确性。

无论是构建工作流系统、分布式服务还是数据处理管道，这些设计模式都能提供坚实的架构基础，帮助你创建出既安全又高效的 Rust 应用程序。
