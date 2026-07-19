# 工作流拓扑结构分析与调度机制设计

"谢谢 非常感谢
以上架构 似乎没有针对工作流本身的拓扑结构进行分析：
-1. 工作流的每个具体的实例间的结构关系，类似于程序语言类型系统的树形组织关系，递归深度优先或者广度优先的执行流关系，自上向下和自下而上归纳关系等
-2.  由于存在以上1的情况 使得工作流的执行者需要被良好的有序调度，而不是单一的抢占式执行，或者存在其他的类似异步并发编程模式的机制 类似于rust tokio的调度机制
-3. 在1，2的情况下 如何权衡 与 工作流编排之间的设计和关系 就很重要了
如果你有很多好思路请回复  如果需要借助编程语言表达 可以用rust 或者golang 自由发挥"

您提出了一个很好的观察点。现有架构确实缺少对工作流拓扑结构和执行模型的深入分析。以下我将围绕工作流实例间的结构关系、调度机制和编排策略展开讨论。

## 目录

- [工作流拓扑结构分析与调度机制设计](#工作流拓扑结构分析与调度机制设计)
  - [目录](#目录)
  - [一、工作流拓扑结构模型](#一工作流拓扑结构模型)
    - [1. 工作流实例间的结构关系](#1-工作流实例间的结构关系)
    - [2. 工作流递归与执行模型](#2-工作流递归与执行模型)
  - [二、高级工作流调度器设计](#二高级工作流调度器设计)
    - [1. 异步并发模式的工作流调度器](#1-异步并发模式的工作流调度器)
    - [2. 工作流执行器实现（类似于tokio的调度机制）](#2-工作流执行器实现类似于tokio的调度机制)
  - [三、工作流拓扑与编排的整合设计](#三工作流拓扑与编排的整合设计)
    - [1. 工作流拓扑感知编排器](#1-工作流拓扑感知编排器)
    - [2. 工作流拓扑优化器](#2-工作流拓扑优化器)
    - [3. 分层工作流结构模型](#3-分层工作流结构模型)
  - [四、工作流递归模型与拓扑感知调度](#四工作流递归模型与拓扑感知调度)
    - [1. 递归工作流结构](#1-递归工作流结构)
    - [2. 拓扑感知调度器实现](#2-拓扑感知调度器实现)
  - [五、工作流编排与拓扑优化器](#五工作流编排与拓扑优化器)
  - [六、总结与设计原则](#六总结与设计原则)
    - [1. 工作流拓扑结构设计原则](#1-工作流拓扑结构设计原则)
    - [2. 工作流调度机制设计原则](#2-工作流调度机制设计原则)
    - [3. 优化与编排策略](#3-优化与编排策略)
  - [工作流架构与智能家居系统的适配性分析](#工作流架构与智能家居系统的适配性分析)
    - [智能家居系统的独特特点](#智能家居系统的独特特点)
    - [工作流架构的独特优势](#工作流架构的独特优势)
  - [其他架构模式的局限性](#其他架构模式的局限性)
    - [微服务架构](#微服务架构)
    - [事件驱动架构](#事件驱动架构)
    - [响应式架构](#响应式架构)
    - [分层架构](#分层架构)
  - [工作流架构的成功因素](#工作流架构的成功因素)
  - [构建成功的智能家居工作流系统关键点](#构建成功的智能家居工作流系统关键点)

## 一、工作流拓扑结构模型

### 1. 工作流实例间的结构关系

工作流实例间可以形成多种拓扑结构关系，这直接影响执行模式和系统行为。

```rust
/// 工作流关系类型枚举
pub enum WorkflowRelationType {
    /// 父子关系 - 父工作流创建并监督子工作流
    ParentChild,
    /// 依赖关系 - 工作流A依赖工作流B的结果
    Dependency,
    /// 协作关系 - 多个工作流协同完成一个任务
    Collaboration,
    /// 触发关系 - 工作流A的完成触发工作流B的开始
    Trigger,
    /// 版本关系 - 工作流A是工作流B的新版本
    Version,
}

/// 工作流拓扑结构
pub struct WorkflowTopology {
    /// 拓扑图 - 使用邻接表表示
    graph: HashMap<WorkflowInstanceId, Vec<(WorkflowInstanceId, WorkflowRelationType)>>,
    /// 根工作流列表
    roots: HashSet<WorkflowInstanceId>,
    /// 工作流元数据
    metadata: HashMap<WorkflowInstanceId, WorkflowMetadata>,
}

impl WorkflowTopology {
    /// 判断是否存在环路
    pub fn has_cycles(&self) -> bool {
        // 使用拓扑排序检测环路
        let mut visited = HashSet::new();
        let mut temp_visited = HashSet::new();
        
        for root in &self.roots {
            if self.has_cycle_dfs(root, &mut visited, &mut temp_visited) {
                return true;
            }
        }
        false
    }
    
    /// 获取工作流的树形结构（仅考虑父子关系）
    pub fn get_tree_structure(&self) -> HashMap<WorkflowInstanceId, Vec<WorkflowInstanceId>> {
        let mut tree = HashMap::new();
        
        for (parent, relations) in &self.graph {
            let children: Vec<WorkflowInstanceId> = relations
                .iter()
                .filter(|(_, rel_type)| matches!(rel_type, WorkflowRelationType::ParentChild))
                .map(|(child_id, _)| child_id.clone())
                .collect();
                
            if !children.is_empty() {
                tree.insert(parent.clone(), children);
            }
        }
        
        tree
    }
    
    /// 获取工作流的依赖图（仅考虑依赖关系）
    pub fn get_dependency_graph(&self) -> HashMap<WorkflowInstanceId, Vec<WorkflowInstanceId>> {
        let mut dep_graph = HashMap::new();
        
        for (wf, relations) in &self.graph {
            let dependencies: Vec<WorkflowInstanceId> = relations
                .iter()
                .filter(|(_, rel_type)| matches!(rel_type, WorkflowRelationType::Dependency))
                .map(|(dep_id, _)| dep_id.clone())
                .collect();
                
            if !dependencies.is_empty() {
                dep_graph.insert(wf.clone(), dependencies);
            }
        }
        
        dep_graph
    }
    
    /// 计算工作流的执行级别（拓扑排序）
    pub fn calculate_execution_levels(&self) -> HashMap<WorkflowInstanceId, usize> {
        let mut levels = HashMap::new();
        let dep_graph = self.get_dependency_graph();
        
        // 计算入度
        let mut in_degree = HashMap::new();
        for wf_id in self.metadata.keys() {
            in_degree.insert(wf_id.clone(), 0);
        }
        
        for (_, deps) in &dep_graph {
            for dep in deps {
                *in_degree.entry(dep.clone()).or_insert(0) += 1;
            }
        }
        
        // 拓扑排序
        let mut queue = VecDeque::new();
        let mut current_level = 0;
        
        // 将入度为0的节点加入队列
        for (wf_id, degree) in &in_degree {
            if *degree == 0 {
                queue.push_back(wf_id.clone());
                levels.insert(wf_id.clone(), current_level);
            }
        }
        
        while !queue.is_empty() {
            let level_size = queue.len();
            current_level += 1;
            
            for _ in 0..level_size {
                let wf_id = queue.pop_front().unwrap();
                
                if let Some(deps) = dep_graph.get(&wf_id) {
                    for dep in deps {
                        let in_deg = in_degree.get_mut(dep).unwrap();
                        *in_deg -= 1;
                        
                        if *in_deg == 0 {
                            queue.push_back(dep.clone());
                            levels.insert(dep.clone(), current_level);
                        }
                    }
                }
            }
        }
        
        levels
    }
}
```

### 2. 工作流递归与执行模型

我们可以设计支持不同执行模型的工作流结构：

```go
// 工作流执行模型
type ExecutionModel string

const (
    // 深度优先 - 适合需要快速获得特定分支结果的场景
    DepthFirst ExecutionModel = "depth_first"
    // 广度优先 - 适合需要均衡处理所有分支的场景
    BreadthFirst ExecutionModel = "breadth_first"
    // 优先级优先 - 基于优先级的执行
    PriorityBased ExecutionModel = "priority_based"
    // 事件驱动 - 基于事件触发的执行
    EventDriven ExecutionModel = "event_driven"
)

// 工作流定义
type WorkflowDefinition struct {
    ID               string
    Name             string
    Version          string
    ExecutionModel   ExecutionModel
    ExecutionOptions ExecutionOptions
    Steps            []WorkflowStep
    SubWorkflows     map[string]WorkflowDefinition
    
    // 递归组合控制
    MaxRecursionDepth int
    RecursionStrategy RecursionStrategy
}

// 递归策略
type RecursionStrategy struct {
    // 终止条件
    TerminationCondition string
    // 结果合并方式
    ResultMergeStrategy string
    // 错误处理策略
    ErrorPropagationStrategy string
}

// 执行递归工作流
func ExecuteRecursiveWorkflow(ctx context.Context, wf WorkflowDefinition, input interface{}, depth int) (interface{}, error) {
    logger := log.FromContext(ctx)
    logger.Info("执行递归工作流", "workflowID", wf.ID, "depth", depth)
    
    // 检查递归深度
    if depth >= wf.MaxRecursionDepth {
        return nil, fmt.Errorf("超过最大递归深度 %d", wf.MaxRecursionDepth)
    }
    
    // 评估终止条件
    terminate, err := evaluateCondition(ctx, wf.RecursionStrategy.TerminationCondition, input)
    if err != nil {
        return nil, fmt.Errorf("评估终止条件失败: %w", err)
    }
    
    if terminate {
        logger.Info("递归终止条件满足，返回", "depth", depth)
        return input, nil
    }
    
    // 执行当前工作流步骤
    result, err := executeWorkflowSteps(ctx, wf.Steps, input)
    if err != nil {
        return nil, fmt.Errorf("执行工作流步骤失败: %w", err)
    }
    
    // 分解问题并递归执行子工作流
    subResults := make([]interface{}, 0)
    subProblems, err := decomposeInput(result)
    if err != nil {
        return nil, fmt.Errorf("分解问题失败: %w", err)
    }
    
    // 根据执行模型选择递归执行顺序
    switch wf.ExecutionModel {
    case DepthFirst:
        for _, subProblem := range subProblems {
            subResult, err := ExecuteRecursiveWorkflow(ctx, wf, subProblem, depth+1)
            if err != nil {
                if wf.RecursionStrategy.ErrorPropagationStrategy == "fail_fast" {
                    return nil, err
                }
                // 记录错误但继续执行
                logger.Error("子问题执行失败", "error", err)
                continue
            }
            subResults = append(subResults, subResult)
        }
    case BreadthFirst:
        var wg sync.WaitGroup
        resultChan := make(chan interface{}, len(subProblems))
        errorChan := make(chan error, len(subProblems))
        
        for _, subProblem := range subProblems {
            wg.Add(1)
            go func(sp interface{}) {
                defer wg.Done()
                subResult, err := ExecuteRecursiveWorkflow(ctx, wf, sp, depth+1)
                if err != nil {
                    errorChan <- err
                    return
                }
                resultChan <- subResult
            }(subProblem)
        }
        
        wg.Wait()
        close(resultChan)
        close(errorChan)
        
        // 处理错误
        if len(errorChan) > 0 && wf.RecursionStrategy.ErrorPropagationStrategy == "fail_fast" {
            return nil, <-errorChan
        }
        
        // 收集结果
        for res := range resultChan {
            subResults = append(subResults, res)
        }
    }
    
    // 合并子问题结果
    finalResult, err := mergeResults(subResults, wf.RecursionStrategy.ResultMergeStrategy)
    if err != nil {
        return nil, fmt.Errorf("合并结果失败: %w", err)
    }
    
    return finalResult, nil
}
```

## 二、高级工作流调度器设计

### 1. 异步并发模式的工作流调度器

```rust
/// 工作流任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 0,
    Normal = 100,
    High = 200,
    Critical = 300,
}

/// 工作流调度器配置
pub struct SchedulerConfig {
    /// 默认工作线程数
    pub worker_threads: usize,
    /// 最大工作线程数
    pub max_worker_threads: usize,
    /// 队列容量
    pub queue_capacity: usize,
    /// 任务批处理大小
    pub batch_size: usize,
    /// 工作流隔离策略
    pub isolation_policy: IsolationPolicy,
    /// 任务盗取启用
    pub task_stealing_enabled: bool,
}

/// 工作流隔离策略
pub enum IsolationPolicy {
    /// 无隔离 - 所有工作流共享线程池
    None,
    /// 按优先级隔离 - 不同优先级的工作流使用不同线程池
    ByPriority,
    /// 按域隔离 - 不同域的工作流使用不同线程池
    ByDomain,
    /// 自定义隔离 - 使用自定义函数确定隔离
    Custom(Box<dyn Fn(&WorkflowTask) -> String>),
}

/// 工作流任务
pub struct WorkflowTask {
    /// 任务ID
    pub id: TaskId,
    /// 所属工作流实例ID
    pub workflow_id: WorkflowInstanceId,
    /// 任务优先级
    pub priority: TaskPriority,
    /// 任务域
    pub domain: String,
    /// 预计执行时间
    pub estimated_duration: Option<Duration>,
    /// 任务状态
    pub status: TaskStatus,
    /// 任务依赖
    pub dependencies: Vec<TaskId>,
    /// 执行函数
    pub execute: Box<dyn FnOnce() -> Result<TaskResult, TaskError> + Send>,
}

/// 工作流调度器
pub struct WorkflowScheduler {
    /// 配置
    config: SchedulerConfig,
    /// 任务队列 - 按优先级排序
    task_queues: HashMap<String, PriorityQueue<WorkflowTask>>,
    /// 工作线程池
    thread_pools: HashMap<String, ThreadPool>,
    /// 任务状态
    task_states: DashMap<TaskId, TaskStatus>,
    /// 任务依赖图
    dependency_graph: RwLock<DiGraph<TaskId, ()>>,
    /// 节点映射
    node_indices: DashMap<TaskId, NodeIndex>,
    /// 调度器状态
    state: AtomicUsize,
    /// 控制通道
    control_tx: mpsc::Sender<ControlMessage>,
    /// 控制接收器
    control_rx: mpsc::Receiver<ControlMessage>,
}

impl WorkflowScheduler {
    /// 创建新的工作流调度器
    pub fn new(config: SchedulerConfig) -> Self {
        let (control_tx, control_rx) = mpsc::channel();
        
        let mut scheduler = Self {
            config,
            task_queues: HashMap::new(),
            thread_pools: HashMap::new(),
            task_states: DashMap::new(),
            dependency_graph: RwLock::new(DiGraph::new()),
            node_indices: DashMap::new(),
            state: AtomicUsize::new(SchedulerState::Initialized as usize),
            control_tx,
            control_rx,
        };
        
        // 初始化队列和线程池
        scheduler.initialize_pools();
        
        scheduler
    }
    
    /// 提交工作流任务
    pub fn submit(&self, task: WorkflowTask) -> Result<(), SchedulerError> {
        // 检查调度器状态
        if self.state.load(Ordering::SeqCst) != SchedulerState::Running as usize {
            return Err(SchedulerError::NotRunning);
        }
        
        // 添加任务到依赖图
        self.add_task_to_dependency_graph(&task)?;
        
        // 确定隔离键
        let isolation_key = match &self.config.isolation_policy {
            IsolationPolicy::None => "default".to_string(),
            IsolationPolicy::ByPriority => format!("priority_{:?}", task.priority),
            IsolationPolicy::ByDomain => task.domain.clone(),
            IsolationPolicy::Custom(func) => func(&task),
        };
        
        // 检查任务依赖
        if task.dependencies.is_empty() {
            // 无依赖，可以立即调度
            self.schedule_task(task, isolation_key)?;
        } else {
            // 有依赖，添加到等待图
            self.task_states.insert(task.id.clone(), TaskStatus::Waiting);
            
            // 存储任务以便依赖完成后调度
            let task_id = task.id.clone();
            let scheduler = self.clone();
            let isolation_key_clone = isolation_key.clone();
            
            self.monitor_dependencies(task, move |completed_task| {
                if let Ok(task) = completed_task {
                    let _ = scheduler.schedule_task(task, isolation_key_clone);
                }
            });
        }
        
        Ok(())
    }
    
    /// 监控任务依赖并在满足条件时调度
    fn monitor_dependencies<F>(&self, task: WorkflowTask, callback: F)
    where
        F: FnOnce(Result<WorkflowTask, SchedulerError>) + Send + 'static,
    {
        let task_id = task.id.clone();
        let dependencies = task.dependencies.clone();
        let task_states = self.task_states.clone();
        
        // 启动监控线程
        std::thread::spawn(move || {
            let mut completed_deps = HashSet::new();
            let mut all_completed = false;
            
            while !all_completed {
                for dep_id in &dependencies {
                    if completed_deps.contains(dep_id) {
                        continue;
                    }
                    
                    if let Some(status) = task_states.get(dep_id) {
                        if *status == TaskStatus::Completed {
                            completed_deps.insert(dep_id.clone());
                        } else if *status == TaskStatus::Failed {
                            // 依赖失败，任务不能执行
                            task_states.insert(task_id.clone(), TaskStatus::DependencyFailed);
                            callback(Err(SchedulerError::DependencyFailed));
                            return;
                        }
                    }
                }
                
                all_completed = completed_deps.len() == dependencies.len();
                
                if !all_completed {
                    // 等待一段时间再检查
                    std::thread::sleep(Duration::from_millis(50));
                }
            }
            
            // 所有依赖已完成，可以调度任务
            callback(Ok(task));
        });
    }
    
    /// 调度任务到指定队列
    fn schedule_task(&self, task: WorkflowTask, queue_key: String) -> Result<(), SchedulerError> {
        let queue = self.task_queues.get(&queue_key).ok_or(SchedulerError::QueueNotFound)?;
        
        // 更新任务状态
        self.task_states.insert(task.id.clone(), TaskStatus::Scheduled);
        
        // 添加到优先级队列
        queue.push(task, task.priority as u64);
        
        // 通知线程池有新任务
        if let Some(pool) = self.thread_pools.get(&queue_key) {
            pool.notify();
        }
        
        Ok(())
    }
    
    /// 启动调度器
    pub fn start(&self) -> Result<(), SchedulerError> {
        let previous_state = self.state.compare_exchange(
            SchedulerState::Initialized as usize,
            SchedulerState::Running as usize,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        
        if previous_state.is_err() {
            return Err(SchedulerError::InvalidState);
        }
        
        // 启动管理线程
        self.start_management_thread();
        
        // 启动所有线程池
        for (key, pool) in &self.thread_pools {
            pool.start()?;
        }
        
        Ok(())
    }
    
    /// 添加任务到依赖图
    fn add_task_to_dependency_graph(&self, task: &WorkflowTask) -> Result<(), SchedulerError> {
        let mut graph = self.dependency_graph.write().unwrap();
        
        // 添加节点
        let node_idx = graph.add_node(task.id.clone());
        self.node_indices.insert(task.id.clone(), node_idx);
        
        // 添加边（依赖）
        for dep_id in &task.dependencies {
            if let Some(dep_idx) = self.node_indices.get(dep_id) {
                // 添加从依赖到当前任务的边
                graph.add_edge(*dep_idx, node_idx, ());
            } else {
                return Err(SchedulerError::DependencyNotFound);
            }
        }
        
        // 检测环路
        let mut cycle_detector = algo::cycle_detection::CycleDetector::new(&graph);
        if cycle_detector.run() {
            // 移除刚添加的节点和边
            graph.remove_node(node_idx);
            return Err(SchedulerError::CyclicDependency);
        }
        
        Ok(())
    }
    
    // 其他方法...
}
```

### 2. 工作流执行器实现（类似于tokio的调度机制）

```go
// 工作流任务执行器
type WorkflowExecutor struct {
    // 执行器配置
    config ExecutorConfig
    // 任务队列
    taskQueue chan *Task
    // 工作线程
    workers []*Worker
    // 工作线程状态
    workerStatus []atomic.Value
    // 工作流状态缓存
    workflowStateCache *cache.Cache
    // 执行统计
    stats *ExecutorStats
    // 上下文和取消函数
    ctx    context.Context
    cancel context.CancelFunc
    // 盗取策略
    stealStrategy StealStrategy
}

// 执行器配置
type ExecutorConfig struct {
    // 最小工作线程数
    MinWorkers int
    // 最大工作线程数
    MaxWorkers int
    // 任务队列大小
    QueueSize int
    // 工作线程空闲超时
    WorkerIdleTimeout time.Duration
    // 是否启用工作窃取
    EnableWorkStealing bool
    // 盗取策略
    StealStrategy StealStrategy
    // 批处理大小
    BatchSize int
    // 统计收集间隔
    StatsInterval time.Duration
}

// 工作窃取策略
type StealStrategy string

const (
    // 随机窃取
    RandomSteal StealStrategy = "random"
    // 从最忙的工作线程窃取
    BusiestSteal StealStrategy = "busiest"
    // 从相关工作流窃取
    RelatedWorkflowSteal StealStrategy = "related_workflow"
)

// 创建新的工作流执行器
func NewWorkflowExecutor(config ExecutorConfig) *WorkflowExecutor {
    ctx, cancel := context.WithCancel(context.Background())
    
    executor := &WorkflowExecutor{
        config:             config,
        taskQueue:          make(chan *Task, config.QueueSize),
        workers:            make([]*Worker, 0, config.MinWorkers),
        workerStatus:       make([]atomic.Value, config.MaxWorkers),
        workflowStateCache: cache.New(5*time.Minute, 10*time.Minute),
        stats:              NewExecutorStats(),
        ctx:                ctx,
        cancel:             cancel,
        stealStrategy:      config.StealStrategy,
    }
    
    // 初始化工作线程状态
    for i := 0; i < config.MaxWorkers; i++ {
        executor.workerStatus[i].Store(WorkerStatusIdle)
    }
    
    return executor
}

// 启动执行器
func (e *WorkflowExecutor) Start() error {
    // 创建初始工作线程
    for i := 0; i < e.config.MinWorkers; i++ {
        worker := NewWorker(i, e)
        e.workers = append(e.workers, worker)
        go worker.Run()
    }
    
    // 启动自动扩展线程
    go e.autoScale()
    
    // 启动统计收集
    go e.collectStats()
    
    return nil
}

// 提交任务
func (e *WorkflowExecutor) SubmitTask(task *Task) error {
    select {
    case e.taskQueue <- task:
        e.stats.IncrementSubmittedTasks()
        return nil
    default:
        return ErrQueueFull
    }
}

// 工作线程
type Worker struct {
    // 工作线程ID
    id int
    // 所属执行器
    executor *WorkflowExecutor
    // 本地任务队列
    localQueue *TaskQueue
    // 上次窃取时间
    lastStealTime time.Time
    // 已处理任务计数
    processedTasks int64
    // 工作线程上下文
    ctx context.Context
}

// 运行工作线程
func (w *Worker) Run() {
    w.executor.workerStatus[w.id].Store(WorkerStatusRunning)
    defer w.executor.workerStatus[w.id].Store(WorkerStatusStopped)
    
    for {
        // 首先检查本地队列
        task := w.localQueue.Pop()
        
        // 如果本地队列为空，从全局队列获取
        if task == nil {
            select {
            case task = <-w.executor.taskQueue:
                // 获取到一个任务
            case <-time.After(100 * time.Millisecond):
                // 超时，尝试窃取任务
                if w.executor.config.EnableWorkStealing && 
                   time.Since(w.lastStealTime) > 500*time.Millisecond {
                    stolen := w.tryStealTask()
                    if stolen != nil {
                        task = stolen
                        w.lastStealTime = time.Now()
                    }
                }
            case <-w.ctx.Done():
                // 上下文取消，工作线程退出
                return
            }
        }
        
        // 如果获取到任务，执行它
        if task != nil {
            w.executeTask(task)
        }
    }
}

// 尝试从其他工作线程窃取任务
func (w *Worker) tryStealTask() *Task {
    switch w.executor.stealStrategy {
    case RandomSteal:
        // 随机选择一个工作线程
        victimIdx := rand.Intn(len(w.executor.workers))
        victim := w.executor.workers[victimIdx]
        
        // 不要从自己窃取
        if victim.id == w.id {
            return nil
        }
        
        return victim.localQueue.Steal()
        
    case BusiestSteal:
        // 找出任务队列最长的工作线程
        var busiest *Worker
        maxQueueSize := 0
        
        for _, worker := range w.executor.workers {
            if worker.id == w.id {
                continue
            }
            
            queueSize := worker.localQueue.Size()
            if queueSize > maxQueueSize {
                maxQueueSize = queueSize
                busiest = worker
            }
        }
        
        if busiest != nil && maxQueueSize > 0 {
            return busiest.localQueue.Steal()
        }
        
    case RelatedWorkflowSteal:
        // 查找处理相同工作流的工作线程
        currentWorkflows := w.getCurrentWorkflows()
        
        for _, worker := range w.executor.workers {
            if worker.id == w.id {
                continue
            }
            
            // 检查是否有共同的工作流
            victimWorkflows := worker.getCurrentWorkflows()
            
            if haveCommonWorkflow(currentWorkflows, victimWorkflows) && 
               worker.localQueue.Size() > 1 {
                return worker.localQueue.Steal()
            }
        }
    }
    
    return nil
}

// 执行任务
func (w *Worker) executeTask(task *Task) {
    // 更新工作线程状态
    w.executor.workerStatus[w.id].Store(WorkerStatusBusy)
    defer w.executor.workerStatus[w.id].Store(WorkerStatusRunning)
    
    // 记录任务开始执行
    startTime := time.Now()
    w.executor.stats.IncrementRunningTasks()
    
    // 执行任务
    result, err := task.Execute(w.ctx)
    
    // 记录任务执行完成
    execTime := time.Since(startTime)
    w.executor.stats.DecrementRunningTasks()
    w.executor.stats.IncrementCompletedTasks()
    w.executor.stats.RecordTaskExecutionTime(execTime)
    
    atomic.AddInt64(&w.processedTasks, 1)
    
    // 处理任务结果
    w.handleTaskResult(task, result, err)
    
    // 检查后续任务
    w.scheduleNextTasks(task, result)
}

// 获取工作线程当前处理的工作流
func (w *Worker) getCurrentWorkflows() map[string]bool {
    workflows := make(map[string]bool)
    
    // 检查本地队列中的所有任务
    for _, task := range w.localQueue.Tasks() {
        workflows[task.WorkflowID] = true
    }
    
    return workflows
}
```

## 三、工作流拓扑与编排的整合设计

### 1. 工作流拓扑感知编排器

```rust
/// 工作流拓扑感知编排器
pub struct TopologyAwareOrchestrator {
    /// 拓扑存储
    topology_store: Arc<RwLock<WorkflowTopology>>,
    /// 工作流存储
    workflow_store: Arc<WorkflowStore>,
    /// 执行器
    executor: Arc<WorkflowExecutor>,
    /// 调度器
    scheduler: Arc<WorkflowScheduler>,
    /// 编排策略
    orchestration_strategy: OrchestrationStrategy,
    /// 拓扑变更通知
    topology_change_tx: watch::Sender<TopologyChangeEvent>,
    topology_change_rx: watch::Receiver<TopologyChangeEvent>,
    /// 流控制器
    flow_controller: Arc<FlowController>,
    /// 指标收集器
    metrics: Arc<OrchestrationMetrics>,
}

/// 编排策略
pub enum OrchestrationStrategy {
    /// 批处理优先 - 优先执行可批处理的工作流组
    BatchFirst,
    /// 关键路径优先 - 优先执行关键路径上的工作流
    CriticalPathFirst,
    /// 资源感知 - 基于资源利用率优化执行顺序
    ResourceAware,
    /// 自适应 - 根据系统状态动态调整策略
    Adaptive {
        current: Box<OrchestrationStrategy>,
        metrics_window: Duration,
        decision_interval: Duration,
    },
}

/// 工作流拓扑变更事件
pub enum TopologyChangeEvent {
    /// 添加了新的工作流
    WorkflowAdded(WorkflowInstanceId),
    /// 工作流状态变更
    WorkflowStateChanged(WorkflowInstanceId, WorkflowState),
    /// 新增工作流关系
    RelationAdded(WorkflowInstanceId, WorkflowInstanceId, WorkflowRelationType),
    /// 删除工作流关系
    RelationRemoved(WorkflowInstanceId, WorkflowInstanceId, WorkflowRelationType),
    /// 拓扑重建
    TopologyRebuilt,
}

impl TopologyAwareOrchestrator {
    /// 创建新的拓扑感知编排器
    pub fn new(
        workflow_store: Arc<WorkflowStore>,
        executor: Arc<WorkflowExecutor>,
        scheduler: Arc<WorkflowScheduler>,
        strategy: OrchestrationStrategy,
    ) -> Self {
        let (topology_change_tx, topology_change_rx) = watch::channel(TopologyChangeEvent::TopologyRebuilt);
        
        Self {
            topology_store: Arc::new(RwLock::new(WorkflowTopology::new())),
            workflow_store,
            executor,
            scheduler,
            orchestration_strategy: strategy,
            topology_change_tx,
            topology_change_rx,
            flow_controller: Arc::new(FlowController::new(20, 100)), // 默认最大并发20，最大等待100
            metrics: Arc::new(OrchestrationMetrics::new()),
        }
    }
    
    /// 启动编排器
    pub async fn start(&self) -> Result<(), OrchestrationError> {
        // 初始化拓扑
        self.rebuild_topology().await?;
        
        // 启动拓扑监控
        self.start_topology_monitor();
        
        // 启动调度循环
        self.start_orchestration_loop();
        
        // 启动指标收集
        self.start_metrics_collection();
        
        // 启动自适应策略调整（如果使用自适应策略）
        if let OrchestrationStrategy::Adaptive { decision_interval, .. } = &self.orchestration_strategy {
            self.start_adaptive_strategy_adjustment(*decision_interval);
        }
        
        Ok(())
    }
    
    /// 重建工作流拓扑
    async fn rebuild_topology(&self) -> Result<(), OrchestrationError> {
        let workflows = self.workflow_store.get_all_workflows().await?;
        let mut topology = WorkflowTopology::new();
        
        for workflow in workflows {
            topology.add_workflow(&workflow);
            
            // 添加工作流关系
            let relations = self.workflow_store.get_workflow_relations(&workflow.id).await?;
            for relation in relations {
                topology.add_relation(
                    relation.source_id,
                    relation.target_id,
                    relation.relation_type,
                );
            }
        }
        
        // 更新拓扑存储
        let mut ts = self.topology_store.write().await;
        *ts = topology;
        
        // 通知拓扑变更
        let _ = self.topology_change_tx.send(TopologyChangeEvent::TopologyRebuilt);
        
        Ok(())
    }
    
    /// 启动拓扑监控循环
    fn start_topology_monitor(&self) {
        let workflow_store = self.workflow_store.clone();
        let topology_store = self.topology_store.clone();
        let topology_change_tx = self.topology_change_tx.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(10));
            
            loop {
                interval.tick().await;
                
                // 检查工作流状态变化
                if let Ok(changes) = workflow_store.get_recent_changes().await {
                    for change in changes {
                        match change {
                            WorkflowChange::Added(wf) => {
                                let mut topo = topology_store.write().await;
                                topo.add_workflow(&wf);
                                let _ = topology_change_tx.send(TopologyChangeEvent::WorkflowAdded(wf.id));
                            }
                            WorkflowChange::StateChanged(id, state) => {
                                let _ = topology_change_tx.send(
                                    TopologyChangeEvent::WorkflowStateChanged(id, state)
                                );
                            }
                            WorkflowChange::RelationAdded(source, target, rel_type) => {
                                let mut topo = topology_store.write().await;
                                topo.add_relation(source.clone(), target.clone(), rel_type);
                                let _ = topology_change_tx.send(
                                    TopologyChangeEvent::RelationAdded(source, target, rel_type)
                                );
                            }
                            WorkflowChange::RelationRemoved(source, target, rel_type) => {
                                let mut topo = topology_store.write().await;
                                topo.remove_relation(&source, &target, rel_type);
                                let _ = topology_change_tx.send(
                                    TopologyChangeEvent::RelationRemoved(source, target, rel_type)
                                );
                            }
                        }
                    }
                }
            }
        });
    }
    
    /// 启动编排循环
    fn start_orchestration_loop(&self) {
        let scheduler = self.scheduler.clone();
        let topology_store = self.topology_store.clone();
        let workflow_store = self.workflow_store.clone();
        let strategy = self.orchestration_strategy.clone();
        let mut topology_change_rx = self.topology_change_rx.clone();
        let flow_controller = self.flow_controller.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            loop {
                // 等待拓扑变更或定时唤醒
                let _changed = tokio::select! {
                    _ = topology_change_rx.changed() => true,
                    _ = tokio::time::sleep(Duration::from_millis(500)) => false,
                };
                
                // 获取待调度的工作流
                let pending_workflows = match workflow_store.get_pending_workflows().await {
                    Ok(wfs) => wfs,
                    Err(e) => {
                        eprintln!("获取待调度工作流失败: {:?}", e);
                        continue;
                    }
                };
                
                if pending_workflows.is_empty() {
                    continue;
                }
                
                // 根据编排策略和拓扑结构确定调度顺序
                let topo = topology_store.read().await;
                let orchestrated = orchestrate_workflows(
                    &pending_workflows,
                    &topo,
                    &strategy,
                );
                
                // 提交任务到调度器
                for workflow in orchestrated {
                    // 使用流控制器控制并发
                    if !flow_controller.try_acquire().await {
                        // 达到最大并发，等待下一轮调度
                        break;
                    }
                    
                    // 创建任务并提交
                    let flow_controller_clone = flow_controller.clone();
                    let metrics_clone = metrics.clone();
                    let start_time = Instant::now();
                    
                    if let Err(e) = scheduler.submit(create_workflow_task(&workflow, move || {
                        // 任务完成后释放流控制资源
                        flow_controller_clone.release();
                        
                        // 记录指标
                        let duration = start_time.elapsed();
                        metrics_clone.record_workflow_execution(&workflow.id, duration);
                    })) {
                        eprintln!("提交工作流任务失败: {:?}, workflow: {:?}", e, workflow.id);
                        // 释放获取的流控制资源
                        flow_controller.release();
                    } else {
                        // 记录调度事件
                        metrics.record_workflow_scheduled(&workflow.id);
                    }
                }
            }
        });
    }
    
    /// 启动自适应策略调整
    fn start_adaptive_strategy_adjustment(&self, interval: Duration) {
        let metrics = self.metrics.clone();
        let this = self.clone();
        
        tokio::spawn(async move {
            let mut adjustment_interval = tokio::time::interval(interval);
            
            loop {
                adjustment_interval.tick().await;
                
                // 获取执行指标
                let execution_stats = metrics.get_recent_stats();
                
                // 基于指标调整策略
                if let OrchestrationStrategy::Adaptive { ref mut current, .. } = this.orchestration_strategy {
                    *current = select_optimal_strategy(&execution_stats);
                }
            }
        });
    }
}

/// 基于拓扑和策略编排工作流
fn orchestrate_workflows(
    workflows: &[Workflow],
    topology: &WorkflowTopology,
    strategy: &OrchestrationStrategy,
) -> Vec<Workflow> {
    match strategy {
        OrchestrationStrategy::BatchFirst => {
            // 识别可以批处理的工作流组
            let workflow_groups = identify_batchable_workflows(workflows, topology);
            flatten_workflow_groups(workflow_groups)
        }
        OrchestrationStrategy::CriticalPathFirst => {
            // 计算关键路径
            let critical_paths = topology.calculate_critical_paths();
            // 按关键路径排序
            sort_by_critical_path(workflows, &critical_paths)
        }
        OrchestrationStrategy::ResourceAware => {
            // 基于资源需求编排
            sort_by_resource_availability(workflows)
        }
        OrchestrationStrategy::Adaptive { current, .. } => {
            // 使用当前选定的策略
            orchestrate_workflows(workflows, topology, current)
        }
    }
}

/// 流控制器 - 控制并发工作流数量
pub struct FlowController {
    /// 信号量控制并发
    semaphore: Semaphore,
    /// 最大并发数
    max_concurrent: usize,
    /// 最大等待数
    max_pending: usize,
    /// 当前等待数
    pending_count: AtomicUsize,
}

impl FlowController {
    /// 创建新的流控制器
    pub fn new(max_concurrent: usize, max_pending: usize) -> Self {
        Self {
            semaphore: Semaphore::new(max_concurrent),
            max_concurrent,
            max_pending,
            pending_count: AtomicUsize::new(0),
        }
    }
    
    /// 尝试获取执行许可
    pub async fn try_acquire(&self) -> bool {
        // 检查是否超过最大等待数
        let current_pending = self.pending_count.fetch_add(1, Ordering::SeqCst);
        if current_pending >= self.max_pending {
            self.pending_count.fetch_sub(1, Ordering::SeqCst);
            return false;
        }
        
        // 尝试获取信号量
        let permit = match self.semaphore.acquire().await {
            Ok(permit) => permit,
            Err(_) => {
                self.pending_count.fetch_sub(1, Ordering::SeqCst);
                return false;
            }
        };
        
        // 减少等待计数
        self.pending_count.fetch_sub(1, Ordering::SeqCst);
        
        // 将许可转移到静态生命周期，稍后释放
        std::mem::forget(permit);
        true
    }
    
    /// 释放执行许可
    pub fn release(&self) {
        self.semaphore.add_permits(1);
    }
}
```

### 2. 工作流拓扑优化器

```go
// 工作流拓扑优化器
type TopologyOptimizer struct {
    // 工作流定义仓库
    workflowRepo WorkflowRepository
    // 执行历史查询
    executionHistory ExecutionHistoryQuery
    // 优化配置
    config OptimizerConfig
    // 优化建议存储
    suggestionsRepo OptimizationSuggestionRepository
    // 拓扑分析引擎
    topologyAnalyzer TopologyAnalyzer
    // 指标收集器
    metrics *metrics.OptimizationMetrics
}

// 优化器配置
type OptimizerConfig struct {
    // 最大合并深度
    MaxMergeDepth int
    // 最小执行频率（触发优化）
    MinExecutionFrequency int
    // 最小优化收益百分比
    MinOptimizationGain float64
    // 最大链长度
    MaxChainLength int
    // 是否启用自动应用
    EnableAutoApply bool
    // 优化间隔
    OptimizationInterval time.Duration
}

// 创建拓扑优化器
func NewTopologyOptimizer(
    repo WorkflowRepository,
    history ExecutionHistoryQuery,
    config OptimizerConfig,
    suggestions OptimizationSuggestionRepository,
) *TopologyOptimizer {
    return &TopologyOptimizer{
        workflowRepo: repo,
        executionHistory: history,
        config: config,
        suggestionsRepo: suggestions,
        topologyAnalyzer: NewTopologyAnalyzer(),
        metrics: metrics.NewOptimizationMetrics(),
    }
}

// 启动优化器
func (o *TopologyOptimizer) Start(ctx context.Context) error {
    ticker := time.NewTicker(o.config.OptimizationInterval)
    defer ticker.Stop()
    
    log.Info("拓扑优化器已启动")
    
    for {
        select {
        case <-ticker.C:
            err := o.runOptimizationCycle(ctx)
            if err != nil {
                log.Error("优化周期执行失败", "error", err)
            }
        case <-ctx.Done():
            log.Info("拓扑优化器正在关闭")
            return ctx.Err()
        }
    }
}

// 运行一个优化周期
func (o *TopologyOptimizer) runOptimizationCycle(ctx context.Context) error {
    start := time.Now()
    log.Info("开始拓扑优化周期")
    
    // 1. 获取所有工作流定义
    workflows, err := o.workflowRepo.GetAllWorkflows(ctx)
    if err != nil {
        return fmt.Errorf("获取工作流失败: %w", err)
    }
    
    // 2. 构建拓扑图
    topology, err := o.buildTopology(ctx, workflows)
    if err != nil {
        return fmt.Errorf("构建拓扑图失败: %w", err)
    }
    
    // 3. 分析拓扑的优化机会
    optimizationOpportunities, err := o.topologyAnalyzer.AnalyzeTopology(ctx, topology)
    if err != nil {
        return fmt.Errorf("分析拓扑优化机会失败: %w", err)
    }
    
    // 4. 过滤和排序优化机会
    filteredOpportunities := o.filterOpportunities(optimizationOpportunities)
    
    // 5. 生成优化建议
    suggestions, err := o.generateOptimizationSuggestions(ctx, filteredOpportunities, topology)
    if err != nil {
        return fmt.Errorf("生成优化建议失败: %w", err)
    }
    
    // 6. 存储优化建议
    err = o.suggestionsRepo.SaveSuggestions(ctx, suggestions)
    if err != nil {
        return fmt.Errorf("存储优化建议失败: %w", err)
    }
    
    // 7. 如果启用自动应用，应用优先级最高的建议
    if o.config.EnableAutoApply && len(suggestions) > 0 {
        topSuggestion := suggestions[0]
        err = o.applyOptimizationSuggestion(ctx, topSuggestion)
        if err != nil {
            log.Error("应用优化建议失败", "suggestionId", topSuggestion.ID, "error", err)
        } else {
            log.Info("成功应用优化建议", "suggestionId", topSuggestion.ID)
        }
    }
    
    duration := time.Since(start)
    log.Info("完成拓扑优化周期", 
        "duration", duration, 
        "opportunitiesFound", len(optimizationOpportunities),
        "suggestionsGenerated", len(suggestions))
    
    o.metrics.RecordOptimizationCycle(duration, len(optimizationOpportunities), len(suggestions))
    
    return nil
}

// 构建工作流拓扑
func (o *TopologyOptimizer) buildTopology(ctx context.Context, workflows []Workflow) (*WorkflowTopology, error) {
    topology := NewWorkflowTopology()
    
    // 添加所有工作流
    for _, wf := range workflows {
        topology.AddWorkflow(wf)
    }
    
    // 添加工作流间关系
    for _, wf := range workflows {
        // 获取调用关系
        callRelations, err := o.workflowRepo.GetWorkflowCallRelations(ctx, wf.ID)
        if err != nil {
            return nil, err
        }
        
        for _, relation := range callRelations {
            topology.AddRelation(relation.SourceID, relation.TargetID, relation.RelationType)
        }
        
        // 获取数据依赖关系
        dataRelations, err := o.workflowRepo.GetWorkflowDataDependencies(ctx, wf.ID)
        if err != nil {
            return nil, err
        }
        
        for _, relation := range dataRelations {
            topology.AddRelation(relation.SourceID, relation.TargetID, WorkflowRelationTypeDataDependency)
        }
    }
    
    // 获取执行频率数据
    execData, err := o.executionHistory.GetExecutionFrequencyData(ctx, time.Now().AddDate(0, -1, 0))
    if err != nil {
        return nil, err
    }
    
    // 设置执行频率信息
    for wfID, frequency := range execData {
        topology.SetWorkflowMetadata(wfID, "execution_frequency", frequency)
    }
    
    // 获取平均执行时间数据
    execTimeData, err := o.executionHistory.GetAverageExecutionTimeData(ctx, time.Now().AddDate(0, -1, 0))
    if err != nil {
        return nil, err
    }
    
    // 设置执行时间信息
    for wfID, execTime := range execTimeData {
        topology.SetWorkflowMetadata(wfID, "average_execution_time", execTime)
    }
    
    // 获取并发执行数据
    concurrencyData, err := o.executionHistory.GetConcurrentExecutionData(ctx, time.Now().AddDate(0, -1, 0))
    if err != nil {
        return nil, err
    }
    
    // 设置并发执行信息
    for wfID, concurrency := range concurrencyData {
        topology.SetWorkflowMetadata(wfID, "max_concurrency", concurrency)
    }
    
    return topology, nil
}

// 过滤优化机会
func (o *TopologyOptimizer) filterOpportunities(opportunities []OptimizationOpportunity) []OptimizationOpportunity {
    // 按照预期收益排序
    sort.Slice(opportunities, func(i, j int) bool {
        return opportunities[i].EstimatedGain > opportunities[j].EstimatedGain
    })
    
    // 过滤掉收益低于阈值的机会
    var filtered []OptimizationOpportunity
    for _, opp := range opportunities {
        if opp.EstimatedGain >= o.config.MinOptimizationGain {
            filtered = append(filtered, opp)
        }
    }
    
    return filtered
}

// 生成优化建议
func (o *TopologyOptimizer) generateOptimizationSuggestions(
    ctx context.Context, 
    opportunities []OptimizationOpportunity,
    topology *WorkflowTopology,
) ([]OptimizationSuggestion, error) {
    var suggestions []OptimizationSuggestion
    
    for _, opp := range opportunities {
        switch opp.Type {
        case OpportunityTypeMerge:
            suggestion, err := o.generateMergeSuggestion(ctx, opp, topology)
            if err != nil {
                log.Error("生成合并建议失败", "opportunity", opp.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
            
        case OpportunityTypeSplit:
            suggestion, err := o.generateSplitSuggestion(ctx, opp, topology)
            if err != nil {
                log.Error("生成拆分建议失败", "opportunity", opp.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
            
        case OpportunityTypeChain:
            suggestion, err := o.generateChainSuggestion(ctx, opp, topology)
            if err != nil {
                log.Error("生成链接建议失败", "opportunity", opp.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
            
        case OpportunityTypeParallelize:
            suggestion, err := o.generateParallelizeSuggestion(ctx, opp, topology)
            if err != nil {
                log.Error("生成并行化建议失败", "opportunity", opp.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
        }
    }
    
    return suggestions, nil
}

// 生成工作流合并建议
func (o *TopologyOptimizer) generateMergeSuggestion(
    ctx context.Context,
    opportunity OptimizationOpportunity,
    topology *WorkflowTopology,
) (OptimizationSuggestion, error) {
    // 获取要合并的工作流
    workflowIDs := opportunity.AffectedWorkflows
    workflows := make([]Workflow, 0, len(workflowIDs))
    
    for _, id := range workflowIDs {
        wf, err := o.workflowRepo.GetWorkflowByID(ctx, id)
        if err != nil {
            return OptimizationSuggestion{}, err
        }
        workflows = append(workflows, wf)
    }
    
    // 生成合并后的工作流定义
    mergedWorkflow, err := o.generateMergedWorkflowDefinition(workflows)
    if err != nil {
        return OptimizationSuggestion{}, err
    }
    
    // 估算合并收益
    detailedGainAnalysis := o.estimateMergeGain(workflows, topology)
    
    return OptimizationSuggestion{
        ID:                uuid.New().String(),
        CreatedAt:         time.Now(),
        Type:              SuggestionTypeMerge,
        AffectedWorkflows: workflowIDs,
        EstimatedGain:     opportunity.EstimatedGain,
        GainAnalysis:      detailedGainAnalysis,
        Description:       fmt.Sprintf("将 %d 个工作流合并为一个工作流以减少调度开销", len(workflowIDs)),
        Justification:     opportunity.Justification,
        ProposedChanges: ProposedChanges{
            NewWorkflows: []Workflow{mergedWorkflow},
            DeleteWorkflows: workflowIDs,
        },
        Risk:             o.assessMergeRisk(workflows),
        ImplementationComplexity: calculateImplementationComplexity(workflows),
        Status:           SuggestionStatusPending,
    }, nil
}
```

### 3. 分层工作流结构模型

```go
// 工作流层次类型
type WorkflowTierType string

const (
    // 应用层 - 业务功能直接映射
    ApplicationTier WorkflowTierType = "application"
    // 领域层 - 领域逻辑编排
    DomainTier WorkflowTierType = "domain"
    // 基础设施层 - 系统功能封装
    InfrastructureTier WorkflowTierType = "infrastructure"
    // 自治层 - 系统自我管理
    AutonomousTier WorkflowTierType = "autonomous"
)

// 分层工作流结构
type TieredWorkflowArchitecture struct {
    // 层次拓扑
    tierTopology map[WorkflowTierType]*WorkflowTopology
    // 层次间关系
    crossTierRelations []CrossTierRelation
    // 层次策略
    tierPolicies map[WorkflowTierType]TierPolicy
    // 层次优先级（从高到低）
    tierPriorities []WorkflowTierType
}

// 跨层关系
type CrossTierRelation struct {
    SourceTier      WorkflowTierType
    SourceWorkflowID string
    TargetTier      WorkflowTierType
    TargetWorkflowID string
    RelationType    WorkflowRelationType
}

// 层次策略
type TierPolicy struct {
    // 最大并发执行数
    MaxConcurrency int
    // 资源分配百分比
    ResourceAllocation float64
    // 默认优先级
    DefaultPriority int
    // 最大执行时间
    MaxExecutionTime time.Duration
    // 故障隔离设置
    FailureIsolation FailureIsolationPolicy
    // 调度策略
    SchedulingPolicy SchedulingPolicyType
}

// 创建分层工作流架构
func NewTieredWorkflowArchitecture() *TieredWorkflowArchitecture {
    // 默认层次优先级（从高到低）
    defaultPriorities := []WorkflowTierType{
        ApplicationTier,
        DomainTier,
        InfrastructureTier,
        AutonomousTier,
    }
    
    // 初始化层次拓扑
    tierTopology := make(map[WorkflowTierType]*WorkflowTopology)
    for _, tier := range defaultPriorities {
        tierTopology[tier] = NewWorkflowTopology()
    }
    
    // 默认层次策略
    tierPolicies := map[WorkflowTierType]TierPolicy{
        ApplicationTier: {
            MaxConcurrency:     100,
            ResourceAllocation: 0.5,
            DefaultPriority:    100,
            MaxExecutionTime:   30 * time.Minute,
            FailureIsolation:   FailureIsolationPolicyStrict,
            SchedulingPolicy:   UserPriorityScheduling,
        },
        DomainTier: {
            MaxConcurrency:     200,
            ResourceAllocation: 0.3,
            DefaultPriority:    80,
            MaxExecutionTime:   15 * time.Minute,
            FailureIsolation:   FailureIsolationPolicyDefault,
            SchedulingPolicy:   FairShareScheduling,
        },
        InfrastructureTier: {
            MaxConcurrency:     300,
            ResourceAllocation: 0.15,
            DefaultPriority:    60,
            MaxExecutionTime:   5 * time.Minute,
            FailureIsolation:   FailureIsolationPolicyDefault,
            SchedulingPolicy:   ResourceAwareScheduling,
        },
        AutonomousTier: {
            MaxConcurrency:     50,
            ResourceAllocation: 0.05,
            DefaultPriority:    40,
            MaxExecutionTime:   10 * time.Minute,
            FailureIsolation:   FailureIsolationPolicyLenient,
            SchedulingPolicy:   BackgroundScheduling,
        },
    }
    
    return &TieredWorkflowArchitecture{
        tierTopology:      tierTopology,
        crossTierRelations: []CrossTierRelation{},
        tierPolicies:      tierPolicies,
        tierPriorities:    defaultPriorities,
    }
}

// 向分层架构中添加工作流
func (t *TieredWorkflowArchitecture) AddWorkflow(
    workflow Workflow,
    tier WorkflowTierType,
) error {
    topology, exists := t.tierTopology[tier]
    if !exists {
        return fmt.Errorf("未知的工作流层次: %s", tier)
    }
    
    // 添加到对应层次的拓扑
    topology.AddWorkflow(workflow)
    
    return nil
}

// 添加层内工作流关系
func (t *TieredWorkflowArchitecture) AddIntraTierRelation(
    tier WorkflowTierType,
    sourceID string,
    targetID string,
    relationType WorkflowRelationType,
) error {
    topology, exists := t.tierTopology[tier]
    if !exists {
        return fmt.Errorf("未知的工作流层次: %s", tier)
    }
    
    // 添加层内关系
    topology.AddRelation(sourceID, targetID, relationType)
    
    return nil
}

// 添加跨层工作流关系
func (t *TieredWorkflowArchitecture) AddCrossTierRelation(
    sourceTier WorkflowTierType,
    sourceID string,
    targetTier WorkflowTierType,
    targetID string,
    relationType WorkflowRelationType,
) error {
    // 验证层次存在
    if _, exists := t.tierTopology[sourceTier]; !exists {
        return fmt.Errorf("未知的源工作流层次: %s", sourceTier)
    }
    if _, exists := t.tierTopology[targetTier]; !exists {
        return fmt.Errorf("未知的目标工作流层次: %s", targetTier)
    }
    
    // 验证工作流存在
    if !t.tierTopology[sourceTier].HasWorkflow(sourceID) {
        return fmt.Errorf("源层次 %s 中不存在工作流 %s", sourceTier, sourceID)
    }
    if !t.tierTopology[targetTier].HasWorkflow(targetID) {
        return fmt.Errorf("目标层次 %s 中不存在工作流 %s", targetTier, targetID)
    }
    
    // 添加跨层关系
    relation := CrossTierRelation{
        SourceTier:      sourceTier,
        SourceWorkflowID: sourceID,
        TargetTier:      targetTier,
        TargetWorkflowID: targetID,
        RelationType:    relationType,
    }
    
    t.crossTierRelations = append(t.crossTierRelations, relation)
    
    return nil
}

// 获取工作流所在层次
func (t *TieredWorkflowArchitecture) GetWorkflowTier(workflowID string) (WorkflowTierType, bool) {
    for tier, topology := range t.tierTopology {
        if topology.HasWorkflow(workflowID) {
            return tier, true
        }
    }
    
    return "", false
}

// 获取工作流的执行策略
func (t *TieredWorkflowArchitecture) GetWorkflowExecutionPolicy(workflowID string) (TierPolicy, error) {
    tier, found := t.GetWorkflowTier(workflowID)
    if !found {
        return TierPolicy{}, fmt.Errorf("未找到工作流 %s", workflowID)
    }
    
    policy, exists := t.tierPolicies[tier]
    if !exists {
        return TierPolicy{}, fmt.Errorf("层次 %s 没有定义执行策略", tier)
    }
    
    return policy, nil
}

// 构建完整的工作流依赖图（包括跨层依赖）
func (t *TieredWorkflowArchitecture) BuildCompleteDependencyGraph() (*graph.DirectedGraph, error) {
    // 创建一个新的有向图
    dependencyGraph := graph.NewDirectedGraph()
    
    // 添加所有工作流作为节点
    for tier, topology := range t.tierTopology {
        for _, workflow := range topology.GetAllWorkflows() {
            // 节点ID格式: "tier:workflowID"
            nodeID := fmt.Sprintf("%s:%s", tier, workflow.ID)
            dependencyGraph.AddNode(nodeID, workflow)
        }
    }
    
    // 添加层内关系作为边
    for tier, topology := range t.tierTopology {
        relations := topology.GetAllRelations()
        for _, relation := range relations {
            sourceNodeID := fmt.Sprintf("%s:%s", tier, relation.SourceID)
            targetNodeID := fmt.Sprintf("%s:%s", tier, relation.TargetID)
            
            dependencyGraph.AddEdge(sourceNodeID, targetNodeID, relation.RelationType)
        }
    }
    
    // 添加跨层关系作为边
    for _, relation := range t.crossTierRelations {
        sourceNodeID := fmt.Sprintf("%s:%s", relation.SourceTier, relation.SourceWorkflowID)
        targetNodeID := fmt.Sprintf("%s:%s", relation.TargetTier, relation.TargetWorkflowID)
        
        dependencyGraph.AddEdge(sourceNodeID, targetNodeID, relation.RelationType)
    }
    
    return dependencyGraph, nil
}

// 验证跨层依赖的合法性
func (t *TieredWorkflowArchitecture) ValidateCrossTierDependencies() []ValidationIssue {
    var issues []ValidationIssue
    
    // 获取层次优先级映射
    tierPriorityMap := make(map[WorkflowTierType]int)
    for i, tier := range t.tierPriorities {
        tierPriorityMap[tier] = i
    }
    
    // 检查跨层关系
    for _, relation := range t.crossTierRelations {
        sourceTierPriority := tierPriorityMap[relation.SourceTier]
        targetTierPriority := tierPriorityMap[relation.TargetTier]
        
        // 检查是否违反层次优先级
        // 通常高优先级层不应依赖低优先级层
        if sourceTierPriority < targetTierPriority {
            issues = append(issues, ValidationIssue{
                Type:        "cross_tier_dependency_violation",
                Severity:    "warning",
                Description: fmt.Sprintf(
                    "高优先级层 %s 的工作流 %s 依赖低优先级层 %s 的工作流 %s",
                    relation.SourceTier,
                    relation.SourceWorkflowID,
                    relation.TargetTier,
                    relation.TargetWorkflowID,
                ),
                AffectedWorkflows: []string{relation.SourceWorkflowID, relation.TargetWorkflowID},
            })
        }
        
        // 检查自治层的依赖
        if relation.SourceTier == AutonomousTier && relation.TargetTier != AutonomousTier {
            issues = append(issues, ValidationIssue{
                Type:        "autonomous_tier_external_dependency",
                Severity:    "info",
                Description: fmt.Sprintf(
                    "自治层工作流 %s 依赖非自治层 %s 的工作流 %s",
                    relation.SourceWorkflowID,
                    relation.TargetTier,
                    relation.TargetWorkflowID,
                ),
                AffectedWorkflows: []string{relation.SourceWorkflowID, relation.TargetWorkflowID},
            })
        }
    }
    
    return issues
}

// 执行分层工作流调度
func (t *TieredWorkflowArchitecture) ScheduleWorkflows(
    scheduler WorkflowScheduler,
    pendingWorkflows []Workflow,
) error {
    // 按层次划分待调度的工作流
    workflowsByTier := make(map[WorkflowTierType][]Workflow)
    
    for _, workflow := range pendingWorkflows {
        tier, found := t.GetWorkflowTier(workflow.ID)
        if !found {
            return fmt.Errorf("未找到工作流 %s 所在的层次", workflow.ID)
        }
        
        if _, exists := workflowsByTier[tier]; !exists {
            workflowsByTier[tier] = []Workflow{}
        }
        
        workflowsByTier[tier] = append(workflowsByTier[tier], workflow)
    }
    
    // 按层次优先级调度
    for _, tier := range t.tierPriorities {
        workflows, exists := workflowsByTier[tier]
        if !exists || len(workflows) == 0 {
            continue
        }
        
        policy := t.tierPolicies[tier]
        tierTopology := t.tierTopology[tier]
        
        // 根据层次策略进行调度
        switch policy.SchedulingPolicy {
        case UserPriorityScheduling:
            // 按用户定义的优先级排序
            sort.Slice(workflows, func(i, j int) bool {
                return workflows[i].Priority > workflows[j].Priority
            })
            
        case FairShareScheduling:
            // 平衡不同用户/服务的资源使用
            workflows = applyFairShareScheduling(workflows)
            
        case ResourceAwareScheduling:
            // 考虑资源使用的调度
            workflows = applyResourceAwareScheduling(workflows, tierTopology)
            
        case BackgroundScheduling:
            // 仅在系统空闲时运行
            if isSystemBusy() {
                // 跳过调度此层次的工作流
                continue
            }
        }
        
        // 调度该层次的工作流
        for _, workflow := range workflows {
            // 检查层次并发限制
            if scheduler.GetRunningCount(tier) >= policy.MaxConcurrency {
                // 此层次已达最大并发，停止调度
                break
            }
            
            err := scheduler.Schedule(workflow, ScheduleOptions{
                Tier:           tier,
                MaxExecutionTime: policy.MaxExecutionTime,
                Priority:       workflow.Priority,
                DefaultPriority: policy.DefaultPriority,
            })
            
            if err != nil {
                log.Error("调度工作流失败", 
                    "tier", tier, 
                    "workflowID", workflow.ID, 
                    "error", err)
            }
        }
    }
    
    return nil
}
```

## 四、工作流递归模型与拓扑感知调度

### 1. 递归工作流结构

在复杂的智能家居系统中，许多工作流本质上具有递归特性，比如分层场景触发、层叠式规则执行等。
以下是一个递归工作流结构的设计：

```rust
/// 递归工作流定义
pub struct RecursiveWorkflow {
    /// 工作流基本信息
    pub base: WorkflowBase,
    /// 递归策略
    pub recursion_strategy: RecursionStrategy,
    /// 子问题分解器
    pub decomposer: Box<dyn SubproblemDecomposer>,
    /// 结果合并器
    pub result_merger: Box<dyn ResultMerger>,
    /// 终止条件
    pub termination_condition: Box<dyn TerminationCondition>,
    /// 最大递归深度
    pub max_depth: usize,
    /// 执行策略
    pub execution_strategy: RecursiveExecutionStrategy,
}

/// 递归执行策略
pub enum RecursiveExecutionStrategy {
    /// 深度优先 - 先完成一个分支再处理其他分支
    DepthFirst,
    /// 广度优先 - 同一层次的子问题并行处理
    BreadthFirst,
    /// 混合策略 - 根据问题特性动态选择
    Hybrid {
        /// 深度优先的阈值
        depth_threshold: usize,
        /// 子问题并行阈值
        parallelism_threshold: usize,
    },
    /// 自适应策略 - 根据系统负载和问题特性调整
    Adaptive,
}

/// 递归工作流执行器
pub struct RecursiveWorkflowExecutor {
    /// 工作流定义
    workflow: RecursiveWorkflow,
    /// 执行上下文
    context: ExecutionContext,
    /// 执行追踪器
    tracer: RecursionTracer,
    /// 资源控制器
    resource_controller: ResourceController,
}

impl RecursiveWorkflowExecutor {
    /// 执行递归工作流
    pub async fn execute(&mut self, input: WorkflowInput) -> Result<WorkflowOutput, WorkflowError> {
        // 初始化追踪器
        self.tracer.start_trace();
        
        // 执行根问题
        let result = self.execute_recursive(input, 0).await?;
        
        // 完成追踪
        self.tracer.complete_trace();
        
        Ok(result)
    }
    
    /// 递归执行子问题
    async fn execute_recursive(&mut self, input: WorkflowInput, depth: usize) -> Result<WorkflowOutput, WorkflowError> {
        // 检查递归深度
        if depth >= self.workflow.max_depth {
            return Err(WorkflowError::MaxDepthExceeded(depth));
        }
        
        // 记录当前层次执行开始
        self.tracer.trace_step_begin(depth, &input);
        
        // 检查终止条件
        if self.workflow.termination_condition.should_terminate(&input, depth) {
            let result = self.execute_base_workflow(input.clone()).await?;
            self.tracer.trace_step_end(depth, &result);
            return Ok(result);
        }
        
        // 分解为子问题
        let subproblems = self.workflow.decomposer.decompose(&input, depth)?;
        
        if subproblems.is_empty() {
            // 无法进一步分解，执行基础工作流
            let result = self.execute_base_workflow(input).await?;
            self.tracer.trace_step_end(depth, &result);
            return Ok(result);
        }
        
        // 根据执行策略处理子问题
        let subresults = match &self.workflow.execution_strategy {
            RecursiveExecutionStrategy::DepthFirst => {
                self.execute_depth_first(subproblems, depth).await?
            }
            RecursiveExecutionStrategy::BreadthFirst => {
                self.execute_breadth_first(subproblems, depth).await?
            }
            RecursiveExecutionStrategy::Hybrid { depth_threshold, parallelism_threshold } => {
                if depth >= *depth_threshold || subproblems.len() <= *parallelism_threshold {
                    self.execute_depth_first(subproblems, depth).await?
                } else {
                    self.execute_breadth_first(subproblems, depth).await?
                }
            }
            RecursiveExecutionStrategy::Adaptive => {
                // 根据系统负载和问题特性动态选择策略
                if self.resource_controller.is_system_busy() || depth > 3 {
                    self.execute_depth_first(subproblems, depth).await?
                } else {
                    self.execute_breadth_first(subproblems, depth).await?
                }
            }
        };
        
        // 合并子问题结果
        let merged_result = self.workflow.result_merger.merge(subresults, &input)?;
        
        // 记录当前层次执行结束
        self.tracer.trace_step_end(depth, &merged_result);
        
        Ok(merged_result)
    }
    
    /// 深度优先执行子问题
    async fn execute_depth_first(&mut self, subproblems: Vec<WorkflowInput>, depth: usize) 
        -> Result<Vec<WorkflowOutput>, WorkflowError> {
        let mut results = Vec::with_capacity(subproblems.len());
        
        for (idx, subproblem) in subproblems.into_iter().enumerate() {
            self.tracer.trace_subproblem_begin(depth, idx, &subproblem);
            
            match self.execute_recursive(subproblem, depth + 1).await {
                Ok(result) => {
                    results.push(result);
                    self.tracer.trace_subproblem_success(depth, idx);
                }
                Err(err) => {
                    self.tracer.trace_subproblem_error(depth, idx, &err);
                    
                    // 根据失败策略处理
                    match self.workflow.recursion_strategy.error_strategy {
                        ErrorStrategy::FailFast => return Err(err),
                        ErrorStrategy::ContinueOnError => continue,
                        ErrorStrategy::PartialResults => {
                            // 添加错误占位符
                            results.push(WorkflowOutput::error_placeholder());
                        }
                    }
                }
            }
        }
        
        Ok(results)
    }
    
    /// 广度优先执行子问题
    async fn execute_breadth_first(&mut self, subproblems: Vec<WorkflowInput>, depth: usize) 
        -> Result<Vec<WorkflowOutput>, WorkflowError> {
        // 准备任务
        let mut tasks = Vec::with_capacity(subproblems.len());
        
        // 获取可用并行度
        let available_parallelism = self.resource_controller.get_available_parallelism();
        let batch_size = std::cmp::min(available_parallelism, subproblems.len());
        
        self.tracer.trace_parallel_execution_begin(depth, batch_size);
        
        // 创建子任务
        for (idx, subproblem) in subproblems.into_iter().enumerate() {
            let mut executor_clone = self.clone();
            
            tasks.push(async move {
                executor_clone.tracer.trace_subproblem_begin(depth, idx, &subproblem);
                let result = executor_clone.execute_recursive(subproblem, depth + 1).await;
                
                match &result {
                    Ok(_) => executor_clone.tracer.trace_subproblem_success(depth, idx),
                    Err(err) => executor_clone.tracer.trace_subproblem_error(depth, idx, err),
                }
                
                (idx, result)
            });
        }
        
        // 执行所有子问题
        let results = futures::future::join_all(tasks).await;
        
        self.tracer.trace_parallel_execution_end(depth);
        
        // 处理结果
        let mut outputs = vec![None; results.len()];
        let mut has_error = false;
        
        for (idx, result) in results {
            match result {
                Ok(output) => {
                    outputs[idx] = Some(output);
                }
                Err(err) => {
                    has_error = true;
                    
                    // 根据失败策略处理
                    match self.workflow.recursion_strategy.error_strategy {
                        ErrorStrategy::FailFast => return Err(err),
                        ErrorStrategy::ContinueOnError => {},
                        ErrorStrategy::PartialResults => {
                            outputs[idx] = Some(WorkflowOutput::error_placeholder());
                        }
                    }
                }
            }
        }
        
        // 如果存在错误且策略是继续执行，则过滤掉失败结果
        let final_results = if has_error && self.workflow.recursion_strategy.error_strategy == ErrorStrategy::ContinueOnError {
            outputs.into_iter().filter_map(|x| x).collect()
        } else {
            outputs.into_iter().map(|x| x.unwrap()).collect()
        };
        
        Ok(final_results)
    }
}
```

### 2. 拓扑感知调度器实现

以下是一个针对智能家居系统工作流拓扑结构特点的调度器实现：

```go
// 拓扑感知调度器
type TopologyAwareScheduler struct {
    // 工作流拓扑结构
    topology *WorkflowTopology
    // 分层工作流架构
    tieredArchitecture *TieredWorkflowArchitecture
    // 工作流执行器
    executor *WorkflowExecutor
    // 任务队列（按优先级）
    taskQueues map[int]TaskQueue
    // 工作流实例状态
    instanceStates sync.Map
    // 工作流调度锁（防止同一工作流被并发调度）
    schedulingLocks sync.Map
    // 工作流执行指标
    executionMetrics *ExecutionMetrics
    // 系统资源监控器
    resourceMonitor *ResourceMonitor
    // 工作流拓扑统计
    topologyStats *TopologyStats
    // 调度器配置
    config SchedulerConfig
}

// 创建拓扑感知调度器
func NewTopologyAwareScheduler(
    topology *WorkflowTopology,
    tieredArch *TieredWorkflowArchitecture,
    executor *WorkflowExecutor,
    config SchedulerConfig,
) *TopologyAwareScheduler {
    // 创建优先级队列
    queues := make(map[int]TaskQueue)
    for priority := config.MinPriority; priority <= config.MaxPriority; priority += config.PriorityStep {
        queues[priority] = NewTaskQueue(config.QueueCapacity)
    }
    
    return &TopologyAwareScheduler{
        topology:          topology,
        tieredArchitecture: tieredArch,
        executor:          executor,
        taskQueues:        queues,
        executionMetrics:  NewExecutionMetrics(),
        resourceMonitor:   NewResourceMonitor(),
        topologyStats:     NewTopologyStats(topology),
        config:            config,
    }
}

// 提交工作流执行
func (s *TopologyAwareScheduler) SubmitWorkflow(
    ctx context.Context,
    workflowID string,
    input interface{},
    options SubmitOptions,
) (string, error) {
    // 验证工作流存在
    workflow, err := s.topology.GetWorkflow(workflowID)
    if err != nil {
        return "", fmt.Errorf("工作流不存在: %w", err)
    }
    
    // 创建工作流实例ID
    instanceID := uuid.New().String()
    
    // 计算调度优先级
    priority := calculatePriority(workflow, options)
    
    // 创建执行任务
    task := &WorkflowTask{
        InstanceID:  instanceID,
        WorkflowID:  workflowID,
        Input:       input,
        Priority:    priority,
        SubmitTime:  time.Now(),
        Options:     options,
        Status:      TaskStatusCreated,
    }
    
    // 获取工作流所在层次
    tier, _ := s.tieredArchitecture.GetWorkflowTier(workflowID)
    task.Tier = tier
    
    // 分析工作流依赖
    deps, err := s.analyzeDependencies(ctx, workflowID, instanceID, input)
    if err != nil {
        return instanceID, fmt.Errorf("依赖分析失败: %w", err)
    }
    task.Dependencies = deps
    
    // 存储工作流实例状态
    s.instanceStates.Store(instanceID, &WorkflowInstanceState{
        InstanceID:     instanceID,
        WorkflowID:     workflowID,
        Status:         InstanceStatusCreated,
        StartTime:      time.Now(),
        DependentCount: len(deps),
    })
    
    // 检查是否有未满足的依赖
    if len(deps) > 0 {
        // 存在依赖，注册依赖回调
        s.registerDependencyCallbacks(instanceID, deps)
        
        // 更新状态为等待依赖
        s.updateInstanceStatus(instanceID, InstanceStatusWaitingDependencies)
    } else {
        // 无依赖，直接放入调度队列
        err := s.enqueueTask(task)
        if err != nil {
            return instanceID, fmt.Errorf("入队失败: %w", err)
        }
    }
    
    return instanceID, nil
}

// 分析工作流依赖
func (s *TopologyAwareScheduler) analyzeDependencies(
    ctx context.Context,
    workflowID string,
    instanceID string,
    input interface{},
) ([]Dependency, error) {
    // 获取静态依赖（从拓扑结构）
    staticDeps := s.topology.GetWorkflowDependencies(workflowID)
    
    // 解析动态依赖（从输入参数）
    dynamicDeps, err := s.resolveDynamicDependencies(ctx, workflowID, input)
    if err != nil {
        return nil, err
    }
    
    // 合并依赖
    allDeps := append(staticDeps, dynamicDeps...)
    
    // 过滤已满足的依赖
    var activeDeps []Dependency
    for _, dep := range allDeps {
        if !s.isDependencySatisfied(dep) {
            activeDeps = append(activeDeps, dep)
        }
    }
    
    return activeDeps, nil
}

// 启动调度循环
func (s *TopologyAwareScheduler) Start(ctx context.Context) error {
    log.Info("启动拓扑感知调度器")
    
    // 启动资源监控
    s.resourceMonitor.Start(ctx)
    
    // 启动指标收集
    s.executionMetrics.Start(ctx)
    
    // 启动拓扑统计
    s.topologyStats.Start(ctx)
    
    // 启动调度器工作循环
    go s.schedulingLoop(ctx)
    
    // 启动依赖监控循环
    go s.dependencyMonitorLoop(ctx)
    
    // 启动工作流超时检查
    go s.timeoutMonitorLoop(ctx)
    
    return nil
}

// 调度循环
func (s *TopologyAwareScheduler) schedulingLoop(ctx context.Context) {
    ticker := time.NewTicker(s.config.SchedulingInterval)
    defer ticker.Stop()
    
    for {
        select {
        case <-ctx.Done():
            return
            
        case <-ticker.C:
            // 获取系统资源状态
            resources := s.resourceMonitor.GetResourceStatus()
            
            // 确定此轮可调度任务数量
            maxTasks := calculateSchedulableTaskCount(resources, s.config)
            
            if maxTasks <= 0 {
                continue
            }
            
            // 按优先级遍历队列
            scheduledCount := 0
            for priority := s.config.MaxPriority; priority >= s.config.MinPriority; priority -= s.config.PriorityStep {
                queue, exists := s.taskQueues[priority]
                if !exists || queue.IsEmpty() {
                    continue
                }
                
                // 从当前优先级队列批量获取任务
                tasks := queue.DequeueBatch(maxTasks - scheduledCount)
                if len(tasks) == 0 {
                    continue
                }
                
                // 应用拓扑感知调度算法
                schedulableTasks := s.applyTopologyAwareScheduling(tasks, resources)
                
                // 提交任务到执行器
                for _, task := range schedulableTasks {
                    if err := s.executeWorkflowTask(ctx, task); err != nil {
                        log.Error("执行工作流任务失败", 
                            "instanceID", task.InstanceID, 
                            "workflowID", task.WorkflowID, 
                            "error", err)
                            
                        // 重新入队或标记失败
                        s.handleExecutionFailure(task, err)
                    } else {
                        scheduledCount++
                    }
                }
                
                // 检查是否达到本轮调度上限
                if scheduledCount >= maxTasks {
                    break
                }
            }
            
            // 更新调度指标
            s.executionMetrics.RecordSchedulingRound(scheduledCount)
        }
    }
}

// 应用拓扑感知调度算法
func (s *TopologyAwareScheduler) applyTopologyAwareScheduling(
    tasks []*WorkflowTask,
    resources ResourceStatus,
) []*WorkflowTask {
    if len(tasks) == 0 {
        return tasks
    }
    
    // 获取拓扑统计信息
    stats := s.topologyStats.GetStats()
    
    // 1. 基于工作流关键路径排序
    sort.Slice(tasks, func(i, j int) bool {
        // 获取各自工作流的关键路径长度
        pathLengthI := stats.CriticalPathLengths[tasks[i].WorkflowID]
        pathLengthJ := stats.CriticalPathLengths[tasks[j].WorkflowID]
        
        // 关键路径更长的优先级更高
        if pathLengthI != pathLengthJ {
            return pathLengthI > pathLengthJ
        }
        
        // 关键路径相同时，按原始优先级排序
        return tasks[i].Priority > tasks[j].Priority
    })
    
    // 2. 考虑资源限制
    var schedulableTasks []*WorkflowTask
    remainingCPU := resources.AvailableCPU
    remainingMemory := resources.AvailableMemory
    
    // 获取工作流资源需求预估
    resourceEstimates := s.executionMetrics.GetResourceEstimates()
    
    for _, task := range tasks {
        // 获取工作流预估资源需求
        estimate, exists := resourceEstimates[task.WorkflowID]
        if !exists {
            // 使用默认估计
            estimate = ResourceEstimate{
                CPU:    0.1,
                Memory: 100 * 1024 * 1024, // 100MB
            }
        }
        
        // 检查资源是否足够
        if estimate.CPU <= remainingCPU && estimate.Memory <= remainingMemory {
            schedulableTasks = append(schedulableTasks, task)
            
            // 减少可用资源
            remainingCPU -= estimate.CPU
            remainingMemory -= estimate.Memory
        } else {
            // 资源不足，无法调度此任务
            // 将任务重新入队，等待下一轮调度
            if err := s.requeueTask(task); err != nil {
                log.Error("重新入队任务失败", 
                    "instanceID", task.InstanceID, 
                    "workflowID", task.WorkflowID, 
                    "error", err)
            }
        }
    }
    
    // 3. 应用拓扑优化规则
    
    // 3.1 检测同级工作流组并优化执行顺序
    schedulableTasks = s.optimizeSiblingWorkflows(schedulableTasks, stats)
    
    // 3.2 优化基于数据局部性
    schedulableTasks = s.optimizeDataLocality(schedulableTasks, stats)
    
    // 3.3 处理递归工作流特殊优化
    schedulableTasks = s.optimizeRecursiveWorkflows(schedulableTasks, stats)
    
    return schedulableTasks
}

// 优化同级工作流执行
func (s *TopologyAwareScheduler) optimizeSiblingWorkflows(
    tasks []*WorkflowTask,
    stats TopologyStatistics,
) []*WorkflowTask {
    // 按工作流组分组
    workflowGroups := make(map[string][]*WorkflowTask)
    
    // 找出相同父工作流的任务
    for _, task := range tasks {
        parentID := stats.ParentWorkflows[task.WorkflowID]
        if parentID != "" {
            groupID := fmt.Sprintf("parent:%s", parentID)
            workflowGroups[groupID] = append(workflowGroups[groupID], task)
        }
        
        // 查找同一场景的工作流
        sceneID := s.getWorkflowSceneID(task.WorkflowID)
        if sceneID != "" {
            groupID := fmt.Sprintf("scene:%s", sceneID)
            workflowGroups[groupID] = append(workflowGroups[groupID], task)
        }
    }
    
    // 优化每个工作流组内的执行顺序
    optimizedGroups := make(map[string][]*WorkflowTask)
    for groupID, groupTasks := range workflowGroups {
        if len(groupTasks) <= 1 {
            optimizedGroups[groupID] = groupTasks
            continue
        }
        
        // 分析组内工作流依赖关系
        dependencyGraph := s.buildGroupDependencyGraph(groupTasks)
        
        // 基于依赖图执行拓扑排序
        sorted := dependencyGraph.TopologicalSort()
        
        // 按拓扑排序重新组织任务
        sortedTasks := make([]*WorkflowTask, 0, len(groupTasks))
        for _, nodeID := range sorted {
            for _, task := range groupTasks {
                if task.WorkflowID == nodeID {
                    sortedTasks = append(sortedTasks, task)
                    break
                }
            }
        }
        
        optimizedGroups[groupID] = sortedTasks
    }
    
    // 保留所有任务但调整顺序
    result := make([]*WorkflowTask, 0, len(tasks))
    
    // 首先添加所有优化过的组
    addedTasks := make(map[string]bool)
    for _, groupTasks := range optimizedGroups {
        for _, task := range groupTasks {
            if !addedTasks[task.InstanceID] {
                result = append(result, task)
                addedTasks[task.InstanceID] = true
            }
        }
    }
    
    // 添加剩余的任务
    for _, task := range tasks {
        if !addedTasks[task.InstanceID] {
            result = append(result, task)
        }
    }
    
    return result
}

// 优化基于数据局部性
func (s *TopologyAwareScheduler) optimizeDataLocality(
    tasks []*WorkflowTask,
    stats TopologyStatistics,
) []*WorkflowTask {
    // 获取工作流数据访问模式
    dataAccessPatterns := s.executionMetrics.GetDataAccessPatterns()
    
    // 为任务计算数据亲和度得分
    affinityScores := make(map[string]float64)
    for _, task := range tasks {
        // 获取此工作流的数据访问模式
        pattern, exists := dataAccessPatterns[task.WorkflowID]
        if !exists {
            affinityScores[task.InstanceID] = 0.0
            continue
        }
        
        // 计算与最近执行工作流的数据重叠度
        recentWorkflows := s.executionMetrics.GetRecentlyExecutedWorkflows(10)
        maxOverlap := 0.0
        
        for _, recentWF := range recentWorkflows {
            if recentPattern, exists := dataAccessPatterns[recentWF]; exists {
                overlap := calculateDataOverlap(pattern, recentPattern)
                if overlap > maxOverlap {
                    maxOverlap = overlap
                }
            }
        }
        
        affinityScores[task.InstanceID] = maxOverlap
    }
    
    // 根据数据亲和度排序
    sort.Slice(tasks, func(i, j int) bool {
        // 数据亲和度高的优先执行
        scoreI := affinityScores[tasks[i].InstanceID]
        scoreJ := affinityScores[tasks[j].InstanceID]
        
        if math.Abs(scoreI-scoreJ) > 0.1 {
            return scoreI > scoreJ
        }
        
        // 亲和度接近时，保持原有顺序
        return i < j
    })
    
    return tasks
}

// 优化递归工作流
func (s *TopologyAwareScheduler) optimizeRecursiveWorkflows(
    tasks []*WorkflowTask,
    stats TopologyStatistics,
) []*WorkflowTask {
    // 识别递归工作流任务
    var recursiveTasks []*WorkflowTask
    var regularTasks []*WorkflowTask
    
    for _, task := range tasks {
        if stats.IsRecursive[task.WorkflowID] {
            recursiveTasks = append(recursiveTasks, task)
        } else {
            regularTasks = append(regularTasks, task)
        }
    }
    
    if len(recursiveTasks) == 0 {
        return tasks
    }
    
    // 分析系统当前负载
    systemLoad := s.resourceMonitor.GetSystemLoad()
    
    // 根据系统负载调整递归工作流的调度策略
    if systemLoad > 0.7 { // 系统负载高
        // 降低递归工作流的优先级，优先执行非递归任务
        return append(regularTasks, recursiveTasks...)
    } else {
        // 系统负载适中或较低，先处理一些递归任务
        // 但确保不会饿死常规任务
        
        // 根据递归深度信息调整顺序
        recursionDepths := s.executionMetrics.GetRecursionDepths()
        
        // 优先处理递归深度较浅的任务
        sort.Slice(recursiveTasks, func(i, j int) bool {
            depthI := recursionDepths[recursiveTasks[i].WorkflowID]
            depthJ := recursionDepths[recursiveTasks[j].WorkflowID]
            return depthI < depthJ
        })
        
        // 交错排列递归任务和常规任务
        result := make([]*WorkflowTask, 0, len(tasks))
        regularIdx := 0
        recursiveIdx := 0
        
        // 2:1的比例交错安排常规任务和递归任务
        for regularIdx < len(regularTasks) || recursiveIdx < len(recursiveTasks) {
            // 添加两个常规任务
            for i := 0; i < 2 && regularIdx < len(regularTasks); i++ {
                result = append(result, regularTasks[regularIdx])
                regularIdx++
            }
            
            // 添加一个递归任务
            if recursiveIdx < len(recursiveTasks) {
                result = append(result, recursiveTasks[recursiveIdx])
                recursiveIdx++
            }
        }
        
        return result
    }
}

// 执行工作流任务
func (s *TopologyAwareScheduler) executeWorkflowTask(ctx context.Context, task *WorkflowTask) error {
    // 更新任务状态
    task.Status = TaskStatusRunning
    task.StartTime = time.Now()
    
    // 更新实例状态
    s.updateInstanceStatus(task.InstanceID, InstanceStatusRunning)
    
    // 获取工作流定义
    workflowDef, err := s.topology.GetWorkflow(task.WorkflowID)
    if err != nil {
        return fmt.Errorf("获取工作流定义失败: %w", err)
    }
    
    // 根据工作流类型确定执行策略
    executionContext := &ExecutionContext{
        InstanceID:  task.InstanceID,
        WorkflowID:  task.WorkflowID,
        Input:       task.Input,
        StartTime:   task.StartTime,
        MaxDuration: task.Options.Timeout,
    }
    
    // 检查工作流是否为递归类型
    var executionResult *ExecutionResult
    if s.topologyStats.GetStats().IsRecursive[task.WorkflowID] {
        // 递归工作流特殊处理
        executionResult, err = s.executeRecursiveWorkflow(ctx, workflowDef, executionContext)
    } else {
        // 常规工作流执行
        executionResult, err = s.executor.ExecuteWorkflow(ctx, workflowDef, executionContext)
    }
    
    // 记录执行结束
    task.EndTime = time.Now()
    task.Duration = task.EndTime.Sub(task.StartTime)
    
    if err != nil {
        // 更新任务和实例状态为失败
        task.Status = TaskStatusFailed
        task.Error = err.Error()
        s.updateInstanceStatus(task.InstanceID, InstanceStatusFailed)
        
        // 记录指标
        s.executionMetrics.RecordFailedExecution(task.WorkflowID, task.Duration)
        
        return err
    }
    
    // 更新任务和实例状态为成功
    task.Status = TaskStatusCompleted
    task.Result = executionResult.Output
    s.updateInstanceStatus(task.InstanceID, InstanceStatusCompleted)
    
    // 记录执行指标
    s.executionMetrics.RecordSuccessfulExecution(
        task.WorkflowID, 
        task.Duration,
        executionResult.ResourceUsage,
    )
    
    // 触发依赖此工作流的任务
    s.notifyDependentWorkflows(task.InstanceID, executionResult.Output)
    
    return nil
}

// 执行递归工作流
func (s *TopologyAwareScheduler) executeRecursiveWorkflow(
    ctx context.Context,
    workflowDef *WorkflowDefinition,
    execContext *ExecutionContext,
) (*ExecutionResult, error) {
    // 获取当前递归深度
    recursionData, _ := s.instanceStates.Load(execContext.InstanceID)
    state := recursionData.(*WorkflowInstanceState)
    currentDepth := state.RecursionDepth
    
    // 获取递归工作流配置
    recursiveConfig, ok := workflowDef.Properties["recursive_config"].(RecursiveWorkflowConfig)
    if !ok {
        // 没有递归配置，作为普通工作流执行
        return s.executor.ExecuteWorkflow(ctx, workflowDef, execContext)
    }
    
    // 检查最大递归深度
    if currentDepth >= recursiveConfig.MaxDepth {
        return nil, fmt.Errorf("超过最大递归深度: %d", recursiveConfig.MaxDepth)
    }
    
    log.Info("执行递归工作流", 
        "workflowID", workflowDef.ID, 
        "instanceID", execContext.InstanceID,
        "depth", currentDepth)
    
    // 检查终止条件
    if recursiveConfig.TerminationCondition != nil {
        shouldTerminate, err := recursiveConfig.TerminationCondition.Evaluate(execContext.Input)
        if err != nil {
            return nil, fmt.Errorf("评估终止条件失败: %w", err)
        }
        
        if shouldTerminate {
            // 到达终止条件，直接执行基础逻辑
            return s.executor.ExecuteWorkflow(ctx, workflowDef, execContext)
        }
    }
    
    // 分解问题
    subproblems, err := recursiveConfig.Decomposer.Decompose(execContext.Input)
    if err != nil {
        return nil, fmt.Errorf("分解问题失败: %w", err)
    }
    
    if len(subproblems) == 0 {
        // 无法进一步分解，执行基础逻辑
        return s.executor.ExecuteWorkflow(ctx, workflowDef, execContext)
    }
    
    // 根据执行策略选择执行方式
    var subResults []interface{}
    
    switch recursiveConfig.ExecutionStrategy {
    case "depth_first":
        // 深度优先执行
        subResults, err = s.executeDepthFirst(ctx, workflowDef, execContext, subproblems, currentDepth)
    case "breadth_first":
        // 广度优先执行
        subResults, err = s.executeBreadthFirst(ctx, workflowDef, execContext, subproblems, currentDepth)
    case "adaptive":
        // 自适应执行策略
        systemLoad := s.resourceMonitor.GetSystemLoad()
        if systemLoad > 0.6 || currentDepth > 2 {
            // 系统负载高或递归深度较深时使用深度优先
            subResults, err = s.executeDepthFirst(ctx, workflowDef, execContext, subproblems, currentDepth)
        } else {
            // 否则使用广度优先
            subResults, err = s.executeBreadthFirst(ctx, workflowDef, execContext, subproblems, currentDepth)
        }
    default:
        return nil, fmt.Errorf("未知的递归执行策略: %s", recursiveConfig.ExecutionStrategy)
    }
    
    if err != nil {
        return nil, fmt.Errorf("执行子问题失败: %w", err)
    }
    
    // 合并子问题结果
    mergedResult, err := recursiveConfig.ResultMerger.Merge(subResults, execContext.Input)
    if err != nil {
        return nil, fmt.Errorf("合并结果失败: %w", err)
    }
    
    // 构建执行结果
    return &ExecutionResult{
        Output: mergedResult,
        ResourceUsage: ResourceUsage{
            CPUTimeSeconds: float64(time.Since(execContext.StartTime).Seconds()),
            MemoryBytes:    estimateMemoryUsage(subResults),
            IOOperations:   len(subproblems) * 2, // 估算值
        },
    }, nil
}
```

## 五、工作流编排与拓扑优化器

```go
// 工作流编排与拓扑优化器
type WorkflowOrchestratorOptimizer struct {
    // 工作流仓库
    repository WorkflowRepository
    // 执行引擎
    engine WorkflowEngine
    // 拓扑存储
    topologyStore TopologyStore
    // 拓扑感知调度器
    scheduler *TopologyAwareScheduler
    // 编排规则引擎
    orchestrationRules *OrchestrationRuleEngine
    // 优化器
    optimizer *TopologyOptimizer
    // 智能建议生成器
    advisor *WorkflowAdvisor
    // 配置
    config OrchestratorConfig
}

// 启动编排优化器
func (o *WorkflowOrchestratorOptimizer) Start(ctx context.Context) error {
    // 初始化拓扑
    if err := o.initializeTopology(ctx); err != nil {
        return err
    }
    
    // 启动组件
    if err := o.scheduler.Start(ctx); err != nil {
        return err
    }
    
    if err := o.optimizer.Start(ctx); err != nil {
        return err
    }
    
    // 启动编排规则引擎
    if err := o.orchestrationRules.Start(ctx); err != nil {
        return err
    }
    
    // 定期拓扑分析与优化
    go o.periodicOptimization(ctx)
    
    // 监听工作流变更
    go o.monitorWorkflowChanges(ctx)
    
    return nil
}

// 定期执行拓扑优化
func (o *WorkflowOrchestratorOptimizer) periodicOptimization(ctx context.Context) {
    ticker := time.NewTicker(o.config.OptimizationInterval)
    defer ticker.Stop()
    
    for {
        select {
        case <-ctx.Done():
            return
        case <-ticker.C:
            // 分析工作流拓扑
            topologyStats, err := o.analyzeTopology(ctx)
            if err != nil {
                log.Error("拓扑分析失败", "error", err)
                continue
            }
            
            // 识别优化机会
            opportunities, err := o.identifyOptimizationOpportunities(ctx, topologyStats)
            if err != nil {
                log.Error("识别优化机会失败", "error", err)
                continue
            }
            
            if len(opportunities) == 0 {
                log.Info("未发现优化机会")
                continue
            }
            
            log.Info("发现优化机会", "count", len(opportunities))
            
            // 生成优化建议
            suggestions, err := o.generateOptimizationSuggestions(ctx, opportunities)
            if err != nil {
                log.Error("生成优化建议失败", "error", err)
                continue
            }
            
            // 应用高置信度的自动优化
            if o.config.EnableAutoOptimization {
                appliedCount, err := o.applyAutoOptimizations(ctx, suggestions)
                if err != nil {
                    log.Error("应用自动优化失败", "error", err)
                } else if appliedCount > 0 {
                    log.Info("应用了自动优化", "count", appliedCount)
                }
            }
            
            // 存储建议以供用户审查
            if err := o.storeOptimizationSuggestions(ctx, suggestions); err != nil {
                log.Error("存储优化建议失败", "error", err)
            }
        }
    }
}

// 分析工作流拓扑
func (o *WorkflowOrchestratorOptimizer) analyzeTopology(ctx context.Context) (*TopologyStatistics, error) {
    // 获取最新拓扑
    topology, err := o.topologyStore.GetCurrentTopology(ctx)
    if err != nil {
        return nil, fmt.Errorf("获取拓扑失败: %w", err)
    }
    
    // 计算拓扑统计数据
    stats := &TopologyStatistics{
        NodeCount:           topology.CountNodes(),
        EdgeCount:           topology.CountEdges(),
        AverageOutDegree:    topology.CalculateAverageOutDegree(),
        MaxOutDegree:        topology.CalculateMaxOutDegree(),
        CriticalPathLengths: topology.CalculateCriticalPaths(),
        ConnectedComponents: topology.CountConnectedComponents(),
        CycleCount:          topology.CountCycles(),
        DependencyDepths:    topology.CalculateDependencyDepths(),
        FrequentPatterns:    o.detectFrequentPatterns(topology),
        HotspotWorkflows:    o.identifyHotspots(topology),
        ExecutionFrequency:  o.getWorkflowExecutionFrequency(),
        AverageExecutionTimes: o.getAverageExecutionTimes(),
        DataDependencies:    topology.AnalyzeDataDependencies(),
        RecursiveWorkflows:  o.identifyRecursiveWorkflows(topology),
    }
    
    // 更新拓扑统计存储
    if err := o.topologyStore.UpdateStatistics(ctx, stats); err != nil {
        log.Error("更新拓扑统计失败", "error", err)
    }
    
    return stats, nil
}

// 识别优化机会
func (o *WorkflowOrchestratorOptimizer) identifyOptimizationOpportunities(
    ctx context.Context,
    stats *TopologyStatistics,
) ([]OptimizationOpportunity, error) {
    var opportunities []OptimizationOpportunity
    
    // 1. 寻找可合并的工作流
    mergeOps, err := o.findMergeCandidates(ctx, stats)
    if err != nil {
        return nil, err
    }
    opportunities = append(opportunities, mergeOps...)
    
    // 2. 寻找可并行化的工作流
    parallelOps, err := o.findParallelizationOpportunities(ctx, stats)
    if err != nil {
        return nil, err
    }
    opportunities = append(opportunities, parallelOps...)
    
    // 3. 寻找需要拆分的工作流
    splitOps, err := o.findSplitCandidates(ctx, stats)
    if err != nil {
        return nil, err
    }
    opportunities = append(opportunities, splitOps...)
    
    // 4. 寻找可提升效率的链式工作流
    chainOps, err := o.findChainOptimizations(ctx, stats)
    if err != nil {
        return nil, err
    }
    opportunities = append(opportunities, chainOps...)
    
    // 5. 寻找递归工作流优化机会
    recursiveOps, err := o.findRecursiveOptimizations(ctx, stats)
    if err != nil {
        return nil, err
    }
    opportunities = append(opportunities, recursiveOps...)
    
    // 计算优化收益并排序
    for i := range opportunities {
        opportunities[i].EstimatedGain = o.calculateOptimizationGain(&opportunities[i], stats)
    }
    
    // 按预期收益排序
    sort.Slice(opportunities, func(i, j int) bool {
        return opportunities[i].EstimatedGain > opportunities[j].EstimatedGain
    })
    
    return opportunities, nil
}

// 寻找可合并的工作流
func (o *WorkflowOrchestratorOptimizer) findMergeCandidates(
    ctx context.Context,
    stats *TopologyStatistics,
) ([]OptimizationOpportunity, error) {
    var opportunities []OptimizationOpportunity
    
    // 获取最新拓扑
    topology, err := o.topologyStore.GetCurrentTopology(ctx)
    if err != nil {
        return nil, err
    }
    
    // 寻找顺序执行的工作流组
    sequentialGroups := topology.FindSequentialWorkflowChains(3) // 至少3个连续工作流
    
    for _, group := range sequentialGroups {
        // 检查这些工作流是否适合合并
        if o.areMergeCompatible(group) {
            // 计算合并后资源需求估计
            mergedResourceEst := o.estimateMergedResourceNeeds(group)
            
            // 确保合并后资源需求不会过高
            if mergedResourceEst.Memory <= o.config.MaxMergedMemory &&
               mergedResourceEst.CPU <= o.config.MaxMergedCPU {
                
                opportunity := OptimizationOpportunity{
                    ID:                uuid.New().String(),
                    Type:              OpportunityTypeMerge,
                    AffectedWorkflows: group,
                    Description:       fmt.Sprintf("合并 %d 个顺序执行的工作流以减少调度开销", len(group)),
                    Justification:     "这些工作流总是按固定顺序执行，且数据传递简单",
                    ResourceEstimates: mergedResourceEst,
                    ComplexityScore:   calculateMergeComplexity(group),
                }
                
                opportunities = append(opportunities, opportunity)
            }
        }
    }
    
    // 寻找频繁共同执行的工作流
    frequentlyCoexecuted := o.findFrequentlyCoexecutedWorkflows(stats.ExecutionFrequency)
    
    for _, group := range frequentlyCoexecuted {
        // 跳过已经在顺序组中的工作流
        if o.isGroupOverlapping(group, sequentialGroups) {
            continue
        }
        
        // 检查这些工作流是否适合合并
        if o.areMergeCompatible(group) {
            mergedResourceEst := o.estimateMergedResourceNeeds(group)
            
            if mergedResourceEst.Memory <= o.config.MaxMergedMemory &&
               mergedResourceEst.CPU <= o.config.MaxMergedCPU {
                
                opportunity := OptimizationOpportunity{
                    ID:                uuid.New().String(),
                    Type:              OpportunityTypeMerge,
                    AffectedWorkflows: group,
                    Description:       fmt.Sprintf("合并 %d 个频繁共同执行的工作流", len(group)),
                    Justification:     "这些工作流经常同时执行，合并可减少启动开销",
                    ResourceEstimates: mergedResourceEst,
                    ComplexityScore:   calculateMergeComplexity(group),
                }
                
                opportunities = append(opportunities, opportunity)
            }
        }
    }
    
    return opportunities, nil
}

// 生成优化建议
func (o *WorkflowOrchestratorOptimizer) generateOptimizationSuggestions(
    ctx context.Context, 
    opportunities []OptimizationOpportunity,
) ([]OptimizationSuggestion, error) {
    var suggestions []OptimizationSuggestion
    
    for _, opportunity := range opportunities {
        switch opportunity.Type {
        case OpportunityTypeMerge:
            suggestion, err := o.generateMergeSuggestion(ctx, opportunity)
            if err != nil {
                log.Error("生成合并建议失败", "opportunityID", opportunity.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
            
        case OpportunityTypeParallelize:
            suggestion, err := o.generateParallelizeSuggestion(ctx, opportunity)
            if err != nil {
                log.Error("生成并行化建议失败", "opportunityID", opportunity.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
            
        case OpportunityTypeSplit:
            suggestion, err := o.generateSplitSuggestion(ctx, opportunity)
            if err != nil {
                log.Error("生成拆分建议失败", "opportunityID", opportunity.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
            
        case OpportunityTypeChainOptimize:
            suggestion, err := o.generateChainOptimizeSuggestion(ctx, opportunity)
            if err != nil {
                log.Error("生成链优化建议失败", "opportunityID", opportunity.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
            
        case OpportunityTypeRecursiveOptimize:
            suggestion, err := o.generateRecursiveOptimizeSuggestion(ctx, opportunity)
            if err != nil {
                log.Error("生成递归优化建议失败", "opportunityID", opportunity.ID, "error", err)
                continue
            }
            suggestions = append(suggestions, suggestion)
        }
    }
    
    // 计算建议的置信度
    for i := range suggestions {
        suggestions[i].ConfidenceScore = o.calculateSuggestionConfidence(&suggestions[i])
    }
    
    // 按置信度排序
    sort.Slice(suggestions, func(i, j int) bool {
        return suggestions[i].ConfidenceScore > suggestions[j].ConfidenceScore
    })
    
    return suggestions, nil
}

// 生成工作流合并建议
func (o *WorkflowOrchestratorOptimizer) generateMergeSuggestion(
    ctx context.Context,
    opportunity OptimizationOpportunity,
) (OptimizationSuggestion, error) {
    // 获取要合并的工作流定义
    workflows := make([]*WorkflowDefinition, 0, len(opportunity.AffectedWorkflows))
    for _, id := range opportunity.AffectedWorkflows {
        wf, err := o.repository.GetWorkflowByID(ctx, id)
        if err != nil {
            return OptimizationSuggestion{}, err
        }
        workflows = append(workflows, wf)
    }
    
    // 生成合并后的工作流定义
    mergedWorkflow, err := o.workflowMerger.MergeWorkflows(workflows)
    if err != nil {
        return OptimizationSuggestion{}, err
    }
    
    // 生成代码变更
    codeChanges, err := o.generateMergeCodeChanges(workflows, mergedWorkflow)
    if err != nil {
        return OptimizationSuggestion{}, err
    }
    
    // 生成测试案例
    testCases, err := o.generateTestCasesForMergedWorkflow(workflows, mergedWorkflow)
    if err != nil {
        return OptimizationSuggestion{}, err
    }
    
    // 生成回滚计划
    rollbackPlan := o.generateRollbackPlan(workflows, mergedWorkflow)
    
    return OptimizationSuggestion{
        ID:                uuid.New().String(),
        OpportunityID:     opportunity.ID,
        Type:              SuggestionTypeMerge,
        Description:       opportunity.Description,
        Justification:     opportunity.Justification,
        AffectedWorkflows: opportunity.AffectedWorkflows,
        EstimatedGain:     opportunity.EstimatedGain,
        ProposedChanges: ProposedChanges{
            NewWorkflows:     []*WorkflowDefinition{mergedWorkflow},
            DeleteWorkflows:  opportunity.AffectedWorkflows,
            CodeChanges:      codeChanges,
            TestCases:        testCases,
            RollbackPlan:     rollbackPlan,
        },
        Risk:              o.assessMergeRisk(workflows),
        ImplementationComplexity: opportunity.ComplexityScore,
        Status:            SuggestionStatusPending,
        CreatedAt:         time.Now(),
    }, nil
}

// 应用自动优化
func (o *WorkflowOrchestratorOptimizer) applyAutoOptimizations(
    ctx context.Context,
    suggestions []OptimizationSuggestion,
) (int, error) {
    var appliedCount int
    
    for _, suggestion := range suggestions {
        // 只应用高置信度的建议
        if suggestion.ConfidenceScore < o.config.AutoOptimizeThreshold {
            continue
        }
        
        // 避免高风险操作的自动优化
        if suggestion.Risk > RiskLevelMedium {
            continue
        }
        
        // 避免高复杂度的自动优化
        if suggestion.ImplementationComplexity > 0.7 {
            continue
        }
        
        log.Info("尝试自动应用优化建议", 
            "suggestionID", suggestion.ID, 
            "type", suggestion.Type, 
            "confidence", suggestion.ConfidenceScore)
        
        // 应用优化
        err := o.applyOptimizationSuggestion(ctx, suggestion)
        if err != nil {
            log.Error("应用优化建议失败", 
                "suggestionID", suggestion.ID, 
                "error", err)
            continue
        }
        
        // 更新建议状态
        suggestion.Status = SuggestionStatusApplied
        suggestion.AppliedAt = time.Now()
        
        if err := o.storeOptimizationSuggestion(ctx, suggestion); err != nil {
            log.Error("更新优化建议状态失败", 
                "suggestionID", suggestion.ID, 
                "error", err)
        }
        
        appliedCount++
        
        // 添加部署记录
        o.recordOptimizationDeployment(ctx, suggestion)
    }
    
    return appliedCount, nil
}

// 工作流状态监控和拓扑更新
func (o *WorkflowOrchestratorOptimizer) monitorWorkflowChanges(ctx context.Context) {
    changesChan := o.repository.SubscribeToChanges(ctx)
    
    for {
        select {
        case <-ctx.Done():
            return
            
        case change := <-changesChan:
            log.Info("检测到工作流变更", "changeType", change.Type, "workflowID", change.WorkflowID)
            
            // 更新拓扑
            if err := o.updateTopology(ctx, change); err != nil {
                log.Error("更新拓扑失败", "error", err)
            }
            
            // 根据变更类型处理
            switch change.Type {
            case ChangeTypeAdd, ChangeTypeUpdate:
                // 分析新工作流是否适合现有拓扑
                if err := o.analyzeNewWorkflowFit(ctx, change.WorkflowID); err != nil {
                    log.Error("分析新工作流适应性失败", "error", err)
                }
                
            case ChangeTypeDelete:
                // 检查删除的影响
                if err := o.analyzeDeletionImpact(ctx, change.WorkflowID); err != nil {
                    log.Error("分析删除影响失败", "error", err)
                }
                
            case ChangeTypeExecute:
                // 更新执行统计
                if err := o.updateExecutionStats(ctx, change.WorkflowID); err != nil {
                    log.Error("更新执行统计失败", "error", err)
                }
            }
        }
    }
}
```

## 六、总结与设计原则

工作流拓扑结构和调度机制的设计是智能家居系统架构中的核心考量，
通过本次讨论，我们可以总结出以下关键设计原则：

### 1. 工作流拓扑结构设计原则

1. **结构分层**
   - 通过分层设计（应用层、领域层、基础设施层、自治层）明确责任边界
   - 使用严格的层间依赖规则避免循环依赖
   - 为不同层次提供独立的调度策略和资源控制

2. **拓扑模型明确**
   - 显式定义工作流关系类型（父子、依赖、协作、触发、版本）
   - 支持多种执行模型（深度优先、广度优先、优先级优先、事件驱动）
   - 使用拓扑统计和分析指导调度决策

3. **递归结构支持**
   - 为复杂问题的分解与组合提供递归工作流结构
   - 支持多种递归执行策略以适应不同场景
   - 实现递归深度控制和终止机制防止无限递归

### 2. 工作流调度机制设计原则

1. **拓扑感知调度**
   - 调度决策考虑工作流在拓扑中的位置和关系
   - 优先执行关键路径上的工作流
   - 基于工作流组和局部性优化调度顺序

2. **资源感知与自适应**
   - 根据系统负载动态调整调度策略
   - 为不同工作流层次分配合理资源配额
   - 支持工作窃取等机制提高资源利用率

3. **支持多元执行模式**
   - 为递归工作流提供特殊调度考量
   - 支持批处理、链式优化等高级执行模式
   - 允许多种并发控制机制共存

### 3. 优化与编排策略

1. **持续拓扑优化**
   - 自动识别优化机会并生成建议
   - 安全应用高置信度优化
   - 提供细粒度的优化控制和回滚机制

2. **数据驱动决策**
   - 收集执行统计和资源使用模式
   - 基于真实世界执行数据优化拓扑
   - 使用预测模型提前调整资源分配

3. **平衡灵活性与确定性**
   - 提供严格的编排规则保证关键业务流程的可靠性
   - 同时允许自适应行为以应对变化的环境
   - 平衡自动化与人工干预

这种综合考虑工作流拓扑结构和调度机制的设计适合智能家居系统中复杂的自动化场景，
能够有效处理多变的用户需求和设备环境，同时保持系统的可靠性和响应性。

## 工作流架构与智能家居系统的适配性分析

确实，智能家居系统的独特特点使得工作流架构成为其最佳选择。
这里我将分析为什么工作流架构特别适合智能家居系统，以及其他架构模式在此场景下面临的挑战。

### 智能家居系统的独特特点

智能家居系统具有几个关键特性，使其区别于传统软件系统：

1. **事件驱动与场景多变**：用户行为、环境变化、设备状态转换等都能触发系统行为
2. **分布式执行环境**：从云端到边缘再到各类设备的多层次执行
3. **状态持久性与长时间运行**：需要维护和恢复复杂的系统状态
4. **高度异构性**：集成多种不同制造商、不同协议的设备
5. **自适应与自学习需求**：系统需要学习用户偏好并适应变化

### 工作流架构的独特优势

工作流架构能够很好地解决上述挑战：

1. **拓扑结构映射现实场景**：工作流的有向图结构天然映射了智能家居场景间的逻辑关系和执行流程
2. **状态管理内置**：工作流引擎通常内置状态管理和恢复机制
3. **多层次调度**：从我们讨论的拓扑感知调度可以看出，工作流架构支持多种精细化调度策略
4. **递归组合能力**：工作流的递归特性能够处理复杂场景的分解和重组
5. **动态适应能力**：工作流定义可以动态变更，支持系统演进

## 其他架构模式的局限性

### 微服务架构

尽管微服务架构具有模块化和可扩展性优势，但在智能家居场景下面临：

1. **长流程协调困难**：微服务间主要通过API调用通信，缺乏内置的长流程协调机制
2. **状态管理复杂**：每个微服务管理自身状态，跨服务状态一致性难以保证
3. **边缘场景支持有限**：传统微服务通常假设网络连接稳定，不适合边缘计算场景

### 事件驱动架构

虽然事件驱动架构适合处理异步事件，但仍有局限：

1. **缺乏流程编排**：纯事件驱动架构难以表达复杂的条件逻辑和顺序依赖
2. **拓扑关系不明确**：事件发布订阅模式使系统拓扑关系难以可视化和管理
3. **调试与追踪困难**：事件链在分布式环境下难以追踪和重现

### 响应式架构

响应式架构强调响应性和弹性，但不足之处在于：

1. **流程控制复杂**：数据流范式下复杂控制流表达不自然
2. **与硬件系统集成挑战**：传统硬件设备往往不遵循响应式编程模型
3. **状态跟踪困难**：在纯响应式系统中维护和恢复全局状态较为复杂

### 分层架构

传统分层架构太过刚性：

1. **难以表达动态关系**：层间关系固定，难以表达智能家居中的动态协作关系
2. **自适应性有限**：难以根据运行时条件调整组件间通信方式
3. **缺乏编排能力**：不具备内置的流程编排和协调能力

## 工作流架构的成功因素

工作流架构成功应用于智能家居有几个关键因素：

1. **统一的编排语言**：提供描述从简单到复杂场景的通用语言
2. **分离关注点**：将业务逻辑、执行环境和调度策略分离
3. **可视化与易理解**：工作流可以直观地可视化，便于理解和设计
4. **适应性强**：可以从简单规则到复杂AI驱动的决策流程无缝过渡
5. **拓扑感知**：能够通过拓扑分析优化系统性能和资源使用

## 构建成功的智能家居工作流系统关键点

根据我们的讨论，构建成功的智能家居工作流系统应关注：

1. **多层次工作流设计**：从应用层到自治层的清晰分层
2. **拓扑感知调度机制**：基于工作流关系和系统状态的智能调度
3. **递归工作流支持**：处理复杂场景的分解与合成
4. **边缘云协同执行**：流畅处理从设备到云端的跨域执行
5. **持续优化与自适应**：通过运行时数据持续优化工作流拓扑

总结来说，工作流架构不仅能够适应智能家居系统的复杂性，
还能够随着系统规模和复杂度的增长而保持稳定性和可维护性。
其他架构模式虽然在特定方面有优势，但难以全面应对智能家居领域的多维度挑战。
工作流架构提供了描述、执行和管理复杂自动化场景的统一范式，这正是智能家居系统所需要的。
