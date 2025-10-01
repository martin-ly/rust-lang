//! 递归异步分析和示例模型
//! 
//! 本模块实现了递归异步编程的分析和建模，包括：
//! - 异步递归模式分析
//! - 栈安全递归实现
//! - 尾递归优化
//! - 异步递归性能分析
//! - 递归深度控制
//! - 内存使用优化
//! 
//! 充分利用 Rust 1.90 的异步特性和栈安全保证

use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};
use std::pin::Pin;
use std::future::Future;
use serde::{Deserialize, Serialize};
use crate::error::ModelError;

#[cfg(feature = "tokio-adapter")]
use tokio::time::timeout;
#[cfg(feature = "tokio-adapter")]
use tokio::sync::Semaphore;

/// 递归异步结果类型
pub type RecursiveAsyncResult<T> = Result<T, ModelError>;

/// 递归类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RecursionType {
    /// 直接递归
    DirectRecursion,
    /// 间接递归
    IndirectRecursion,
    /// 尾递归
    TailRecursion,
    /// 相互递归
    MutualRecursion,
    /// 嵌套递归
    NestedRecursion,
    /// 树递归
    TreeRecursion,
}

/// 递归策略
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RecursionStrategy {
    /// 栈递归（传统）
    StackRecursion,
    /// 堆递归（异步安全）
    HeapRecursion,
    /// 迭代转换
    IterativeConversion,
    /// 蹦床技术
    Trampoline,
    /// 延续传递风格
    ContinuationPassing,
    /// 协程递归
    CoroutineRecursion,
}

/// 递归控制配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RecursionConfig {
    /// 最大递归深度
    pub max_depth: usize,
    /// 栈大小限制
    pub stack_size_limit: usize,
    /// 超时设置
    pub timeout: Option<Duration>,
    /// 内存限制
    pub memory_limit: Option<usize>,
    /// 并发递归限制
    pub concurrent_recursion_limit: usize,
    /// 递归策略
    pub strategy: RecursionStrategy,
    /// 是否启用尾递归优化
    pub tail_call_optimization: bool,
}

impl Default for RecursionConfig {
    fn default() -> Self {
        Self {
            max_depth: 1000,
            stack_size_limit: 8 * 1024 * 1024, // 8MB
            timeout: Some(Duration::from_secs(30)),
            memory_limit: Some(100 * 1024 * 1024), // 100MB
            concurrent_recursion_limit: 10,
            strategy: RecursionStrategy::HeapRecursion,
            tail_call_optimization: true,
        }
    }
}

/// 递归统计信息
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct RecursionMetrics {
    /// 总递归调用次数
    pub total_calls: u64,
    /// 最大递归深度
    pub max_depth_reached: usize,
    /// 平均递归深度
    pub average_depth: f64,
    /// 总执行时间
    pub total_execution_time: Duration,
    /// 平均执行时间
    pub average_execution_time: Duration,
    /// 内存峰值使用
    pub peak_memory_usage: usize,
    /// 栈溢出次数
    pub stack_overflow_count: u64,
    /// 超时次数
    pub timeout_count: u64,
    /// 成功完成次数
    pub success_count: u64,
    /// 失败次数
    pub failure_count: u64,
}

impl RecursionMetrics {
    pub fn update_call(&mut self, depth: usize, execution_time: Duration, memory_usage: usize) {
        self.total_calls += 1;
        self.max_depth_reached = self.max_depth_reached.max(depth);
        
        // 更新平均深度
        let total_depth = self.average_depth * (self.total_calls - 1) as f64 + depth as f64;
        self.average_depth = total_depth / self.total_calls as f64;
        
        // 更新执行时间
        self.total_execution_time += execution_time;
        self.average_execution_time = Duration::from_nanos(
            (self.total_execution_time.as_nanos() / self.total_calls as u128) as u64
        );
        
        // 更新内存使用
        self.peak_memory_usage = self.peak_memory_usage.max(memory_usage);
    }
    
    pub fn record_success(&mut self) {
        self.success_count += 1;
    }
    
    pub fn record_failure(&mut self) {
        self.failure_count += 1;
    }
    
    pub fn record_stack_overflow(&mut self) {
        self.stack_overflow_count += 1;
        self.record_failure();
    }
    
    pub fn record_timeout(&mut self) {
        self.timeout_count += 1;
        self.record_failure();
    }
    
    pub fn success_rate(&self) -> f64 {
        if self.total_calls > 0 {
            self.success_count as f64 / self.total_calls as f64
        } else {
            0.0
        }
    }
}

/// 递归上下文
#[derive(Debug, Clone)]
pub struct RecursionContext {
    /// 当前递归深度
    pub current_depth: usize,
    /// 递归路径
    pub call_stack: Vec<String>,
    /// 开始时间
    pub start_time: Instant,
    /// 内存使用跟踪
    pub memory_usage: usize,
    /// 递归ID
    pub recursion_id: String,
    /// 父递归ID
    pub parent_id: Option<String>,
}

impl RecursionContext {
    pub fn new(recursion_id: String) -> Self {
        Self {
            current_depth: 0,
            call_stack: Vec::new(),
            start_time: Instant::now(),
            memory_usage: 0,
            recursion_id,
            parent_id: None,
        }
    }
    
    pub fn push_call(&mut self, function_name: String) {
        self.current_depth += 1;
        self.call_stack.push(function_name);
    }
    
    pub fn pop_call(&mut self) {
        if self.current_depth > 0 {
            self.current_depth -= 1;
            self.call_stack.pop();
        }
    }
    
    pub fn elapsed_time(&self) -> Duration {
        self.start_time.elapsed()
    }
    
    pub fn create_child_context(&self, child_id: String) -> Self {
        Self {
            current_depth: self.current_depth,
            call_stack: self.call_stack.clone(),
            start_time: self.start_time,
            memory_usage: self.memory_usage,
            recursion_id: child_id,
            parent_id: Some(self.recursion_id.clone()),
        }
    }
}

/// 异步递归执行器
#[derive(Debug)]
pub struct AsyncRecursionExecutor {
    config: RecursionConfig,
    metrics: Arc<RwLock<RecursionMetrics>>,
    active_recursions: Arc<RwLock<HashMap<String, RecursionContext>>>,
    #[cfg(feature = "tokio-adapter")]
    semaphore: Arc<Semaphore>,
}

impl AsyncRecursionExecutor {
    pub fn new(config: RecursionConfig) -> Self {
        Self {
            #[cfg(feature = "tokio-adapter")]
            semaphore: Arc::new(Semaphore::new(config.concurrent_recursion_limit)),
            config,
            metrics: Arc::new(RwLock::new(RecursionMetrics::default())),
            active_recursions: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 执行异步递归函数
    pub async fn execute_recursive<F, Fut, T>(
        &self,
        function_name: String,
        recursive_fn: F,
        initial_input: T,
    ) -> RecursiveAsyncResult<T>
    where
        F: Fn(T, RecursionContext, Arc<AsyncRecursionExecutor>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = RecursiveAsyncResult<T>> + Send + 'static,
        T: Send + 'static,
    {
        let recursion_id = uuid::Uuid::new_v4().to_string();
        let mut context = RecursionContext::new(recursion_id.clone());
        context.push_call(function_name);
        
        // 获取执行许可
        #[cfg(feature = "tokio-adapter")]
        let _permit = self.semaphore.acquire().await.map_err(|e| {
            ModelError::AsyncError(format!("Failed to acquire recursion permit: {}", e))
        })?;
        
        // 注册活跃递归
        self.active_recursions.write().unwrap().insert(recursion_id.clone(), context.clone());
        
        // 执行递归函数
        let start_time = Instant::now();
        let result = if let Some(timeout_duration) = self.config.timeout {
            #[cfg(feature = "tokio-adapter")]
            {
                timeout(timeout_duration, recursive_fn(initial_input, context.clone(), Arc::new(self.clone()))).await
                    .map_err(|_| ModelError::TimeoutError("Recursion timeout".to_string()))?
            }
            #[cfg(not(feature = "tokio-adapter"))]
            {
                recursive_fn(initial_input, context.clone(), Arc::new(self.clone())).await
            }
        } else {
            recursive_fn(initial_input, context.clone(), Arc::new(self.clone())).await
        };
        
        let execution_time = start_time.elapsed();
        
        // 更新统计信息
        {
            let mut metrics = self.metrics.write().unwrap();
            metrics.update_call(context.current_depth, execution_time, context.memory_usage);
            match &result {
                Ok(_) => metrics.record_success(),
                Err(ModelError::StackOverflowError(_)) => metrics.record_stack_overflow(),
                Err(ModelError::TimeoutError(_)) => metrics.record_timeout(),
                Err(_) => metrics.record_failure(),
            }
        }
        
        // 清理活跃递归
        self.active_recursions.write().unwrap().remove(&recursion_id);
        
        result
    }
    
    /// 检查递归深度限制
    pub fn check_depth_limit(&self, context: &RecursionContext) -> RecursiveAsyncResult<()> {
        if context.current_depth >= self.config.max_depth {
            return Err(ModelError::StackOverflowError(format!(
                "Maximum recursion depth {} exceeded", 
                self.config.max_depth
            )));
        }
        Ok(())
    }
    
    /// 检查超时
    pub fn check_timeout(&self, context: &RecursionContext) -> RecursiveAsyncResult<()> {
        if let Some(timeout_duration) = self.config.timeout {
            if context.elapsed_time() >= timeout_duration {
                return Err(ModelError::TimeoutError("Recursion timeout".to_string()));
            }
        }
        Ok(())
    }
    
    /// 获取统计信息
    pub fn metrics(&self) -> RecursionMetrics {
        self.metrics.read().unwrap().clone()
    }
    
    /// 获取活跃递归数量
    pub fn active_recursion_count(&self) -> usize {
        self.active_recursions.read().unwrap().len()
    }
    
    /// 获取配置
    pub fn config(&self) -> &RecursionConfig {
        &self.config
    }
}

impl Clone for AsyncRecursionExecutor {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            metrics: Arc::clone(&self.metrics),
            active_recursions: Arc::clone(&self.active_recursions),
            #[cfg(feature = "tokio-adapter")]
            semaphore: Arc::clone(&self.semaphore),
        }
    }
}

/// 尾递归优化器
#[derive(Debug)]
pub struct TailRecursionOptimizer;

impl TailRecursionOptimizer {
    /// 将递归函数转换为迭代形式
    pub async fn optimize_tail_recursion<T, F>(
        initial_value: T,
        mut condition: impl FnMut(&T) -> bool + Send,
        mut transform: F,
    ) -> RecursiveAsyncResult<T>
    where
        T: Send + 'static,
        F: FnMut(T) -> Pin<Box<dyn Future<Output = RecursiveAsyncResult<T>> + Send>> + Send,
    {
        let mut current = initial_value;
        
        while condition(&current) {
            current = transform(current).await?;
            
            // 让出控制权，防止阻塞
            #[cfg(feature = "tokio-adapter")]
            tokio::task::yield_now().await;
        }
        
        Ok(current)
    }
    
    /// 使用蹦床技术优化递归
    pub async fn trampoline_optimization<T>(
        initial_computation: TrampolineComputation<T>,
    ) -> RecursiveAsyncResult<T>
    where
        T: Send + 'static,
    {
        let mut computation = initial_computation;
        
        loop {
            match computation {
                TrampolineComputation::Done(value) => return Ok(value),
                TrampolineComputation::Call(future) => {
                    computation = future.await?;
                }
                TrampolineComputation::Error(error) => return Err(error),
            }
            
            // 让出控制权
            #[cfg(feature = "tokio-adapter")]
            tokio::task::yield_now().await;
        }
    }
}

/// 蹦床计算类型
pub enum TrampolineComputation<T> {
    Done(T),
    Call(Pin<Box<dyn Future<Output = RecursiveAsyncResult<TrampolineComputation<T>>> + Send>>),
    Error(ModelError),
}

impl<T: std::fmt::Debug> std::fmt::Debug for TrampolineComputation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TrampolineComputation::Done(t) => f.debug_tuple("Done").field(t).finish(),
            TrampolineComputation::Call(_) => f.debug_tuple("Call").field(&"<future>").finish(),
            TrampolineComputation::Error(e) => f.debug_tuple("Error").field(e).finish(),
        }
    }
}

/// 递归模式分析器
#[derive(Debug)]
pub struct RecursionPatternAnalyzer {
    patterns: HashMap<String, RecursionPattern>,
    call_graph: HashMap<String, Vec<String>>,
}

impl RecursionPatternAnalyzer {
    pub fn new() -> Self {
        Self {
            patterns: HashMap::new(),
            call_graph: HashMap::new(),
        }
    }
    
    /// 分析递归模式
    pub fn analyze_pattern(&mut self, function_name: String, calls: Vec<String>) -> RecursionPattern {
        self.call_graph.insert(function_name.clone(), calls.clone());
        
        let pattern = if calls.contains(&function_name) {
            if calls.len() == 1 && calls[0] == function_name {
                RecursionPattern {
                    recursion_type: RecursionType::DirectRecursion,
                    is_tail_recursive: self.is_tail_recursive(&function_name, &calls),
                    complexity: self.estimate_complexity(&calls),
                    optimization_potential: self.assess_optimization_potential(&calls),
                }
            } else {
                RecursionPattern {
                    recursion_type: RecursionType::IndirectRecursion,
                    is_tail_recursive: false,
                    complexity: self.estimate_complexity(&calls),
                    optimization_potential: self.assess_optimization_potential(&calls),
                }
            }
        } else if self.is_mutual_recursion(&function_name, &calls) {
            RecursionPattern {
                recursion_type: RecursionType::MutualRecursion,
                is_tail_recursive: false,
                complexity: ComplexityClass::Exponential,
                optimization_potential: OptimizationPotential::Medium,
            }
        } else {
            RecursionPattern {
                recursion_type: RecursionType::TreeRecursion,
                is_tail_recursive: false,
                complexity: self.estimate_complexity(&calls),
                optimization_potential: self.assess_optimization_potential(&calls),
            }
        };
        
        self.patterns.insert(function_name, pattern.clone());
        pattern
    }
    
    fn is_tail_recursive(&self, _function_name: &str, calls: &[String]) -> bool {
        // 简化实现：检查是否只有一个递归调用且在最后
        calls.len() == 1
    }
    
    fn is_mutual_recursion(&self, function_name: &str, calls: &[String]) -> bool {
        for call in calls {
            if let Some(sub_calls) = self.call_graph.get(call) {
                if sub_calls.contains(&function_name.to_string()) {
                    return true;
                }
            }
        }
        false
    }
    
    fn estimate_complexity(&self, calls: &[String]) -> ComplexityClass {
        match calls.len() {
            0 => ComplexityClass::Constant,
            1 => ComplexityClass::Linear,
            2 => ComplexityClass::Exponential,
            _ => ComplexityClass::Factorial,
        }
    }
    
    fn assess_optimization_potential(&self, calls: &[String]) -> OptimizationPotential {
        match calls.len() {
            0..=1 => OptimizationPotential::High,
            2 => OptimizationPotential::Medium,
            _ => OptimizationPotential::Low,
        }
    }
    
    /// 获取所有分析的模式
    pub fn get_patterns(&self) -> &HashMap<String, RecursionPattern> {
        &self.patterns
    }
    
    /// 生成优化建议
    pub fn generate_optimization_suggestions(&self) -> Vec<OptimizationSuggestion> {
        let mut suggestions = Vec::new();
        
        for (function_name, pattern) in &self.patterns {
            match pattern.optimization_potential {
                OptimizationPotential::High => {
                    if pattern.is_tail_recursive {
                        suggestions.push(OptimizationSuggestion {
                            function_name: function_name.clone(),
                            suggestion_type: SuggestionType::TailCallOptimization,
                            description: "Convert to iterative form using tail call optimization".to_string(),
                            expected_improvement: ImprovementMetric {
                                memory_reduction: 0.8,
                                performance_gain: 0.3,
                                stack_safety: true,
                            },
                        });
                    } else {
                        suggestions.push(OptimizationSuggestion {
                            function_name: function_name.clone(),
                            suggestion_type: SuggestionType::TrampolineOptimization,
                            description: "Use trampoline technique for stack safety".to_string(),
                            expected_improvement: ImprovementMetric {
                                memory_reduction: 0.6,
                                performance_gain: 0.1,
                                stack_safety: true,
                            },
                        });
                    }
                }
                OptimizationPotential::Medium => {
                    suggestions.push(OptimizationSuggestion {
                        function_name: function_name.clone(),
                        suggestion_type: SuggestionType::Memoization,
                        description: "Add memoization to avoid redundant calculations".to_string(),
                        expected_improvement: ImprovementMetric {
                            memory_reduction: -0.2, // 增加内存使用
                            performance_gain: 0.7,
                            stack_safety: false,
                        },
                    });
                }
                OptimizationPotential::Low => {
                    suggestions.push(OptimizationSuggestion {
                        function_name: function_name.clone(),
                        suggestion_type: SuggestionType::DepthLimiting,
                        description: "Add depth limiting to prevent stack overflow".to_string(),
                        expected_improvement: ImprovementMetric {
                            memory_reduction: 0.0,
                            performance_gain: 0.0,
                            stack_safety: true,
                        },
                    });
                }
            }
        }
        
        suggestions
    }
}

/// 递归模式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RecursionPattern {
    pub recursion_type: RecursionType,
    pub is_tail_recursive: bool,
    pub complexity: ComplexityClass,
    pub optimization_potential: OptimizationPotential,
}

/// 复杂度类别
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ComplexityClass {
    Constant,
    Logarithmic,
    Linear,
    Linearithmic,
    Quadratic,
    Cubic,
    Exponential,
    Factorial,
}

/// 优化潜力
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum OptimizationPotential {
    High,
    Medium,
    Low,
}

/// 优化建议
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationSuggestion {
    pub function_name: String,
    pub suggestion_type: SuggestionType,
    pub description: String,
    pub expected_improvement: ImprovementMetric,
}

/// 建议类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SuggestionType {
    TailCallOptimization,
    TrampolineOptimization,
    Memoization,
    IterativeConversion,
    DepthLimiting,
    ParallelRecursion,
}

/// 改进指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImprovementMetric {
    /// 内存减少比例（负值表示增加）
    pub memory_reduction: f64,
    /// 性能提升比例
    pub performance_gain: f64,
    /// 是否提供栈安全
    pub stack_safety: bool,
}

/// 异步递归示例集合
pub struct AsyncRecursionExamples;

impl AsyncRecursionExamples {
    /// 异步斐波那契数列（带记忆化）
    pub async fn fibonacci_memoized(
        n: u64,
        memo: Arc<Mutex<HashMap<u64, u64>>>,
        executor: Arc<AsyncRecursionExecutor>,
        mut context: RecursionContext,
    ) -> RecursiveAsyncResult<u64> {
        // 检查限制
        executor.check_depth_limit(&context)?;
        executor.check_timeout(&context)?;
        
        // 检查记忆化缓存
        {
            let memo_guard = memo.lock().unwrap();
            if let Some(&result) = memo_guard.get(&n) {
                return Ok(result);
            }
        }
        
        let result = match n {
            0 => 0,
            1 => 1,
            _ => {
                context.push_call(format!("fibonacci({})", n));
                
                // 递归调用
                let a = Box::pin(Self::fibonacci_memoized(
                    n - 1, 
                    Arc::clone(&memo), 
                    Arc::clone(&executor),
                    context.create_child_context(uuid::Uuid::new_v4().to_string())
                )).await?;
                
                let b = Box::pin(Self::fibonacci_memoized(
                    n - 2, 
                    Arc::clone(&memo), 
                    Arc::clone(&executor),
                    context.create_child_context(uuid::Uuid::new_v4().to_string())
                )).await?;
                
                context.pop_call();
                a + b
            }
        };
        
        // 存储到记忆化缓存
        memo.lock().unwrap().insert(n, result);
        
        Ok(result)
    }
    
    /// 异步阶乘（尾递归优化）
    pub async fn factorial_tail_recursive(n: u64, accumulator: u64) -> RecursiveAsyncResult<u64> {
        TailRecursionOptimizer::optimize_tail_recursion(
            (n, accumulator),
            |(n, _)| *n > 0,
            |(n, acc)| {
                Box::pin(async move {
                    #[cfg(feature = "tokio-adapter")]
                    tokio::task::yield_now().await;
                    Ok((n - 1, acc * n))
                })
            },
        ).await.map(|(_, acc)| acc)
    }
    
    /// 异步二叉树遍历
    pub async fn binary_tree_traversal<T>(
        node: Option<Arc<BinaryTreeNode<T>>>,
        executor: Arc<AsyncRecursionExecutor>,
        mut context: RecursionContext,
    ) -> RecursiveAsyncResult<Vec<T>>
    where
        T: Clone + Send + Sync + 'static,
    {
        executor.check_depth_limit(&context)?;
        executor.check_timeout(&context)?;
        
        match node {
            None => Ok(Vec::new()),
            Some(node) => {
                context.push_call("tree_traversal".to_string());
                
                let mut result = Vec::new();
                
                // 遍历左子树
                let left_result = Box::pin(Self::binary_tree_traversal(
                    node.left.clone(),
                    Arc::clone(&executor),
                    context.create_child_context(uuid::Uuid::new_v4().to_string())
                )).await?;
                result.extend(left_result);
                
                // 访问当前节点
                result.push(node.value.clone());
                
                // 遍历右子树
                let right_result = Box::pin(Self::binary_tree_traversal(
                    node.right.clone(),
                    Arc::clone(&executor),
                    context.create_child_context(uuid::Uuid::new_v4().to_string())
                )).await?;
                result.extend(right_result);
                
                context.pop_call();
                Ok(result)
            }
        }
    }
    
    /// 异步快速排序
    pub async fn quicksort_async<T>(
        mut arr: Vec<T>,
        executor: Arc<AsyncRecursionExecutor>,
        mut context: RecursionContext,
    ) -> RecursiveAsyncResult<Vec<T>>
    where
        T: Clone + PartialOrd + Send + Sync + 'static,
    {
        executor.check_depth_limit(&context)?;
        executor.check_timeout(&context)?;
        
        if arr.len() <= 1 {
            return Ok(arr);
        }
        
        context.push_call(format!("quicksort(len={})", arr.len()));
        
        // 选择枢轴
        let pivot_index = arr.len() / 2;
        let pivot = arr.remove(pivot_index);
        
        // 分区
        let mut less = Vec::new();
        let mut greater = Vec::new();
        
        for item in arr {
            if item <= pivot {
                less.push(item);
            } else {
                greater.push(item);
            }
        }
        
        // 递归排序
        let less_sorted = Box::pin(Self::quicksort_async(
            less,
            Arc::clone(&executor),
            context.create_child_context(uuid::Uuid::new_v4().to_string())
        )).await?;
        
        let greater_sorted = Box::pin(Self::quicksort_async(
            greater,
            Arc::clone(&executor),
            context.create_child_context(uuid::Uuid::new_v4().to_string())
        )).await?;
        
        // 合并结果
        let mut result = less_sorted;
        result.push(pivot);
        result.extend(greater_sorted);
        
        context.pop_call();
        Ok(result)
    }
    
    /// 使用蹦床技术的递归
    pub async fn trampoline_example(n: u64) -> RecursiveAsyncResult<u64> {
        fn factorial_trampoline(n: u64, acc: u64) -> TrampolineComputation<u64> {
            if n == 0 {
                TrampolineComputation::Done(acc)
            } else {
                TrampolineComputation::Call(Box::pin(async move {
                    #[cfg(feature = "tokio-adapter")]
                    tokio::task::yield_now().await;
                    Ok(factorial_trampoline(n - 1, acc * n))
                }))
            }
        }
        
        TailRecursionOptimizer::trampoline_optimization(factorial_trampoline(n, 1)).await
    }
}

/// 二叉树节点
#[derive(Debug, Clone)]
pub struct BinaryTreeNode<T> {
    pub value: T,
    pub left: Option<Arc<BinaryTreeNode<T>>>,
    pub right: Option<Arc<BinaryTreeNode<T>>>,
}

impl<T> BinaryTreeNode<T> {
    pub fn new(value: T) -> Self {
        Self {
            value,
            left: None,
            right: None,
        }
    }
    
    pub fn with_children(
        value: T,
        left: Option<Arc<BinaryTreeNode<T>>>,
        right: Option<Arc<BinaryTreeNode<T>>>,
    ) -> Self {
        Self { value, left, right }
    }
}

impl Default for RecursionPatternAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_async_recursion_executor() {
        let config = RecursionConfig::default();
        let executor = Arc::new(AsyncRecursionExecutor::new(config));
        
        let result = executor.execute_recursive(
            "test_function".to_string(),
            |input: i32, _context, _executor| {
                Box::pin(async move {
                    if input <= 0 {
                        Ok(1)
                    } else {
                        Ok(input * 2)
                    }
                })
            },
            5,
        ).await;
        
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 10);
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_fibonacci_memoized() {
        let config = RecursionConfig::default();
        let executor = Arc::new(AsyncRecursionExecutor::new(config));
        let memo = Arc::new(Mutex::new(HashMap::new()));
        let context = RecursionContext::new("test".to_string());
        
        let result = AsyncRecursionExamples::fibonacci_memoized(10, memo, executor, context).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 55);
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_factorial_tail_recursive() {
        let result = AsyncRecursionExamples::factorial_tail_recursive(5, 1).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 120);
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_trampoline_example() {
        let result = AsyncRecursionExamples::trampoline_example(5).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 120);
    }
    
    #[test]
    fn test_recursion_pattern_analyzer() {
        let mut analyzer = RecursionPatternAnalyzer::new();
        
        let pattern = analyzer.analyze_pattern(
            "fibonacci".to_string(),
            vec!["fibonacci".to_string(), "fibonacci".to_string()],
        );
        
        assert_eq!(pattern.recursion_type, RecursionType::DirectRecursion);
        assert_eq!(pattern.complexity, ComplexityClass::Exponential);
    }
    
    #[test]
    fn test_recursion_metrics() {
        let mut metrics = RecursionMetrics::default();
        
        metrics.update_call(5, Duration::from_millis(100), 1024);
        metrics.record_success();
        
        assert_eq!(metrics.total_calls, 1);
        assert_eq!(metrics.max_depth_reached, 5);
        assert_eq!(metrics.success_count, 1);
        assert_eq!(metrics.success_rate(), 1.0);
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_binary_tree_traversal() {
        let config = RecursionConfig::default();
        let executor = Arc::new(AsyncRecursionExecutor::new(config));
        let context = RecursionContext::new("test".to_string());
        
        // 创建简单的二叉树
        let leaf1 = Arc::new(BinaryTreeNode::new(1));
        let leaf2 = Arc::new(BinaryTreeNode::new(3));
        let root = Arc::new(BinaryTreeNode::with_children(2, Some(leaf1), Some(leaf2)));
        
        let result = AsyncRecursionExamples::binary_tree_traversal(
            Some(root),
            executor,
            context,
        ).await;
        
        assert!(result.is_ok());
        let values = result.unwrap();
        assert_eq!(values, vec![1, 2, 3]);
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_quicksort_async() {
        let config = RecursionConfig::default();
        let executor = Arc::new(AsyncRecursionExecutor::new(config));
        let context = RecursionContext::new("test".to_string());
        
        let arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        let result = AsyncRecursionExamples::quicksort_async(arr, executor, context).await;
        
        assert!(result.is_ok());
        let sorted = result.unwrap();
        assert_eq!(sorted, vec![1, 1, 2, 3, 4, 5, 5, 6, 9]);
    }
}
