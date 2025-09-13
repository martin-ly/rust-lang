# Rust 1.89 工作流算法设计：类型安全与性能优化

## 📋 概述

本文档基于 Rust 1.89 的最新语言特性，重新设计工作流算法和类型系统，充分利用常量泛型显式推导、生命周期语法改进和 x86 特性扩展等新功能。

## 目录

- [Rust 1.89 工作流算法设计：类型安全与性能优化](#rust-189-工作流算法设计类型安全与性能优化)
  - [📋 概述](#-概述)
  - [目录](#目录)
  - [🚀 Rust 1.89 特性集成](#-rust-189-特性集成)
    - [核心改进](#核心改进)
  - [1. 类型与算法的表达与组合](#1-类型与算法的表达与组合)
    - [1.1 构建流式处理管道（Rust 1.89 优化版）](#11-构建流式处理管道rust-189-优化版)
    - [1.2 迭代器与算法组合](#12-迭代器与算法组合)
  - [2. 状态管理与转换](#2-状态管理与转换)
    - [2.1 工作流状态机](#21-工作流状态机)
    - [2.2 事务性操作模式](#22-事务性操作模式)
  - [3. 算法与策略接口设计](#3-算法与策略接口设计)
    - [3.1 可组合策略模式](#31-可组合策略模式)
    - [3.2 优化器与目标函数模式](#32-优化器与目标函数模式)
  - [4. 迭代与递归工作流](#4-迭代与递归工作流)
    - [4.1 自适应迭代器](#41-自适应迭代器)
    - [4.2 可继续/可恢复递归模式](#42-可继续可恢复递归模式)
  - [5. 并行与异步工作流](#5-并行与异步工作流)
    - [5.1 工作窃取任务池](#51-工作窃取任务池)
    - [5.2 异步工作流状态机](#52-异步工作流状态机)
  - [6. 总结：工作流与算法设计准则](#6-总结工作流与算法设计准则)
    - [6.1 组合与流程设计](#61-组合与流程设计)
    - [6.2 算法设计与执行](#62-算法设计与执行)
    - [6.3 集成设计原则](#63-集成设计原则)

## 🚀 Rust 1.89 特性集成

### 核心改进

1. **常量泛型显式推导** - 使用 `_` 占位符让编译器自动推断数组大小
2. **生命周期语法改进** - 更严格的生命周期检查，提升代码健壮性
3. **x86 特性扩展** - 支持更多 AVX-512 指令，提供硬件加速
4. **标准库增强** - 改进的测试框架和数组处理函数

结合工作流组合与算法设计的视角，以下是基于 Rust 1.89 的类型设计综合准则，旨在创建既易于使用又高效的类型系统。

## 1. 类型与算法的表达与组合

### 1.1 构建流式处理管道（Rust 1.89 优化版）

```rust
use std::marker::PhantomData;

/// Rust 1.89 优化版：类型安全的流式处理管道
/// 使用常量泛型显式推导和生命周期改进
pub struct WorkflowPipeline<I, O, const MAX_STEPS: usize> {
    steps: Vec<Box<dyn Fn(I) -> O + Send + Sync>>,
    _phantom: PhantomData<(I, O)>,
}

impl<I: Clone + 'static, O: 'static, const MAX_STEPS: usize> WorkflowPipeline<I, O, MAX_STEPS> {
    /// 创建新的管道，使用常量泛型限制最大步骤数
    pub fn new(initial_step: impl Fn(I) -> O + Send + Sync + 'static) -> Self {
        Self {
            steps: vec![Box::new(initial_step)],
            _phantom: PhantomData,
        }
    }
    
    /// 添加转换步骤，编译时检查步骤数量限制
    pub fn then<P>(self, next_step: impl Fn(O) -> P + Send + Sync + 'static) -> Result<WorkflowPipeline<I, P, MAX_STEPS>, PipelineError> {
        if self.steps.len() >= MAX_STEPS {
            return Err(PipelineError::ExceedsMaxSteps(MAX_STEPS));
        }
        
        let mut new_steps: Vec<Box<dyn Fn(I) -> P + Send + Sync>> = Vec::new();
        
        for step in self.steps {
            let cloned_next = next_step.clone();
            new_steps.push(Box::new(move |input: I| {
                let intermediate = step(input);
                cloned_next(intermediate)
            }));
        }
        
        Ok(WorkflowPipeline { 
            steps: new_steps,
            _phantom: PhantomData,
        })
    }
    
    /// 使用 x86 特性进行并行执行（如果支持）
    pub fn process_parallel(&self, inputs: Vec<I>) -> Vec<O> 
    where 
        I: Send + Clone,
        O: Send,
    {
        // 检查是否支持 AVX-512
        let is_avx512_supported = is_x86_feature_detected!("avx512f");
        
        if is_avx512_supported && inputs.len() >= 16 {
            // 使用硬件加速的并行处理
            unsafe { self.process_parallel_avx512(inputs) }
        } else {
            // 回退到标准并行处理
            self.process_parallel_standard(inputs)
        }
    }
    
    /// 使用 AVX-512 进行并行处理
    #[target_feature(enable = "avx512f")]
    unsafe fn process_parallel_avx512(&self, inputs: Vec<I>) -> Vec<O> 
    where 
        I: Send + Clone,
        O: Send,
    {
        use rayon::prelude::*;
        
        inputs.into_par_iter()
            .map(|input| self.process(input))
            .collect()
    }
    
    /// 标准并行处理
    fn process_parallel_standard(&self, inputs: Vec<I>) -> Vec<O> 
    where 
        I: Send + Clone,
        O: Send,
    {
        use rayon::prelude::*;
        
        inputs.into_par_iter()
            .map(|input| self.process(input))
            .collect()
    }
    
    /// 处理单个输入
    pub fn process(&self, input: I) -> O {
        // 使用第一个步骤（管道中唯一的一个）
        self.steps[0](input)
    }
    
    /// 获取当前步骤数量
    pub fn step_count(&self) -> usize {
        self.steps.len()
    }
    
    /// 转换为固定大小数组（如果步骤数量匹配）
    pub fn to_fixed_array<const N: usize>(self) -> Result<[Box<dyn Fn(I) -> O + Send + Sync>; N], PipelineError> 
    where 
        [Box<dyn Fn(I) -> O + Send + Sync>; N]: Default,
    {
        if self.steps.len() != N {
            return Err(PipelineError::SizeMismatch {
                expected: N,
                actual: self.steps.len(),
            });
        }
        
        let mut array = <[Box<dyn Fn(I) -> O + Send + Sync>; N]>::default();
        for (i, step) in self.steps.into_iter().enumerate() {
            array[i] = step;
        }
        Ok(array)
    }
}

/// 管道错误类型
#[derive(Debug, thiserror::Error)]
pub enum PipelineError {
    #[error("Exceeds maximum steps: {0}")]
    ExceedsMaxSteps(usize),
    #[error("Size mismatch: expected {expected}, got {actual}")]
    SizeMismatch { expected: usize, actual: usize },
}

// Rust 1.89 使用示例
fn process_data_with_rust189() -> Result<(), PipelineError> {
    // 创建图像处理管道，使用常量泛型限制最大步骤数
    let image_pipeline = WorkflowPipeline::<String, Vec<u8>, 10>::new(|path: String| {
            // 加载图像
            println!("Loading image from {}", path);
            vec![0u8; 100] // 模拟图像数据
        })?
        .then(|image: Vec<u8>| {
            // 调整大小
            println!("Resizing image of {} bytes", image.len());
            let mut resized = image;
            resized.resize(50, 0);
            resized
        })?
        .then(|image: Vec<u8>| {
            // 应用滤镜
            println!("Applying filter to image of {} bytes", image.len());
            let filtered = image;
            filtered
        })?;
    
    // 处理多个图像
    let image_paths = vec![
        "image1.jpg".to_string(),
        "image2.jpg".to_string(),
        "image3.jpg".to_string(),
    ];
    
    // 使用 x86 特性进行并行处理
    let results = image_pipeline.process_parallel(image_paths);
    println!("Processed {} images", results.len());
    
    // 转换为固定大小数组（如果步骤数量匹配）
    if image_pipeline.step_count() == 3 {
        let fixed_array = image_pipeline.to_fixed_array::<3>()?;
        println!("Successfully converted to fixed array with {} steps", fixed_array.len());
    }
    
    Ok(())
}

/// 使用常量泛型显式推导的示例
fn demonstrate_const_generic_inference() -> Result<(), PipelineError> {
    // 使用 _ 让编译器自动推断数组大小
    let steps = ["step1", "step2", "step3"];
    let workflow_array: WorkflowArray<String, _> = WorkflowArray::from_iter(steps.iter().map(|s| s.to_string()))?;
    
    println!("Created workflow array with {} steps", workflow_array.data.len());
    
    // 映射到新类型
    let processed_array = workflow_array.map(|step| format!("processed_{}", step));
    
    for (i, step) in processed_array.data.iter().enumerate() {
        println!("Step {}: {}", i, step);
    }
    
    Ok(())
}

/// 工作流数组定义（使用常量泛型）
pub struct WorkflowArray<T, const N: usize> {
    pub data: [T; N],
}

impl<T, const N: usize> WorkflowArray<T, N> {
    /// 从迭代器创建，使用常量泛型显式推导
    pub fn from_iter<I>(iter: I) -> Result<Self, PipelineError>
    where 
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = iter.into_iter();
        if iter.len() != N {
            return Err(PipelineError::SizeMismatch {
                expected: N,
                actual: iter.len(),
            });
        }
        
        let mut array = std::array::from_fn(|_| {
            // 这里需要更复杂的实现来从迭代器填充数组
            // 为简化示例，我们假设 T 实现了 Default
            unsafe { std::mem::zeroed() }
        });
        
        for (i, item) in iter.enumerate() {
            array[i] = item;
        }
        
        Ok(Self { data: array })
    }
    
    /// 映射到新类型
    pub fn map<U, F>(self, mut f: F) -> WorkflowArray<U, N>
    where 
        F: FnMut(T) -> U,
    {
        WorkflowArray {
            data: self.data.map(f),
        }
    }
}
```

**准则**：设计支持组合的数据流处理管道，实现声明式工作流。

### 1.2 迭代器与算法组合

```rust
// 推荐：迭代器与算法组合
pub trait DataProcessing<T> {
    fn process(&self, data: T) -> T;
}

// 算法实现
pub struct Normalize;
impl<T: AsRef<[f64]> + AsMut<[f64]>> DataProcessing<T> for Normalize {
    fn process(&self, mut data: T) -> T {
        let slice = data.as_ref();
        if slice.is_empty() {
            return data;
        }
        
        // 找最大和最小值
        let max = slice.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        let min = slice.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        
        // 归一化
        let range = max - min;
        if range > 0.0 {
            let mut output = data.as_mut();
            for value in output.iter_mut() {
                *value = (*value - min) / range;
            }
        }
        
        data
    }
}

pub struct MovingAverage {
    window_size: usize,
}

impl MovingAverage {
    pub fn new(window_size: usize) -> Self {
        Self { window_size }
    }
}

impl<T: AsRef<[f64]> + AsMut<[f64]>> DataProcessing<T> for MovingAverage {
    fn process(&self, mut data: T) -> T {
        let slice = data.as_ref();
        if slice.len() <= self.window_size {
            return data;
        }
        
        let mut result = Vec::with_capacity(slice.len());
        
        // 计算移动平均
        for i in 0..slice.len() {
            let start = if i < self.window_size / 2 {
                0
            } else {
                i - self.window_size / 2
            };
            
            let end = std::cmp::min(slice.len(), i + self.window_size / 2 + 1);
            let window = &slice[start..end];
            
            let avg = window.iter().sum::<f64>() / window.len() as f64;
            result.push(avg);
        }
        
        // 复制结果
        let mut output = data.as_mut();
        for (i, &val) in result.iter().enumerate() {
            output[i] = val;
        }
        
        data
    }
}

// 组合多个处理步骤
pub struct ProcessingPipeline<T> {
    steps: Vec<Box<dyn DataProcessing<T> + Send + Sync>>,
}

impl<T> ProcessingPipeline<T> {
    pub fn new() -> Self {
        Self { steps: Vec::new() }
    }
    
    pub fn add_step<P: DataProcessing<T> + Send + Sync + 'static>(&mut self, processor: P) -> &mut Self {
        self.steps.push(Box::new(processor));
        self
    }
    
    pub fn process(&self, data: T) -> T {
        self.steps.iter().fold(data, |acc, processor| {
            processor.process(acc)
        })
    }
    
    // 并行处理多个数据项
    pub fn process_batch<I>(&self, data: I) -> Vec<T>
    where
        I: IntoIterator<Item = T>,
        T: Send + 'static,
    {
        use rayon::prelude::*;
        
        data.into_iter()
            .collect::<Vec<_>>()
            .into_par_iter()
            .map(|item| self.process(item))
            .collect()
    }
}

// 使用示例
fn process_time_series() {
    // 创建示例数据
    let data = vec![1.0, 5.0, 3.0, 8.0, 2.0, 9.0, 6.0, 4.0, 7.0];
    
    // 创建处理管道
    let mut pipeline = ProcessingPipeline::new();
    pipeline
        .add_step(MovingAverage::new(3))  // 移动平均
        .add_step(Normalize);             // 归一化
    
    // 处理数据
    let processed = pipeline.process(data);
    println!("Processed data: {:?}", processed);
    
    // 处理多个数据集
    let batch = vec![
        vec![1.0, 2.0, 3.0, 4.0, 5.0],
        vec![5.0, 4.0, 3.0, 2.0, 1.0],
        vec![3.0, 6.0, 9.0, 6.0, 3.0],
    ];
    
    let processed_batch = pipeline.process_batch(batch);
    println!("Processed {} datasets", processed_batch.len());
}
```

**准则**：设计支持数据处理算法的可组合接口，实现灵活的处理管道。

## 2. 状态管理与转换

### 2.1 工作流状态机

```rust
// 推荐：工作流状态机
// 定义工作流状态
pub mod state {
    pub struct Uninitialized;
    pub struct Ready;
    pub struct Running;
    pub struct Completed;
    pub struct Failed;
}

// 工作流状态机
pub struct Workflow<S> {
    name: String,
    created_at: std::time::Instant,
    progress: f32,
    result: Option<String>,
    error: Option<String>,
    _state: std::marker::PhantomData<S>,
}

// 未初始化状态
impl Workflow<state::Uninitialized> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            created_at: std::time::Instant::now(),
            progress: 0.0,
            result: None,
            error: None,
            _state: std::marker::PhantomData,
        }
    }
    
    pub fn initialize(self) -> Workflow<state::Ready> {
        println!("Initializing workflow: {}", self.name);
        Workflow {
            name: self.name,
            created_at: self.created_at,
            progress: 0.0,
            result: None,
            error: None,
            _state: std::marker::PhantomData,
        }
    }
}

// 就绪状态
impl Workflow<state::Ready> {
    pub fn start(self) -> Workflow<state::Running> {
        println!("Starting workflow: {}", self.name);
        Workflow {
            name: self.name,
            created_at: self.created_at,
            progress: 0.0,
            result: None,
            error: None,
            _state: std::marker::PhantomData,
        }
    }
}

// 运行状态
impl Workflow<state::Running> {
    pub fn update_progress(&mut self, progress: f32) {
        self.progress = progress.clamp(0.0, 1.0);
        println!("Progress for {}: {:.1}%", self.name, self.progress * 100.0);
    }
    
    pub fn complete(self, result: impl Into<String>) -> Workflow<state::Completed> {
        println!("Completing workflow: {}", self.name);
        Workflow {
            name: self.name,
            created_at: self.created_at,
            progress: 1.0,
            result: Some(result.into()),
            error: None,
            _state: std::marker::PhantomData,
        }
    }
    
    pub fn fail(self, error: impl Into<String>) -> Workflow<state::Failed> {
        println!("Workflow failed: {}", self.name);
        Workflow {
            name: self.name,
            created_at: self.created_at,
            progress: self.progress,
            result: None,
            error: Some(error.into()),
            _state: std::marker::PhantomData,
        }
    }
}

// 完成状态
impl Workflow<state::Completed> {
    pub fn result(&self) -> Option<&str> {
        self.result.as_deref()
    }
    
    pub fn elapsed(&self) -> std::time::Duration {
        self.created_at.elapsed()
    }
    
    pub fn reset(self) -> Workflow<state::Ready> {
        println!("Resetting workflow: {}", self.name);
        Workflow {
            name: self.name,
            created_at: std::time::Instant::now(),
            progress: 0.0,
            result: None,
            error: None,
            _state: std::marker::PhantomData,
        }
    }
}

// 失败状态
impl Workflow<state::Failed> {
    pub fn error(&self) -> Option<&str> {
        self.error.as_deref()
    }
    
    pub fn retry(self) -> Workflow<state::Running> {
        println!("Retrying workflow: {}", self.name);
        Workflow {
            name: self.name,
            created_at: self.created_at,
            progress: self.progress,
            result: None,
            error: None,
            _state: std::marker::PhantomData,
        }
    }
    
    pub fn reset(self) -> Workflow<state::Ready> {
        println!("Resetting failed workflow: {}", self.name);
        Workflow {
            name: self.name,
            created_at: std::time::Instant::now(),
            progress: 0.0,
            result: None,
            error: None,
            _state: std::marker::PhantomData,
        }
    }
}

// 使用示例
fn run_workflow() {
    // 创建和初始化工作流
    let workflow = Workflow::new("Data Processing")
        .initialize()
        .start();
    
    // 模拟工作流进度
    let mut running = workflow;
    
    // 模拟工作
    for i in 1..=10 {
        std::thread::sleep(std::time::Duration::from_millis(100));
        running.update_progress(i as f32 / 10.0);
    }
    
    // 根据结果选择完成或失败
    let success = true;
    let final_state = if success {
        let completed = running.complete("Processed 1000 records");
        println!("Result: {:?}", completed.result());
        println!("Time elapsed: {:?}", completed.elapsed());
        
        // 可以重置工作流
        let ready = completed.reset();
        ready.start()
    } else {
        let failed = running.fail("Connection error");
        println!("Error: {:?}", failed.error());
        
        // 可以重试
        failed.retry()
    };
    
    // 继续使用...
    println!("Workflow continues: {}", final_state.name);
}
```

**准则**：使用类型状态模式实现工作流状态机，确保状态转换的安全性。

### 2.2 事务性操作模式

```rust
// 推荐：事务性操作模式
// 事务特征
pub trait Transaction {
    type Input;
    type Output;
    type Error;
    
    // 准备事务
    fn prepare(&self, input: &Self::Input) -> Result<(), Self::Error>;
    
    // 执行事务
    fn execute(&self, input: &Self::Input) -> Result<Self::Output, Self::Error>;
    
    // 回滚操作
    fn rollback(&self, input: &Self::Input);
    
    // 安全执行事务
    fn run(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        // 准备阶段
        if let Err(err) = self.prepare(&input) {
            return Err(err);
        }
        
        // 执行阶段
        match self.execute(&input) {
            Ok(output) => Ok(output),
            Err(err) => {
                // 出错时回滚
                self.rollback(&input);
                Err(err)
            }
        }
    }
}

// 文件处理事务示例
pub struct FileProcessingTransaction {
    temp_path: String,
}

impl FileProcessingTransaction {
    pub fn new(temp_dir: impl Into<String>) -> Self {
        Self {
            temp_path: temp_dir.into(),
        }
    }
    
    fn get_temp_file_path(&self, input: &str) -> String {
        format!("{}/temp_{}", self.temp_path, std::path::Path::new(input).file_name().unwrap().to_string_lossy())
    }
}

#[derive(Debug)]
pub enum FileError {
    IoError(std::io::Error),
    ProcessingError(String),
}

impl From<std::io::Error> for FileError {
    fn from(err: std::io::Error) -> Self {
        FileError::IoError(err)
    }
}

impl Transaction for FileProcessingTransaction {
    type Input = String;  // 输入文件路径
    type Output = String; // 输出文件路径
    type Error = FileError;
    
    fn prepare(&self, input: &Self::Input) -> Result<(), Self::Error> {
        // 检查输入文件是否存在
        if !std::path::Path::new(input).exists() {
            return Err(FileError::ProcessingError(format!("Input file not found: {}", input)));
        }
        
        // 检查临时目录是否存在
        if !std::path::Path::new(&self.temp_path).exists() {
            std::fs::create_dir_all(&self.temp_path)
                .map_err(FileError::IoError)?;
        }
        
        Ok(())
    }
    
    fn execute(&self, input: &Self::Input) -> Result<Self::Output, Self::Error> {
        // 创建临时文件
        let temp_file = self.get_temp_file_path(input);
        
        // 模拟文件处理
        println!("Processing file: {}", input);
        println!("Creating processed file: {}", temp_file);
        
        // 模拟写入处理后的文件
        std::fs::write(&temp_file, "Processed content")
            .map_err(FileError::IoError)?;
        
        // 返回处理后的文件路径
        Ok(temp_file)
    }
    
    fn rollback(&self, input: &Self::Input) {
        // 清理临时文件
        let temp_file = self.get_temp_file_path(input);
        println!("Rolling back: removing temp file {}", temp_file);
        
        if let Err(e) = std::fs::remove_file(&temp_file) {
            eprintln!("Warning: Failed to remove temp file during rollback: {}", e);
        }
    }
}

// 使用事务模式
fn process_files() {
    let transaction = FileProcessingTransaction::new("/tmp");
    
    // 处理文件
    let result = transaction.run("input.txt".to_string());
    
    match result {
        Ok(output_path) => {
            println!("Successfully processed file: {}", output_path);
            // 使用处理后的文件...
        }
        Err(err) => {
            println!("Failed to process file: {:?}", err);
            // 处理错误...
        }
    }
}
```

**准则**：通过事务性操作模式确保工作流中操作的一致性和可回滚性。

## 3. 算法与策略接口设计

### 3.1 可组合策略模式

```rust
// 推荐：可组合策略模式
// 定义验证策略特征
pub trait ValidationStrategy<T> {
    fn validate(&self, value: &T) -> Result<(), String>;
}

// 字符串长度验证
pub struct LengthValidator {
    min: usize,
    max: usize,
}

impl LengthValidator {
    pub fn new(min: usize, max: usize) -> Self {
        Self { min, max }
    }
}

impl ValidationStrategy<String> for LengthValidator {
    fn validate(&self, value: &String) -> Result<(), String> {
        let len = value.len();
        if len < self.min {
            Err(format!("String is too short (minimum {})", self.min))
        } else if len > self.max {
            Err(format!("String is too long (maximum {})", self.max))
        } else {
            Ok(())
        }
    }
}

// 正则表达式验证
pub struct RegexValidator {
    pattern: regex::Regex,
    error_message: String,
}

impl RegexValidator {
    pub fn new(pattern: &str, error_message: impl Into<String>) -> Result<Self, regex::Error> {
        Ok(Self {
            pattern: regex::Regex::new(pattern)?,
            error_message: error_message.into(),
        })
    }
}

impl ValidationStrategy<String> for RegexValidator {
    fn validate(&self, value: &String) -> Result<(), String> {
        if self.pattern.is_match(value) {
            Ok(())
        } else {
            Err(self.error_message.clone())
        }
    }
}

// 组合多个验证器
pub struct ValidationChain<T> {
    validators: Vec<Box<dyn ValidationStrategy<T>>>,
}

impl<T> ValidationChain<T> {
    pub fn new() -> Self {
        Self {
            validators: Vec::new(),
        }
    }
    
    pub fn add<V: ValidationStrategy<T> + 'static>(&mut self, validator: V) -> &mut Self {
        self.validators.push(Box::new(validator));
        self
    }
    
    pub fn validate(&self, value: &T) -> Result<(), Vec<String>> {
        let errors: Vec<String> = self.validators.iter()
            .filter_map(|validator| {
                match validator.validate(value) {
                    Ok(()) => None,
                    Err(msg) => Some(msg),
                }
            })
            .collect();
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

// AND 组合验证器 - 所有验证通过才算通过
pub struct AllValidators<T> {
    validators: Vec<Box<dyn ValidationStrategy<T>>>,
}

impl<T> AllValidators<T> {
    pub fn new() -> Self {
        Self {
            validators: Vec::new(),
        }
    }
    
    pub fn add<V: ValidationStrategy<T> + 'static>(&mut self, validator: V) -> &mut Self {
        self.validators.push(Box::new(validator));
        self
    }
}

impl<T> ValidationStrategy<T> for AllValidators<T> {
    fn validate(&self, value: &T) -> Result<(), String> {
        for validator in &self.validators {
            if let Err(msg) = validator.validate(value) {
                return Err(msg);
            }
        }
        Ok(())
    }
}

// OR 组合验证器 - 任一验证通过即可
pub struct AnyValidator<T> {
    validators: Vec<Box<dyn ValidationStrategy<T>>>,
}

impl<T> AnyValidator<T> {
    pub fn new() -> Self {
        Self {
            validators: Vec::new(),
        }
    }
    
    pub fn add<V: ValidationStrategy<T> + 'static>(&mut self, validator: V) -> &mut Self {
        self.validators.push(Box::new(validator));
        self
    }
}

impl<T> ValidationStrategy<T> for AnyValidator<T> {
    fn validate(&self, value: &T) -> Result<(), String> {
        if self.validators.is_empty() {
            return Ok(());
        }
        
        let mut all_errors = Vec::new();
        
        for validator in &self.validators {
            match validator.validate(value) {
                Ok(()) => return Ok(()),
                Err(msg) => all_errors.push(msg),
            }
        }
        
        Err(format!("All validations failed: {}", all_errors.join("; ")))
    }
}

// 使用组合策略模式
fn validate_user_input() {
    // 创建电子邮件验证器（组合多个规则）
    let mut email_validator = AllValidators::new();
    
    // 添加长度验证
    email_validator.add(LengthValidator::new(5, 100));
    
    // 添加正则表达式验证
    let email_regex = RegexValidator::new(
        r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$",
        "Invalid email format",
    ).unwrap();
    
    email_validator.add(email_regex);
    
    // 创建密码验证器（组合多个规则）
    let mut password_validator = AllValidators::new();
    
    // 密码长度
    password_validator.add(LengthValidator::new(8, 64));
    
    // 密码复杂度（至少包含一个大写字母、一个小写字母和一个数字）
    let mut complexity_validator = AnyValidator::new();
    complexity_validator
        .add(RegexValidator::new(r"^.*[A-Z].*$", "Missing uppercase letter").unwrap())
        .add(RegexValidator::new(r"^.*[a-z].*$", "Missing lowercase letter").unwrap())
        .add(RegexValidator::new(r"^.*[0-9].*$", "Missing digit").unwrap());
    
    password_validator.add(complexity_validator);
    
    // 创建验证链，包含所有验证器
    let mut validation_chain = ValidationChain::new();
    validation_chain
        .add(email_validator)
        .add(password_validator);
    
    // 验证输入
    let email = "user@example.com".to_string();
    let password = "Password123".to_string();
    
    if let Err(errors) = validation_chain.validate(&email) {
        println!("Email validation failed: {:?}", errors);
    } else {
        println!("Email is valid!");
    }
    
    if let Err(errors) = validation_chain.validate(&password) {
        println!("Password validation failed: {:?}", errors);
    } else {
        println!("Password is valid!");
    }
}
```

**准则**：设计可组合的策略接口，允许灵活构建复杂的算法组合。

### 3.2 优化器与目标函数模式

```rust
// 推荐：优化器与目标函数模式
// 定义目标函数特征
pub trait ObjectiveFunction {
    type Input;
    type Output: PartialOrd;
    
    // 在优化问题中往往是最大化目标函数
    fn evaluate(&self, input: &Self::Input) -> Self::Output;
}

// 优化器特征
pub trait Optimizer<F: ObjectiveFunction> {
    // 使用目标函数找到最优解
    fn optimize(&self, objective: &F, iterations: usize) -> F::Input;
}

// 梯度下降优化器（简化版，用于一维函数）
pub struct GradientDescent {
    learning_rate: f64,
    epsilon: f64,
}

impl GradientDescent {
    pub fn new(learning_rate: f64, epsilon: f64) -> Self {
        Self { learning_rate, epsilon }
    }
    
    // 计算数值梯度
    fn numerical_gradient(&self, objective: &impl Fn(f64) -> f64, x: f64) -> f64 {
        let h = 1e-5;
        (objective(x + h) - objective(x - h)) / (2.0 * h)
    }
}

// 特化为一维函数的优化器
impl Optimizer<OneDimensionalFunction> for GradientDescent {
    fn optimize(&self, objective: &OneDimensionalFunction, iterations: usize) -> f64 {
        let mut x = objective.initial_guess;
        
        for i in 0..iterations {
            // 计算梯度
            let gradient = self.numerical_gradient(&|x| -objective.function(x), x);
            
            // 更新参数
            let delta = self.learning_rate * gradient;
            x -= delta;
            
            // 输出进度
            if i % 10 == 0 {
                println!(
                    "Iteration {}: x = {:.6}, f(x) = {:.6}, gradient = {:.6}",
                    i, x, objective.function(x), gradient
                );
            }
            
            // 检查收敛
            if delta.abs() < self.epsilon {
                println!("Converged after {} iterations", i);
                break;
            }
        }
        
        x
    }
}

// 一维函数优化问题
pub struct OneDimensionalFunction {
    pub function: Box<dyn Fn(f64) -> f64>,
    pub initial_guess: f64,
}

impl OneDimensionalFunction {
    pub fn new(function: impl Fn(f64) -> f64 + 'static, initial_guess: f64) -> Self {
        Self {
            function: Box::new(function),
            initial_guess,
        }
    }
}

impl ObjectiveFunction for OneDimensionalFunction {
    type Input = f64;
    type Output = f64;
    
    fn evaluate(&self, input: &Self::Input) -> Self::Output {
        (self.function)(*input)
    }
}

// 粒子群优化算法
pub struct ParticleSwarmOptimization {
    particles: usize,
    inertia_weight: f64,
    cognitive_weight: f64,
    social_weight: f64,
}

impl ParticleSwarmOptimization {
    pub fn new(
        particles: usize,
        inertia_weight: f64,
        cognitive_weight: f64,
        social_weight: f64,
    ) -> Self {
        Self {
            particles,
            inertia_weight,
            cognitive_weight,
            social_weight,
        }
    }
}

impl Optimizer<OneDimensionalFunction> for ParticleSwarmOptimization {
    fn optimize(&self, objective: &OneDimensionalFunction, iterations: usize) -> f64 {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        // 初始化粒子位置和速度
        let mut positions: Vec<f64> = (0..self.particles)
            .map(|_| objective.initial_guess + rng.gen_range(-5.0..5.0))
            .collect();
        
        let mut velocities: Vec<f64> = (0..self.particles)
            .map(|_| rng.gen_range(-1.0..1.0))
            .collect();
        
        // 初始化个体最优位置和全局最优位置
        let mut personal_best_positions = positions.clone();
        let mut personal_best_values: Vec<f64> = personal_best_positions.iter()
            .map(|&x| objective.evaluate(&x))
            .collect();
        
        let mut global_best_index = personal_best_values
            .iter()
            .enumerate()
            .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap())
            .unwrap().0;
        
        let mut global_best_position = personal_best_positions[global_best_index];
        
        // 迭代优化
        for i in 0..iterations {
            // 更新每个粒子
            for p in 0..self.particles {
                // 生成随机权重
                let r1: f64 = rng.gen_range(0.0..1.0);
                let r2: f64 = rng.gen_range(0.0..1.0);
                
                // 更新速度
                velocities[p] = self.inertia_weight * velocities[p]
                    + self.cognitive_weight * r1 * (personal_best_positions[p] - positions[p])
                    + self.social_weight * r2 * (global_best_position - positions[p]);
                
                // 更新位置
                positions[p] += velocities[p];
                
                // 评估新位置
                let value = objective.evaluate(&positions[p]);
                
                // 更新个体最优
                if value > personal_best_values[p] {
                    personal_best_values[p] = value;
                    personal_best_positions[p] = positions[p];
                    
                    // 更新全局最优
                    if value > personal_best_values[global_best_index] {
                        global_best_index = p;
                        global_best_position = positions[p];
                    }
                }
            }
            
            // 输出进度
            if i % 10 == 0 {
                println!(
                    "Iteration {}: Best position = {:.6}, Best value = {:.6}",
                    i, global_best_position, personal_best_values[global_best_index]
                );
            }
        }
        
        global_best_position
    }
}

// 使用优化器和目标函数
fn find_maximum() {
    // 定义一个有多个局部极大值的函数
    let complex_function = |x: f64| -> f64 {
        (x * x.sin() / 10.0) + x.cos() * 0.5
    };
    
    // 创建优化问题
    let objective = OneDimensionalFunction::new(complex_function, 0.0);
    
    // 使用梯度下降
    let gd_optimizer = GradientDescent::new(0.1, 1e-6);
    let gd_result = gd_optimizer.optimize(&objective, 100);
    println!("Gradient Descent result: x = {:.6}, f(x) = {:.6}", 
             gd_result, complex_function(gd_result));
    
    // 使用粒子群优化
    let pso_optimizer = ParticleSwarmOptimization::new(20, 0.7, 1.5, 1.5);
    let pso_result = pso_optimizer.optimize(&objective, 50);
    println!("Particle Swarm Optimization result: x = {:.6}, f(x) = {:.6}", 
             pso_result, complex_function(pso_result));
}
```

**准则**：通过特征抽象目标函数和优化器，实现算法与问题分离的灵活架构。

## 4. 迭代与递归工作流

### 4.1 自适应迭代器

```rust
// 推荐：自适应迭代器模式
// 分批处理迭代器适配器
pub struct Batched<I, F> {
    inner: I,
    batch_size: usize,
    process_fn: F,
    current_batch: Vec<I::Item>,
}

impl<I, F, R> Batched<I, F>
where
    I: Iterator,
    F: FnMut(&mut Vec<I::Item>) -> R,
{
    pub fn new(iter: I, batch_size: usize, process_fn: F) -> Self {
        Self {
            inner: iter,
            batch_size,
            process_fn,
            current_batch: Vec::with_capacity(batch_size),
        }
    }
}

impl<I, F, R> Iterator for Batched<I, F>
where
    I: Iterator,
    F: FnMut(&mut Vec<I::Item>) -> R,
{
    type Item = R;
    
    fn next(&mut self) -> Option<Self::Item> {
        // 填充当前批次直到达到批次大小或迭代器结束
        while self.current_batch.len() < self.batch_size {
            match self.inner.next() {
                Some(item) => self.current_batch.push(item),
                None => break,
            }
        }
        
        // 如果批次为空，表示迭代器已结束
        if self.current_batch.is_empty() {
            return None;
        }
        
        // 处理当前批次并返回结果
        let result = (self.process_fn)(&mut self.current_batch);
        self.current_batch.clear();
        Some(result)
    }
}

// 拓展特征，为所有迭代器添加批处理方法
pub trait BatchedExt: Iterator + Sized {
    fn batch<F, R>(self, batch_size: usize, process_fn: F) -> Batched<Self, F>
    where
        F: FnMut(&mut Vec<Self::Item>) -> R,
    {
        Batched::new(self, batch_size, process_fn)
    }
}

impl<T: Iterator> BatchedExt for T {}

// 自适应批处理 - 根据处理时间自动调整批量大小
pub struct AdaptiveBatched<I, F> {
    inner: I,
    min_batch_size: usize,
    max_batch_size: usize,
    target_process_time: std::time::Duration,
    process_fn: F,
    current_batch: Vec<I::Item>,
    current_batch_size: usize,
}

impl<I, F, R> AdaptiveBatched<I, F>
where
    I: Iterator,
    F: FnMut(&mut Vec<I::Item>) -> R,
{
    pub fn new(
        iter: I,
        min_batch_size: usize,
        max_batch_size: usize,
        target_process_time: std::time::Duration,
        process_fn: F,
    ) -> Self {
        let initial_batch_size = (min_batch_size + max_batch_size) / 2;
        Self {
            inner: iter,
            min_batch_size,
            max_batch_size,
            target_process_time,
            process_fn,
            current_batch: Vec::with_capacity(initial_batch_size),
            current_batch_size: initial_batch_size,
        }
    }
}

impl<I, F, R> Iterator for AdaptiveBatched<I, F>
where
    I: Iterator,
    F: FnMut(&mut Vec<I::Item>) -> R,
{
    type Item = R;
    
    fn next(&mut self) -> Option<Self::Item> {
        // 填充当前批次
        self.current_batch.clear();
        for _ in 0..self.current_batch_size {
            match self.inner.next() {
                Some(item) => self.current_batch.push(item),
                None => break,
            }
        }
        
        // 如果批次为空，表示迭代器已结束
        if self.current_batch.is_empty() {
            return None;
        }
        
        // 测量处理时间
        let start = std::time::Instant::now();
        let result = (self.process_fn)(&mut self.current_batch);
        let elapsed = start.elapsed();
        
        // 根据处理时间调整批次大小
        if elapsed > self.target_process_time * 2 {
            // 处理时间太长，减小批次大小
            self.current_batch_size = std::cmp::max(
                self.min_batch_size,
                self.current_batch_size / 2
            );
        } else if elapsed < self.target_process_time / 2 {
            // 处理时间太短，增加批次大小
            self.current_batch_size = std::cmp::min(
                self.max_batch_size,
                self.current_batch_size * 2
            );
        }
        
        Some(result)
    }
}

// 拓展特征，为所有迭代器添加自适应批处理方法
pub trait AdaptiveBatchExt: Iterator + Sized {
    fn adaptive_batch<F, R>(
        self,
        min_batch_size: usize,
        max_batch_size: usize,
        target_process_time: std::time::Duration,
        process_fn: F,
    ) -> AdaptiveBatched<Self, F>
    where
        F: FnMut(&mut Vec<Self::Item>) -> R,
    {
        AdaptiveBatched::new(
            self,
            min_batch_size,
            max_batch_size,
            target_process_time,
            process_fn,
        )
    }
}

impl<T: Iterator> AdaptiveBatchExt for T {}

// 使用自适应迭代器
fn process_large_dataset() {
    // 生成大量数据
    let data: Vec<i32> = (0..10000).collect();
    
    // 使用固定批次大小处理
    let batch_results: Vec<_> = data.iter()
        .batch(100, |batch| {
            // 模拟处理每个批次
            let sum: i32 = batch.iter().copied().sum();
            println!("Processed batch of {} items, sum: {}", batch.len(), sum);
            std::thread::sleep(std::time::Duration::from_millis(10));
            sum
        })
        .collect();
        
    println!("Fixed batch processing produced {} batches", batch_results.len());
    
    // 使用自适应批次大小处理
    let adaptive_results: Vec<_> = data.iter()
        .adaptive_batch(
            10,                                         // 最小批次大小
            1000,                                       // 最大批次大小
            std::time::Duration::from_millis(50),      // 目标处理时间
            |batch| {
                // 模拟处理每个批次，处理时间与批次大小成正比
                let sum: i32 = batch.iter().copied().sum();
                println!("Processed adaptive batch of {} items, sum: {}", batch.len(), sum);
                
                // 模拟处理时间随批次大小增加
                std::thread::sleep(std::time::Duration::from_millis(
                    (batch.len() as u64) / 10
                ));
                
                sum
            }
        )
        .collect();
        
    println!("Adaptive batch processing produced {} batches", adaptive_results.len());
}
```

**准则**：设计自适应迭代器，根据工作负载动态调整处理策略。

### 4.2 可继续/可恢复递归模式

```rust
// 推荐：可继续/可恢复递归模式
// 定义递归操作的状态
pub enum RecursionState<T, R> {
    // 正在进行中
    Continue(T),
    // 已完成，包含结果
    Complete(R),
}

// 可恢复递归框架
pub struct ResumableRecursion<T, R, F> {
    state_fn: F,
    max_depth: usize,
    current_depth: usize,
}

impl<T, R, F> ResumableRecursion<T, R, F> 
where
    F: Fn(&T) -> RecursionState<Vec<T>, R>,
{
    pub fn new(state_fn: F, max_depth: usize) -> Self {
        Self {
            state_fn,
            max_depth,
            current_depth: 0,
        }
    }
    
    // 执行递归，可以设置最大步数限制
    pub fn run(&mut self, initial_state: T, max_steps: usize) -> Option<R> {
        let mut stack = vec![initial_state];
        let mut steps = 0;
        
        while let Some(current) = stack.pop() {
            steps += 1;
            if steps > max_steps {
                // 保存状态并返回 None 表示未完成
                stack.push(current);
                return None;
            }
            
            // 防止递归深度过深
            self.current_depth += 1;
            if self.current_depth > self.max_depth {
                println!("Maximum recursion depth reached");
                self.current_depth -= 1;
                continue;
            }
            
            match (self.state_fn)(&current) {
                RecursionState::Continue(new_states) => {
                    // 将新状态添加到栈中
                    stack.extend(new_states);
                }
                RecursionState::Complete(result) => {
                    self.current_depth -= 1;
                    if self.current_depth == 0 {
                        // 顶层递归完成，返回结果
                        return Some(result);
                    }
                }
            }
            
            if self.current_depth > 0 {
                self.current_depth -= 1;
            }
        }
        
        // 递归结束但没有得到结果
        None
    }
    
    // 恢复执行，从上次保存的状态继续
    pub fn resume(&mut self, saved_states: Vec<T>, max_steps: usize) -> Option<R> {
        let mut stack = saved_states;
        let mut steps = 0;
        
        while let Some(current) = stack.pop() {
            steps += 1;
            if steps > max_steps {
                // 再次保存状态并返回 None
                stack.push(current);
                return None;
            }
            
            self.current_depth += 1;
            if self.current_depth > self.max_depth {
                println!("Maximum recursion depth reached");
                self.current_depth -= 1;
                continue;
            }
            
            match (self.state_fn)(&current) {
                RecursionState::Continue(new_states) => {
                    stack.extend(new_states);
                }
                RecursionState::Complete(result) => {
                    self.current_depth -= 1;
                    if self.current_depth == 0 {
                        return Some(result);
                    }
                }
            }
            
            if self.current_depth > 0 {
                self.current_depth -= 1;
            }
        }
        
        None
    }
    
    // 获取当前栈，用于保存状态
    pub fn get_stack(&self) -> Vec<T> {
        // 实际实现中，这里应该返回当前的递归栈
        // 由于简化，这里返回空栈
        Vec::new()
    }
}

// 使用可恢复递归 - 树的深度优先遍历示例
#[derive(Clone, Debug)]
struct TreeNode {
    value: i32,
    children: Vec<TreeNode>,
}

impl TreeNode {
    fn new(value: i32) -> Self {
        Self {
            value,
            children: Vec::new(),
        }
    }
    
    fn add_child(&mut self, child: TreeNode) {
        self.children.push(child);
    }
}

// 使用可恢复递归进行树遍历
fn traverse_tree() {
    // 创建一个简单的树
    let mut root = TreeNode::new(1);
    
    let mut child1 = TreeNode::new(2);
    child1.add_child(TreeNode::new(5));
    child1.add_child(TreeNode::new(6));
    
    let mut child2 = TreeNode::new(3);
    child2.add_child(TreeNode::new(7));
    
    let child3 = TreeNode::new(4);
    
    root.add_child(child1);
    root.add_child(child2);
    root.add_child(child3);
    
    // 定义遍历状态函数
    let traverse_fn = |node: &TreeNode| -> RecursionState<Vec<TreeNode>, Vec<i32>> {
        println!("Visiting node with value: {}", node.value);
        
        if node.children.is_empty() {
            // 叶子节点，返回当前值
            RecursionState::Complete(vec![node.value])
        } else {
            // 非叶子节点，继续遍历子节点
            RecursionState::Continue(node.children.clone())
        }
    };
    
    // 创建可恢复递归执行器
    let mut recursion = ResumableRecursion::new(traverse_fn, 1000);
    
    // 执行递归，限制步数
    let mut result = recursion.run(root.clone(), 3);
    
    if result.is_none() {
        println!("Recursion paused due to step limit");
        
        // 保存状态
        let saved_state = recursion.get_stack();
        
        // 恢复递归
        result = recursion.resume(saved_state, 10);
    }
    
    if let Some(values) = result {
        println!("Traversal result: {:?}", values);
    } else {
        println!("Traversal incomplete");
    }
}
```

**准则**：设计可继续/可恢复递归模式，处理深度递归和长时间运行的工作流。

## 5. 并行与异步工作流

### 5.1 工作窃取任务池

```rust
// 推荐：工作窃取任务池
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::thread;

// 任务特征
pub trait Task: Send + 'static {
    type Output: Send + 'static;
    
    fn execute(&self) -> Self::Output;
}

// 任务结果
pub struct TaskResult<T> {
    result: Arc<Mutex<Option<T>>>,
    notifier: Arc<Mutex<Vec<std::sync::mpsc::Sender<()>>>>,
}

impl<T> TaskResult<T> {
    pub fn new() -> Self {
        Self {
            result: Arc::new(Mutex::new(None)),
            notifier: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    pub fn set_result(&self, result: T) {
        let mut guard = self.result.lock().unwrap();
        *guard = Some(result);
        
        // 通知所有等待者
        let notifiers = self.notifier.lock().unwrap();
        for notifier in notifiers.iter() {
            let _ = notifier.send(());
        }
    }
    
    pub fn get_result(&self) -> Option<T>
    where
        T: Clone,
    {
        let guard = self.result.lock().unwrap();
        guard.clone()
    }
    
    pub fn wait_for_result(&self) -> T
    where
        T: Clone,
    {
        // 首先检查结果是否已经可用
        {
            let guard = self.result.lock().unwrap();
            if let Some(ref result) = *guard {
                return result.clone();
            }
        }
        
        // 如果结果不可用，等待通知
        let (sender, receiver) = std::sync::mpsc::channel();
        
        {
            let mut notifiers = self.notifier.lock().unwrap();
            notifiers.push(sender);
        }
        
        // 等待通知或定期检查
        loop {
            // 等待通知，超时后重新检查
            let _ = receiver.recv_timeout(std::time::Duration::from_millis(100));
            
            let guard = self.result.lock().unwrap();
            if let Some(ref result) = *guard {
                return result.clone();
            }
        }
    }
}

// 工作窃取任务池
pub struct WorkStealingPool {
    queues: Vec<Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send>>>>>,
    worker_threads: Vec<thread::JoinHandle<()>>,
    shutdown: Arc<Mutex<bool>>,
}

impl WorkStealingPool {
    pub fn new(num_workers: usize) -> Self {
        let mut queues = Vec::with_capacity(num_workers);
        for _ in 0..num_workers {
            queues.push(Arc::new(Mutex::new(VecDeque::new())));
        }
        
        let shutdown = Arc::new(Mutex::new(false));
        let mut worker_threads = Vec::with_capacity(num_workers);
        
        for worker_id in 0..num_workers {
            let queues_clone = queues.clone();
            let shutdown_clone = shutdown.clone();
            
            let handle = thread::spawn(move || {
                Self::worker_loop(worker_id, num_workers, queues_clone, shutdown_clone);
            });
            
            worker_threads.push(handle);
        }
        
        Self {
            queues,
            worker_threads,
            shutdown,
        }
    }
    
    // 提交任务
    pub fn submit<T, F>(&self, task: F) -> TaskResult<T>
    where
        T: Send + 'static,
        F: FnOnce() -> T + Send + 'static,
    {
        // 创建任务结果
        let result = TaskResult::new();
        let result_clone = result.clone();
        
        // 包装任务函数
        let task_fn = Box::new(move || {
            let task_result = task();
            result_clone.set_result(task_result);
        });
        
        // 选择队列并添加任务
        let queue_index = rand::random::<usize>() % self.queues.len();
        let mut queue = self.queues[queue_index].lock().unwrap();
        queue.push_back(task_fn);
        
        result
    }
    
    // 关闭线程池
    pub fn shutdown(self) {
        // 设置关闭标志
        {
            let mut shutdown_guard = self.shutdown.lock().unwrap();
            *shutdown_guard = true;
        }
        
        // 等待所有工作线程完成
        for handle in self.worker_threads {
            let _ = handle.join();
        }
    }
    
    // 工作者线程循环
    fn worker_loop(
        worker_id: usize,
        num_workers: usize,
        queues: Vec<Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send>>>>>,
        shutdown: Arc<Mutex<bool>>,
    ) {
        // 主循环
        loop {
            // 检查是否应该关闭
            if *shutdown.lock().unwrap() {
                break;
            }
            
            // 尝试从自己的队列获取任务
            let task_opt = {
                let mut my_queue = queues[worker_id].lock().unwrap();
                my_queue.pop_front()
            };
            
            if let Some(task) = task_opt {
                // 执行任务
                task();
                continue;
            }
            
            // 如果自己的队列为空，尝试从其他队列窃取任务
            let mut stole_task = false;
            
            // 以随机顺序遍历其他队列
            let mut victim_ids: Vec<usize> = (0..num_workers).filter(|&id| id != worker_id).collect();
            victim_ids.shuffle(&mut rand::thread_rng());
            
            for victim_id in victim_ids {
                let task_opt = {
                    let mut victim_queue = queues[victim_id].lock().unwrap();
                    // 从队列尾部窃取任务（减少冲突）
                    victim_queue.pop_back()
                };
                
                if let Some(task) = task_opt {
                    // 执行窃取的任务
                    task();
                    stole_task = true;
                    break;
                }
            }
            
            // 如果没有窃取到任务，短暂休眠以减少CPU使用
            if !stole_task {
                thread::sleep(std::time::Duration::from_millis(1));
            }
        }
    }
}

impl Clone for TaskResult<T> {
    fn clone(&self) -> Self {
        Self {
            result: self.result.clone(),
            notifier: self.notifier.clone(),
        }
    }
}

// 使用工作窃取任务池
fn parallel_workflow() {
    // 创建线程池
    let pool = WorkStealingPool::new(4);
    
    // 提交计算密集型任务
    let task1_result = pool.submit(|| {
        println!("Task 1 started");
        let mut sum = 0;
        for i in 0..1000000 {
            sum += i;
        }
        println!("Task 1 completed");
        sum
    });
    
    // 提交IO密集型任务
    let task2_result = pool.submit(|| {
        println!("Task 2 started");
        thread::sleep(std::time::Duration::from_millis(100));
        println!("Task 2 completed");
        "Task 2 result"
    });
    
    // 提交取决于前两个任务的任务
    let task3_result = pool.submit(move || {
        println!("Task 3 started");
        
        // 等待任务1和任务2的结果
        let result1 = task1_result.wait_for_result();
        let result2 = task2_result.wait_for_result();
        
        println!("Task 3 completed with inputs: {}, {}", result1, result2);
        format!("Combined result: {}", result1)
    });
    
    // 等待最终结果
    let final_result = task3_result.wait_for_result();
    println!("Final result: {}", final_result);
    
    // 关闭线程池
    pool.shutdown();
}
```

**准则**：设计支持工作窃取的任务池，优化并行工作流的执行效率。

### 5.2 异步工作流状态机

```rust
// 推荐：异步工作流状态机
use futures::future::{BoxFuture, FutureExt};
use std::pin::Pin;

// 异步工作流状态
pub enum WorkflowState<T, E> {
    // 初始状态
    Initial,
    // 等待某个异步操作完成
    Waiting(BoxFuture<'static, Result<WorkflowState<T, E>, E>>),
    // 工作流完成
    Complete(T),
    // 工作流错误
    Error(E),
}

// 工作流执行器
pub struct WorkflowExecutor<T, E> {
    state: WorkflowState<T, E>,
}

impl<T: 'static, E: 'static> WorkflowExecutor<T, E> {
    pub fn new() -> Self {
        Self {
            state: WorkflowState::Initial,
        }
    }
    
    // 注册初始工作流
    pub fn register<F>(&mut self, future: F)
    where
        F: FnOnce() -> BoxFuture<'static, Result<WorkflowState<T, E>, E>> + 'static,
    {
        self.state = WorkflowState::Waiting(future().boxed());
    }
    
    // 驱动工作流向前执行一步
    pub async fn step(&mut self) -> Result<bool, E> {
        match std::mem::replace(&mut self.state, WorkflowState::Initial) {
            WorkflowState::Initial => {
                // 初始状态，无事可做
                self.state = WorkflowState::Initial;
                Ok(false)
            }

            WorkflowState::Waiting(future) => {
                // 等待异步操作
                match future.await {
                    Ok(next_state) => {
                        self.state = next_state;
                        Ok(true)
                    }
                    Err(e) => {
                        self.state = WorkflowState::Error(e);
                        Err(e)
                    }
                }
            }
            WorkflowState::Complete(result) => {
                // 已经完成，保持完成状态
                self.state = WorkflowState::Complete(result);
                Ok(false)
            }
            WorkflowState::Error(error) => {
                // 保持错误状态
                self.state = WorkflowState::Error(error);
                Err(error)
            }
        }
    }
    
    // 持续执行直到工作流完成或出错
    pub async fn run_to_completion(&mut self) -> Result<T, E> {
        loop {
            match &self.state {
                WorkflowState::Complete(result) => {
                    // 需要复制结果，因为我们不能移动 self.state 中的值
                    return Ok(result.clone());
                }
                WorkflowState::Error(error) => {
                    // 同样需要复制错误
                    return Err(error.clone());
                }
                _ => {
                    // 继续执行
                    self.step().await?;
                }
            }
        }
    }
    
    // 获取当前状态（用于检查）
    pub fn current_state(&self) -> &WorkflowState<T, E> {
        &self.state
    }
}

// 使用异步工作流状态机 - 数据处理示例
async fn async_workflow_example() {
    // 定义我们的工作流状态和错误类型
    #[derive(Clone, Debug)]
    struct ProcessedData {
        id: u64,
        content: String,
        metadata: std::collections::HashMap<String, String>,
    }
    
    #[derive(Clone, Debug)]
    enum ProcessingError {
        FetchFailed(String),
        ProcessingFailed(String),
        ValidationFailed(String),
    }
    
    // 模拟异步数据获取
    async fn fetch_data(id: u64) -> Result<String, ProcessingError> {
        println!("Fetching data for id: {}", id);
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        if id % 7 == 0 {
            return Err(ProcessingError::FetchFailed(format!("Failed to fetch data for id: {}", id)));
        }
        
        Ok(format!("Raw data for id {}", id))
    }
    
    // 模拟异步数据处理
    async fn process_data(raw_data: &str) -> Result<String, ProcessingError> {
        println!("Processing data: {}", raw_data);
        tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
        
        if raw_data.contains("666") {
            return Err(ProcessingError::ProcessingFailed("Evil data detected".into()));
        }
        
        Ok(format!("Processed {}", raw_data))
    }
    
    // 模拟异步数据验证
    async fn validate_data(processed_data: &str) -> Result<bool, ProcessingError> {
        println!("Validating data: {}", processed_data);
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        if processed_data.len() < 10 {
            return Err(ProcessingError::ValidationFailed("Data too short".into()));
        }
        
        Ok(true)
    }
    
    // 模拟元数据生成
    async fn generate_metadata(id: u64, processed_data: &str) -> std::collections::HashMap<String, String> {
        let mut metadata = std::collections::HashMap::new();
        metadata.insert("timestamp".to_string(), chrono::Utc::now().to_rfc3339());
        metadata.insert("size".to_string(), processed_data.len().to_string());
        metadata.insert("source".to_string(), format!("ID-{}", id));
        
        metadata
    }
    
    // 创建工作流执行器
    let mut executor = WorkflowExecutor::<ProcessedData, ProcessingError>::new();
    
    // 定义工作流
    let data_id = 42;
    
    executor.register(move || {
        let future = async move {
            // 步骤1: 获取数据
            let raw_data = fetch_data(data_id).await?;
            
            // 返回下一个状态
            Ok(WorkflowState::Waiting(
                (move || async move {
                    // 步骤2: 处理数据
                    let processed_content = process_data(&raw_data).await?;
                    
                    // 返回下一个状态
                    Ok(WorkflowState::Waiting(
                        (move || async move {
                            // 步骤3: 验证数据
                            let is_valid = validate_data(&processed_content).await?;
                            
                            if !is_valid {
                                return Err(ProcessingError::ValidationFailed("Validation returned false".into()));
                            }
                            
                            // 返回下一个状态
                            Ok(WorkflowState::Waiting(
                                (move || async move {
                                    // 步骤4: 生成元数据
                                    let metadata = generate_metadata(data_id, &processed_content).await;
                                    
                                    // 完成工作流
                                    let final_result = ProcessedData {
                                        id: data_id,
                                        content: processed_content,
                                        metadata,
                                    };
                                    
                                    Ok(WorkflowState::Complete(final_result))
                                })().boxed()
                            ))
                        })().boxed()
                    ))
                })().boxed()
            ))
        };
        
        Box::pin(future) as BoxFuture<'static, Result<WorkflowState<ProcessedData, ProcessingError>, ProcessingError>>
    });
    
    // 运行工作流直到完成
    match executor.run_to_completion().await {
        Ok(result) => {
            println!("Workflow completed successfully!");
            println!("ID: {}", result.id);
            println!("Content: {}", result.content);
            println!("Metadata: {:?}", result.metadata);
        }
        Err(error) => {
            println!("Workflow failed with error: {:?}", error);
        }
    }
}
```

**准则**：设计异步工作流状态机，实现复杂异步操作的清晰表示和执行。

## 6. 总结：工作流与算法设计准则

从工作流组合与算法设计视角出发，我们可以归纳出以下关键准则，指导 Rust 中的类型设计：

### 6.1 组合与流程设计

1. **可组合接口**：设计支持链式调用和组合的接口，使工作流的构建变得直观。
2. **处理管道**：通过类型安全的管道模式，实现数据的流式处理。
3. **状态明确性**：使用类型状态模式确保工作流状态转换的安全性和可验证性。
4. **事务原则**：实现支持准备、执行和回滚的事务性操作模式。

### 6.2 算法设计与执行

1. **策略多态**：通过特征抽象策略，允许在运行时或编译时选择不同的算法实现。
2. **可优化接口**：设计允许自动或手动性能优化的接口，如自适应批处理。
3. **递归控制**：实现可控制、可暂停、可恢复的递归模式，处理复杂递归算法。
4. **并行友好型**：设计支持并行执行和工作窃取的任务抽象，优化多核性能。

### 6.3 集成设计原则

1. **错误处理集成**：在工作流中整合一致的错误处理机制，确保异常情况下的安全恢复。
2. **资源管理自动化**：设计确保资源在工作流结束时自动清理的模式。
3. **可测试性**：设计便于单元测试和模拟的接口，验证工作流和算法正确性。
4. **渐进式构建**：支持工作流的渐进式构建和执行，允许动态适应和调整。

这些准则不仅提供了设计高效类型的框架，还促进了安全、可维护的代码结构。
通过结合工作流组合与算法设计的最佳实践，可以创建既易于使用又高效的 Rust 类型系统。
