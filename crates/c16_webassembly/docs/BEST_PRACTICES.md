# WebAssembly 2.0 + Rust 1.90 最佳实践指南

## 📚 概述

本文档提供了使用 WebAssembly 2.0 + Rust 1.90 集成项目的最佳实践指南。通过遵循这些实践，您可以充分发挥项目的性能优势，避免常见问题，并构建高质量的 WebAssembly 应用程序。

## 🎯 设计原则

### 1. 性能优先

- **批量处理**: 尽可能批量处理数据以提高效率
- **内存优化**: 优化内存使用模式和访问模式
- **SIMD 利用**: 充分利用 SIMD 指令进行并行计算
- **缓存友好**: 设计缓存友好的数据结构和算法

### 2. 类型安全

- **强类型**: 使用强类型系统避免运行时错误
- **类型验证**: 在关键点进行类型验证
- **安全转换**: 使用安全的类型转换方法
- **错误处理**: 实现完善的错误处理机制

### 3. 可维护性

- **模块化设计**: 将功能分解为独立的模块
- **清晰接口**: 设计清晰、简洁的 API 接口
- **文档完善**: 提供完整的代码文档和示例
- **测试覆盖**: 确保充分的测试覆盖

## 🏗️ 架构设计

### 1. 模块化架构

```rust
// 推荐的模块结构
pub mod core {
    pub mod types;      // 核心类型定义
    pub mod runtime;    // 运行时系统
    pub mod memory;     // 内存管理
}

pub mod features {
    pub mod webassembly_2_0;  // WebAssembly 2.0 特性
    pub mod rust_1_90;        // Rust 1.90 特性
}

pub mod utils {
    pub mod performance;  // 性能工具
    pub mod security;     // 安全工具
    pub mod debugging;    // 调试工具
}
```

### 2. 分层设计

```text
应用层 (Application Layer)
    ↓
业务逻辑层 (Business Logic Layer)
    ↓
WebAssembly 运行时层 (Runtime Layer)
    ↓
系统层 (System Layer)
```

### 3. 接口设计

```rust
// 推荐的接口设计模式
pub trait WebAssemblyRuntime {
    fn load_module(&mut self, module: Module) -> Result<(), RuntimeError>;
    fn execute_function(&mut self, name: &str, args: Vec<Value>) -> Result<Value, RuntimeError>;
    fn get_statistics(&self) -> RuntimeStatistics;
}

pub trait MemoryManager {
    fn allocate(&mut self, size: usize) -> Result<MemoryHandle, MemoryError>;
    fn deallocate(&mut self, handle: MemoryHandle) -> Result<(), MemoryError>;
    fn bulk_copy(&mut self, dst: u32, src: u32, size: u32) -> Result<(), MemoryError>;
}
```

## 🚀 性能优化

### 1. 内存优化

#### 批量内存操作

```rust
// ✅ 推荐: 使用批量操作
let mut manager = BulkMemoryManager::new(1024);
manager.bulk_copy(0, 100, 50)?;
manager.bulk_fill(200, 0xFF, 25)?;

// ❌ 避免: 逐个操作
for i in 0..50 {
    manager.write_memory(100 + i, &[data[i]])?;
}
```

#### 内存池使用

```rust
// ✅ 推荐: 使用内存池
pub struct MemoryPool {
    pool: Vec<Vec<u8>>,
    free_indices: Vec<usize>,
}

impl MemoryPool {
    pub fn allocate(&mut self, size: usize) -> Result<usize, MemoryError> {
        if let Some(index) = self.free_indices.pop() {
            self.pool[index].resize(size, 0);
            Ok(index)
        } else {
            self.pool.push(vec![0; size]);
            Ok(self.pool.len() - 1)
        }
    }
}
```

#### 数据对齐

```rust
// ✅ 推荐: 确保数据对齐
#[repr(align(16))]
pub struct AlignedData {
    pub data: [u8; 16],
}

// ✅ 推荐: 使用 SIMD 友好的数据结构
pub struct SimdVector {
    pub data: [u8; 16],  // 16 字节对齐
}
```

### 2. SIMD 优化

#### 向量化循环

```rust
// ✅ 推荐: 使用 SIMD 处理向量数据
fn process_vector_simd(data: &[f32]) -> Vec<f32> {
    let mut result = Vec::with_capacity(data.len());
    let mut processor = SimdProcessor::new();
    
    for chunk in data.chunks(4) {
        if chunk.len() == 4 {
            let operands = [
                Value::V128(chunk_to_v128(chunk)),
                Value::V128([1.0; 16])  // 常量
            ];
            let simd_result = processor.execute_simd(SimdInstruction::V128Mul, operands)?;
            result.extend_from_slice(&v128_to_chunk(simd_result));
        }
    }
    
    result
}
```

#### 并行处理

```rust
// ✅ 推荐: 利用 SIMD 并行处理
fn parallel_simd_processing(data: &[u8]) -> Result<Vec<u8>, RuntimeError> {
    let mut processor = SimdProcessor::new();
    let mut result = Vec::with_capacity(data.len());
    
    for chunk in data.chunks(16) {
        if chunk.len() == 16 {
            let operands = [
                Value::V128(*chunk),
                Value::V128([0xFF; 16])
            ];
            let processed = processor.execute_simd(SimdInstruction::V128And, operands)?;
            result.extend_from_slice(&processed.as_v128().unwrap());
        }
    }
    
    Ok(result)
}
```

### 3. 尾调用优化

#### 递归函数优化

```rust
// ✅ 推荐: 使用尾调用优化
fn factorial_tail_call(n: u64, acc: u64) -> u64 {
    if n <= 1 {
        acc
    } else {
        factorial_tail_call(n - 1, n * acc)  // 尾调用
    }
}

// ❌ 避免: 非尾调用递归
fn factorial_normal(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial_normal(n - 1)  // 非尾调用
    }
}
```

#### 尾调用优化器使用

```rust
// ✅ 推荐: 使用尾调用优化器
fn optimized_recursion() -> Result<Value, RuntimeError> {
    let mut optimizer = TailCallOptimizer::new();
    let args = vec![Value::I32(1000), Value::I32(1)];
    optimizer.execute_tail_call(0, args)
}
```

### 4. 宿主绑定优化

#### JavaScript 函数调用

```rust
// ✅ 推荐: 批量调用 JavaScript 函数
fn batch_javascript_calls() -> Result<(), RuntimeError> {
    let mut manager = HostBindingManager::new();
    
    // 注册函数
    for i in 0..100 {
        manager.register_binding(
            format!("func_{}", i),
            HostBindingType::JavaScriptFunction,
            "batch_process".to_string(),
        );
    }
    
    // 批量调用
    for i in 0..100 {
        let args = vec![Value::I32(i)];
        manager.call_javascript_function(&format!("func_{}", i), args)?;
    }
    
    Ok(())
}
```

#### DOM 操作优化

```rust
// ✅ 推荐: 批量 DOM 操作
fn batch_dom_operations() -> Result<(), RuntimeError> {
    let mut manager = HostBindingManager::new();
    
    // 批量设置属性
    for i in 0..1000 {
        let args = vec![
            Value::I32(i),
            Value::String(format!("value_{}", i))
        ];
        manager.call_dom_method("element", "setAttribute", args)?;
    }
    
    Ok(())
}
```

## 🛡️ 安全实践

### 1. 内存安全

#### 边界检查

```rust
// ✅ 推荐: 始终进行边界检查
pub fn safe_memory_access(memory: &[u8], offset: usize, len: usize) -> Result<&[u8], MemoryError> {
    if offset + len > memory.len() {
        return Err(MemoryError::OutOfBounds);
    }
    Ok(&memory[offset..offset + len])
}
```

#### 内存隔离

```rust
// ✅ 推荐: 使用内存隔离
pub struct IsolatedMemory {
    memory: Vec<u8>,
    bounds: MemoryBounds,
}

impl IsolatedMemory {
    pub fn new(size: usize) -> Self {
        Self {
            memory: vec![0; size],
            bounds: MemoryBounds::new(0, size),
        }
    }
    
    pub fn access(&self, offset: usize, len: usize) -> Result<&[u8], MemoryError> {
        self.bounds.check_access(offset, len)?;
        Ok(&self.memory[offset..offset + len])
    }
}
```

### 2. 类型安全1

#### 类型验证

```rust
// ✅ 推荐: 在关键点进行类型验证
pub fn safe_type_conversion(value: Value, target_type: ValueType) -> Result<Value, TypeError> {
    match (&value, target_type) {
        (Value::I32(_), ValueType::I32) => Ok(value),
        (Value::I32(v), ValueType::F32) => Ok(Value::F32(*v as f32)),
        (Value::F32(v), ValueType::I32) => Ok(Value::I32(*v as i32)),
        _ => Err(TypeError::IncompatibleTypes),
    }
}
```

#### 安全转换

```rust
// ✅ 推荐: 使用安全的转换方法
pub fn safe_i128_operation(a: i128, b: i128) -> Result<i128, ArithmeticError> {
    a.checked_add(b).ok_or(ArithmeticError::Overflow)
}
```

### 3. 错误处理

#### 错误类型设计

```rust
// ✅ 推荐: 设计完善的错误类型
#[derive(Error, Debug)]
pub enum WebAssemblyError {
    #[error("内存错误: {0}")]
    MemoryError(#[from] MemoryError),
    
    #[error("类型错误: {0}")]
    TypeError(#[from] TypeError),
    
    #[error("运行时错误: {0}")]
    RuntimeError(#[from] RuntimeError),
    
    #[error("验证错误: {0}")]
    ValidationError(#[from] ValidationError),
}
```

#### 错误恢复

```rust
// ✅ 推荐: 实现错误恢复机制
pub fn resilient_operation() -> Result<Value, WebAssemblyError> {
    // 尝试主要操作
    match primary_operation() {
        Ok(result) => Ok(result),
        Err(e) => {
            // 记录错误
            log::error!("主要操作失败: {}", e);
            
            // 尝试备用操作
            match fallback_operation() {
                Ok(result) => {
                    log::info!("备用操作成功");
                    Ok(result)
                }
                Err(e2) => {
                    log::error!("备用操作也失败: {}", e2);
                    Err(e2.into())
                }
            }
        }
    }
}
```

## 🧪 测试实践

### 1. 单元测试

#### 测试结构

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_memory_operations() {
        let mut manager = BulkMemoryManager::new(1024);
        
        // 测试写入
        let data = b"test data";
        assert!(manager.write_memory(0, data).is_ok());
        
        // 测试读取
        let result = manager.read_memory(0, data.len() as u32).unwrap();
        assert_eq!(result, data);
    }
    
    #[test]
    fn test_simd_operations() {
        let mut processor = SimdProcessor::new();
        let operands = [
            Value::V128([1; 16]),
            Value::V128([2; 16])
        ];
        
        let result = processor.execute_simd(SimdInstruction::V128Add, operands).unwrap();
        assert_eq!(result.as_v128().unwrap(), [3; 16]);
    }
}
```

#### 测试数据

```rust
// ✅ 推荐: 使用测试数据生成器
pub fn generate_test_data(size: usize) -> Vec<u8> {
    (0..size).map(|i| (i % 256) as u8).collect()
}

pub fn generate_test_matrix(size: usize) -> Vec<Vec<f64>> {
    (0..size).map(|i| {
        (0..size).map(|j| (i + j) as f64).collect()
    }).collect()
}
```

### 2. 集成测试

#### 端到端测试

```rust
#[test]
fn test_end_to_end_workflow() {
    // 创建运行时
    let mut runtime = WebAssemblyRuntime::new();
    
    // 加载模块
    let module = create_test_module();
    runtime.load_module("test".to_string(), module).unwrap();
    
    // 执行函数
    let result = runtime.execute_function("test", "main", vec![]).unwrap();
    
    // 验证结果
    assert_eq!(result, Value::I32(42));
}
```

#### 性能测试

```rust
#[test]
fn test_performance_benchmarks() {
    let iterations = 1000;
    let start = std::time::Instant::now();
    
    for _ in 0..iterations {
        let mut manager = BulkMemoryManager::new(1024);
        manager.bulk_copy(0, 100, 50).unwrap();
    }
    
    let duration = start.elapsed();
    let ops_per_second = iterations as f64 / duration.as_secs_f64();
    
    // 验证性能要求
    assert!(ops_per_second > 1000.0, "性能不达标: {} ops/s", ops_per_second);
}
```

### 3. 基准测试

#### 基准测试结构

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_memory_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_operations");
    
    group.bench_function("bulk_copy", |b| {
        b.iter(|| {
            let mut manager = BulkMemoryManager::new(1024);
            manager.bulk_copy(0, 100, 50).unwrap();
            black_box(manager);
        })
    });
    
    group.finish();
}

criterion_group!(benches, bench_memory_operations);
criterion_main!(benches);
```

## 📚 文档实践

### 1. 代码文档

#### 函数文档

```rust
/// 执行批量内存复制操作
/// 
/// # 参数
/// * `dst` - 目标内存地址
/// * `src` - 源内存地址  
/// * `size` - 复制大小（字节）
/// 
/// # 返回值
/// 成功时返回 `Ok(())`，失败时返回 `Err(RuntimeError)`
/// 
/// # 示例
/// ```rust
/// let mut manager = BulkMemoryManager::new(1024);
/// manager.bulk_copy(0, 100, 50)?;
/// ```
/// 
/// # 性能
/// 此操作的时间复杂度为 O(n)，其中 n 是复制的大小。
/// 对于大块内存，建议使用此方法而不是逐个字节复制。
pub fn bulk_copy(&mut self, dst: u32, src: u32, size: u32) -> Result<(), RuntimeError> {
    // 实现...
}
```

#### 结构体文档

```rust
/// WebAssembly 2.0 运行时环境
/// 
/// 此结构体提供了完整的 WebAssembly 2.0 运行时功能，包括：
/// - 模块加载和执行
/// - 内存管理
/// - 函数调用
/// - 宿主绑定
/// - SIMD 操作
/// 
/// # 示例
/// ```rust
/// let mut runtime = WebAssemblyRuntime::new();
/// let module = Module::new("test_module");
/// runtime.load_module("test".to_string(), module)?;
/// let result = runtime.execute_function("test", "main", vec![])?;
/// ```
pub struct WebAssemblyRuntime {
    // 字段...
}
```

### 2. API 文档

#### 使用示例

```rust
//! # WebAssembly 2.0 + Rust 1.90 使用示例
//! 
//! 本模块提供了完整的使用示例，展示如何使用 WebAssembly 2.0 和 Rust 1.90 的新特性。
//! 
//! ## 基本使用
//! 
//! ```rust
//! use c16_webassembly::*;
//! 
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let mut runtime = WebAssemblyRuntime::new();
//!     // ... 使用运行时
//!     Ok(())
//! }
//! ```
//! 
//! ## 高级特性
//! 
//! ### SIMD 操作
//! ```rust
//! let mut processor = SimdProcessor::new();
//! let result = processor.execute_simd(SimdInstruction::V128Add, operands)?;
//! ```
//! 
//! ### 批量内存操作
//! ```rust
//! let mut manager = BulkMemoryManager::new(1024);
//! manager.bulk_copy(0, 100, 50)?;
//! ```
```

## 🔧 调试实践

### 1. 日志记录

#### 结构化日志

```rust
use log::{info, warn, error, debug};

pub fn process_data(data: &[u8]) -> Result<Vec<u8>, ProcessingError> {
    info!("开始处理数据，大小: {} 字节", data.len());
    
    let start = std::time::Instant::now();
    
    match process_internal(data) {
        Ok(result) => {
            let duration = start.elapsed();
            info!("数据处理完成，耗时: {:?}", duration);
            Ok(result)
        }
        Err(e) => {
            error!("数据处理失败: {}", e);
            Err(e)
        }
    }
}
```

#### 性能日志

```rust
pub fn benchmark_operation<F>(name: &str, operation: F) -> Result<(), BenchmarkError>
where
    F: Fn() -> Result<(), BenchmarkError>,
{
    let start = std::time::Instant::now();
    
    match operation() {
        Ok(()) => {
            let duration = start.elapsed();
            info!("基准测试 '{}' 完成，耗时: {:?}", name, duration);
            Ok(())
        }
        Err(e) => {
            error!("基准测试 '{}' 失败: {}", name, e);
            Err(e)
        }
    }
}
```

### 2. 错误追踪

#### 错误上下文

```rust
use anyhow::{Context, Result};

pub fn complex_operation() -> Result<()> {
    let data = load_data()
        .context("加载数据失败")?;
    
    let processed = process_data(&data)
        .context("处理数据失败")?;
    
    save_result(&processed)
        .context("保存结果失败")?;
    
    Ok(())
}
```

#### 堆栈追踪

```rust
use std::backtrace::Backtrace;

#[derive(Debug, thiserror::Error)]
pub enum DetailedError {
    #[error("操作失败: {message}")]
    OperationFailed {
        message: String,
        backtrace: Backtrace,
    },
}

impl DetailedError {
    pub fn new(message: String) -> Self {
        Self::OperationFailed {
            message,
            backtrace: Backtrace::capture(),
        }
    }
}
```

## 🚀 部署实践

### 1. 构建优化

#### 发布配置

```toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"
strip = true
```

#### 特性选择

```toml
[features]
default = ["std", "simd", "bulk-memory"]
std = []
no_std = []
simd = []
bulk-memory = []
tail-calls = []
host-bindings = []
interface-types = []
```

### 2. 运行时配置

#### 内存配置

```rust
pub struct RuntimeConfig {
    pub initial_memory_size: usize,
    pub max_memory_size: usize,
    pub stack_size: usize,
    pub enable_simd: bool,
    pub enable_bulk_memory: bool,
}

impl Default for RuntimeConfig {
    fn default() -> Self {
        Self {
            initial_memory_size: 1024 * 1024,  // 1MB
            max_memory_size: 16 * 1024 * 1024, // 16MB
            stack_size: 64 * 1024,             // 64KB
            enable_simd: true,
            enable_bulk_memory: true,
        }
    }
}
```

#### 性能监控

```rust
pub struct PerformanceMonitor {
    pub operation_count: AtomicUsize,
    pub total_time: AtomicU64,
    pub memory_usage: AtomicUsize,
}

impl PerformanceMonitor {
    pub fn record_operation(&self, duration: std::time::Duration) {
        self.operation_count.fetch_add(1, Ordering::Relaxed);
        self.total_time.fetch_add(duration.as_nanos() as u64, Ordering::Relaxed);
    }
    
    pub fn get_average_time(&self) -> Option<std::time::Duration> {
        let count = self.operation_count.load(Ordering::Relaxed);
        if count > 0 {
            let total = self.total_time.load(Ordering::Relaxed);
            Some(std::time::Duration::from_nanos(total / count as u64))
        } else {
            None
        }
    }
}
```

## 📋 检查清单

### 开发前检查

- [ ] 明确性能要求和目标
- [ ] 设计清晰的架构和接口
- [ ] 选择合适的算法和数据结构
- [ ] 规划测试策略和覆盖范围

### 开发中检查

- [ ] 遵循编码规范和最佳实践
- [ ] 实现完善的错误处理
- [ ] 添加适当的日志记录
- [ ] 编写单元测试和集成测试
- [ ] 进行性能测试和优化

### 发布前检查

- [ ] 所有测试通过
- [ ] 性能指标达标
- [ ] 文档完整准确
- [ ] 安全审查通过
- [ ] 兼容性测试通过

### 部署后检查

- [ ] 监控运行时性能
- [ ] 收集用户反馈
- [ ] 分析错误日志
- [ ] 持续优化改进

---

**注意**: 这些最佳实践是基于当前的技术状态和项目经验总结的。随着技术的发展和项目的发展，这些实践可能会有所调整和更新。
