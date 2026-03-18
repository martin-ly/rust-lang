# 故障排除与调试指南

## 概述

本指南提供Rust安全关键系统开发中常见问题的诊断和解决方法，涵盖编译错误、运行时问题、工具链问题和认证相关问题。

---

## 1. 编译错误故障排除

### 1.1 借用检查器错误

#### 错误 E0499: 多次可变借用

```rust
// ❌ 错误代码
fn process_data(data: &mut Vec<u32>) {
    let ref1 = &mut data[0];
    let ref2 = &mut data[1];  // 错误: 第二次可变借用
    *ref1 += 1;
    *ref2 += 1;
}

// ✅ 解决方案1: 缩小借用范围
fn process_data_fixed(data: &mut Vec<u32>) {
    {
        let ref1 = &mut data[0];
        *ref1 += 1;
    }  // ref1在这里结束
    {
        let ref2 = &mut data[1];
        *ref2 += 1;
    }
}

// ✅ 解决方案2: 使用split_at_mut
fn process_data_split(data: &mut Vec<u32>) {
    let (first, rest) = data.split_at_mut(1);
    let ref1 = &mut first[0];
    let ref2 = &mut rest[0];
    *ref1 += 1;
    *ref2 += 1;
}

// ✅ 解决方案3: 使用索引
fn process_data_index(data: &mut Vec<u32>) {
    data[0] += 1;
    data[1] += 1;
}
```

#### 错误 E0597: 悬垂引用

```rust
// ❌ 错误代码
fn get_reference() -> &String {
    let s = String::from("hello");
    &s  // 错误: s在函数结束时被释放
}

// ✅ 解决方案1: 返回所有权
fn get_string() -> String {
    String::from("hello")
}

// ✅ 解决方案2: 使用静态生命周期
fn get_static() -> &'static str {
    "hello"  // 字符串字面量是'static
}

// ✅ 解决方案3: 使用生命周期参数
struct Container<'a> {
    data: &'a str,
}

impl<'a> Container<'a> {
    fn get_data(&self) -> &'a str {
        self.data
    }
}
```

### 1.2 泛型约束错误

```rust
// ❌ 错误: 缺少trait约束
fn find_max<T>(list: &[T]) -> T {
    let mut max = list[0];
    for &item in list.iter() {
        if item > max {  // 错误: T可能不可比较
            max = item;
        }
    }
    max
}

// ✅ 添加PartialOrd约束
fn find_max<T: PartialOrd + Copy>(list: &[T]) -> T {
    let mut max = list[0];
    for &item in list.iter() {
        if item > max {
            max = item;
        }
    }
    max
}

// ✅ 或使用引用避免Copy约束
fn find_max_ref<T: PartialOrd>(list: &[T]) -> &T {
    let mut max = &list[0];
    for item in list.iter() {
        if item > max {
            max = item;
        }
    }
    max
}
```

### 1.3 no_std编译错误

```rust
// ❌ 错误: 在no_std中使用标准库类型
#![no_std]

fn use_vec() {
    let v = Vec::new();  // 错误: Vec在std中
}

// ✅ 解决方案: 使用alloc
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

fn use_vec_fixed() {
    let v = Vec::new();  // OK
}

// ✅ 或使用heapless进行静态分配
use heapless::Vec as StaticVec;

fn use_static_vec() {
    let v: StaticVec<u32, 100> = StaticVec::new();
}
```

---

## 2. 运行时问题诊断

### 2.1 Panic分析与恢复

```rust
use std::panic;

/// 安全关键panic处理器
pub fn setup_panic_handler() {
    panic::set_hook(Box::new(|info| {
        // 记录panic信息
        log::error!("Panic occurred: {}", info);

        // 获取位置信息
        if let Some(location) = info.location() {
            log::error!(
                "At file: {}, line: {}",
                location.file(),
                location.line()
            );
        }

        // 进入安全状态
        enter_safe_state();
    }));
}

fn enter_safe_state() -> ! {
    // 停止所有执行器
    // 设置安全输出
    // 通知监督系统
    loop {
        // 等待看门狗复位或人工干预
    }
}

/// 可恢复操作包装
pub fn safe_execute<T>(operation: impl FnOnce() -> T) -> Option<T> {
    match panic::catch_unwind(panic::AssertUnwindSafe(operation)) {
        Ok(result) => Some(result),
        Err(_) => {
            log::error!("Operation panicked, recovering...");
            None
        }
    }
}
```

### 2.2 堆栈溢出检测

```rust
/// 堆栈使用监控
#[cfg(target_arch = "arm")]
pub mod stack_monitor {
    use core::ptr;

    static mut STACK_BOTTOM: *const u8 = ptr::null();
    const STACK_SIZE: usize = 0x10000; // 64KB栈
    const STACK_MARGIN: usize = 0x1000; // 4KB安全边距

    /// 初始化栈监控
    pub unsafe fn init() {
        let local: u8 = 0;
        STACK_BOTTOM = &local as *const u8;
    }

    /// 检查栈使用
    pub fn check_usage() -> StackStatus {
        unsafe {
            let local: u8 = 0;
            let current_sp = &local as *const u8;
            let used = STACK_BOTTOM as usize - current_sp as usize;

            if used > STACK_SIZE - STACK_MARGIN {
                StackStatus::Critical(used)
            } else if used > STACK_SIZE * 8 / 10 {
                StackStatus::Warning(used)
            } else {
                StackStatus::Ok(used)
            }
        }
    }

    pub enum StackStatus {
        Ok(usize),
        Warning(usize),
        Critical(usize),
    }
}
```

### 2.3 死锁检测

```rust
use std::sync::{Mutex, LockResult};
use std::time::{Duration, Instant};

/// 带超时的Mutex包装
pub struct TimeoutMutex<T> {
    inner: Mutex<T>,
    timeout: Duration,
}

impl<T> TimeoutMutex<T> {
    pub fn new(data: T, timeout_ms: u64) -> Self {
        Self {
            inner: Mutex::new(data),
            timeout: Duration::from_millis(timeout_ms),
        }
    }

    pub fn try_lock(&self) -> Result<LockResult<std::sync::MutexGuard<T>>, TimeoutError> {
        let start = Instant::now();

        loop {
            match self.inner.try_lock() {
                Ok(guard) => return Ok(Ok(guard)),
                Err(std::sync::TryLockError::Poisoned(e)) => {
                    return Ok(Err(e));
                }
                Err(std::sync::TryLockError::WouldBlock) => {
                    if start.elapsed() > self.timeout {
                        return Err(TimeoutError);
                    }
                    std::thread::yield_now();
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct TimeoutError;

/// 死锁检测器
pub struct DeadlockDetector {
    lock_order: Mutex<Vec<String>>,
}

impl DeadlockDetector {
    pub fn new() -> Self {
        Self {
            lock_order: Mutex::new(Vec::new()),
        }
    }

    pub fn will_lock(&self, lock_name: &str) {
        let mut order = self.lock_order.lock().unwrap();

        // 检查是否违反锁顺序
        if order.contains(&lock_name.to_string()) {
            panic!("Potential deadlock: trying to acquire {} out of order", lock_name);
        }

        order.push(lock_name.to_string());
    }

    pub fn did_unlock(&self, lock_name: &str) {
        let mut order = self.lock_order.lock().unwrap();
        order.retain(|name| name != lock_name);
    }
}
```

---

## 3. 工具链问题

### 3.1 Miri常见问题

```bash
# 问题1: Miri报告"unsupported operation"
# 原因: 使用了Miri不支持的系统调用
# 解决: 条件编译跳过或使用Miri stub

#[cfg(miri)]
fn system_call() {
    // Miri环境下的模拟实现
}

#[cfg(not(miri))]
fn system_call() {
    // 真实系统调用
}

# 问题2: Miri运行缓慢
# 解决: 限制测试规模
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test --release

# 问题3: 堆栈溢出
# 解决: 增加栈大小
MIRIFLAGS="-Zmiri-stack-frame=16777216" cargo miri test
```

### 3.2 Kani验证失败

```rust
// 问题1: 验证超时
// 解决: 添加展开限制
#[kani::proof]
#[kani::unwind(10)]  // 限制循环展开
fn verify_with_loop() {
    // ...
}

// 问题2: 验证器内存不足
// 解决: 减少符号变量数量
#[kani::proof]
fn verify_small() {
    let x: u8 = kani::any();  // 使用u8而不是u64
    // ...
}

// 问题3: 期望的验证失败
#[kani::proof]
#[kani::should_panic]
fn verify_panic_case() {
    let x: u32 = kani::any();
    kani::assume(x > 100);
    assert!(x < 50);  // 这应该失败
}
```

### 3.3 Clippy配置问题

```toml
# clippy.toml
# 问题: 某些lint在安全关键代码中不适用

allow = [
    "clippy::cast_possible_truncation",  # 我们已经处理
    "clippy::cast_sign_loss",            # 有意识的转换
    "clippy::module_name_repetitions",   # 命名规范允许
]
```

---

## 4. 性能问题

### 4.1 二进制大小优化

```toml
# Cargo.toml
[profile.release]
opt-level = "z"      # 优化大小
lto = true           # 链接时优化
strip = true         # 去除符号
codegen-units = 1    # 单一代码单元
panic = "abort"      # 简化panic

# 可选: 使用优化后的panic处理器
[dependencies]
panic-halt = "0.2"
```

### 4.2 实时性能调优

```rust
/// 禁用运行时检查(仅在充分验证后)
#[cfg(not(debug_assertions))]
pub fn fast_add(a: u32, b: u32) -> u32 {
    // release模式下溢出检查关闭
    a + b
}

/// 确定性延迟
pub fn deterministic_delay(cycles: u32) {
    for _ in 0..cycles {
        // 编译器屏障防止优化
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

/// 缓存预热
pub fn cache_warmup<T>(data: &[T]) {
    // 访问所有数据以加载到缓存
    for item in data.iter() {
        core::ptr::read_volatile(item as *const T);
    }
}
```

---

## 5. 认证相关问题

### 5.1 覆盖率不达标

```bash
# 问题: MC/DC覆盖率低于100%
# 诊断: 找出未覆盖的分支
cargo llvm-cov --html --open

# 解决方案1: 添加边界测试
#[test]
fn test_boundary_conditions() {
    // 测试所有条件组合
    assert_eq!(compute(0, 0), expected);
    assert_eq!(compute(0, 1), expected);
    assert_eq!(compute(1, 0), expected);
    assert_eq!(compute(1, 1), expected);
}

# 解决方案2: 使用属性测试
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_all_branches(a: bool, b: bool) {
        let result = compute(a as u8, b as u8);
        // 验证所有分支
    }
}
```

### 5.2 工具链鉴定问题

```rust
/// 工具验证测试
#[cfg(test)]
mod tool_qualification {
    /// 验证编译器正确性
    #[test]
    fn verify_compiler_correctness() {
        // 基本运算
        assert_eq!(2 + 2, 4);

        // 溢出行为
        let max = u32::MAX;
        assert_eq!(max.wrapping_add(1), 0);

        // 类型转换
        let x: u8 = 255;
        let y = x as u16;
        assert_eq!(y, 255);
    }

    /// 验证优化不影响语义
    #[test]
    fn verify_optimization_correctness() {
        let data = [1, 2, 3, 4, 5];
        let sum: i32 = data.iter().sum();
        assert_eq!(sum, 15);
    }
}
```

---

## 6. 调试技巧

### 6.1 日志记录

```rust
use log::{info, warn, error, debug, trace};

/// 结构化日志
pub fn log_safety_event(event: SafetyEvent) {
    match event.severity {
        Severity::Info => info!(
            target: "safety",
            event_id = %event.id,
            timestamp = %event.timestamp,
            "Safety event: {}", event.description
        ),
        Severity::Warning => warn!(
            target: "safety",
            event_id = %event.id,
            "Safety warning: {}", event.description
        ),
        Severity::Error => error!(
            target: "safety",
            event_id = %event.id,
            "Safety error: {}", event.description
        ),
    }
}
```

### 6.2 断言策略

```rust
/// 编译时断言
const_assert!(std::mem::size_of::<State>() <= 64);

/// 运行时断言
fn critical_operation(data: &[u8]) {
    assert!(!data.is_empty(), "Input data cannot be empty");
    assert!(data.len() <= MAX_SIZE, "Input data too large");

    // 调试断言(只在debug模式)
    debug_assert_eq!(data[0], HEADER_MAGIC, "Invalid header");

    // 操作...
}

/// 不变量检查
struct InvariantChecker<T> {
    data: T,
}

impl<T> InvariantChecker<T> {
    pub fn new(data: T) -> Self
    where
        T: Invariant,
    {
        assert!(data.check_invariant(), "Invariant violated");
        Self { data }
    }

    pub fn modify<F>(&mut self, f: F)
    where
        F: FnOnce(&mut T),
        T: Invariant,
    {
        f(&mut self.data);
        assert!(self.data.check_invariant(), "Invariant violated after modification");
    }
}

trait Invariant {
    fn check_invariant(&self) -> bool;
}
```

---

## 7. 常见问题速查

| 问题 | 快速解决方案 |
|------|-------------|
| 借用检查器错误 | 使用`split_at_mut`, 缩小作用域, 或重构为索引 |
| 堆栈溢出 | 增加栈大小, 减少递归, 使用堆分配 |
| 二进制过大 | 启用LTO, strip符号, 优化大小而非速度 |
| Miri超时 | 减少测试规模, 添加unwind限制 |
| 覆盖率不足 | 添加边界测试, 使用属性测试 |
| 死锁 | 统一锁顺序, 使用超时锁, 避免嵌套锁 |
| 性能下降 | 分析热点, 减少动态分发, 启用优化 |

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**适用范围**: 所有ASIL/SIL等级

---

*持续更新中，欢迎贡献更多故障排除案例。*
