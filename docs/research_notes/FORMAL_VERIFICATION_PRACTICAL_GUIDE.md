# Rust 形式化验证实战指南

> **版本**: 1.0.0  
> **更新日期**: 2026-02-28  
> **目标读者**: Rust 开发者、安全工程师、形式化验证研究者  
> **前置知识**: 中级 Rust 编程基础、基本逻辑概念

---

## 📋 目录

- [1. 概述](#1-概述)
- [2. Kani 模型检查器](#2-kani-模型检查器)
  - [2.1 安装和配置](#21-安装和配置)
  - [2.2 基础属性验证](#22-基础属性验证)
  - [2.3 范围验证](#23-范围验证)
  - [2.4 内存安全验证](#24-内存安全验证)
  - [2.5 并发验证](#25-并发验证)
  - [2.6 循环和递归处理](#26-循环和递归处理)
  - [2.7 与 Cargo 集成](#27-与-cargo-集成)
  - [2.8 CI/CD 集成](#28-cicd-集成)
  - [2.9 实战验证案例](#29-实战验证案例)
- [3. Aeneas 函数式验证](#3-aeneas-函数式验证)
  - [3.1 安装和设置](#31-安装和设置)
  - [3.2 LLBC 中间表示](#32-llbc-中间表示)
  - [3.3 到 LeanCoq 的转换](#33-到-leancoq-的转换)
  - [3.4 证明编写基础](#34-证明编写基础)
  - [3.5 与 Rust 代码的对应关系](#35-与-rust-代码的对应关系)
  - [3.6 验证案例](#36-验证案例)
- [4. Miri 未定义行为检测](#4-miri-未定义行为检测)
  - [4.1 安装和运行](#41-安装和运行)
  - [4.2 Stacked Borrows vs Tree Borrows](#42-stacked-borrows-vs-tree-borrows)
  - [4.3 常见 UB 检测](#43-常见-ub-检测)
  - [4.4 与测试框架集成](#44-与测试框架集成)
- [5. 形式化验证策略](#5-形式化验证策略)
  - [5.1 何时使用何种工具](#51-何时使用何种工具)
  - [5.2 验证覆盖度规划](#52-验证覆盖度规划)
  - [5.3 与测试金字塔的关系](#53-与测试金字塔的关系)
- [6. 工具对比总结](#6-工具对比总结)
- [7. 参考资源](#7-参考资源)

---

## 1. 概述

### 1.1 什么是形式化验证

形式化验证是使用数学方法证明程序满足特定规范的过程。与传统测试不同，形式化验证可以**证明**程序在所有可能的输入下都正确，而不仅仅是测试有限的用例。

### 1.2 Rust 形式化验证生态系统

| 工具 | 验证方法 | 适用范围 | 自动化程度 | 学习曲线 |
|------|----------|----------|------------|----------|
| **Kani** | 模型检查 | 安全属性、边界检查 | 高 | 中等 |
| **Aeneas** | 定理证明 | 函数正确性、所有权 | 中 | 陡峭 |
| **Miri** | 动态分析 | 未定义行为检测 | 高 | 低 |
| **Prusti** | 契约验证 | 前置/后置条件 | 高 | 中等 |
| **Creusot** | 定理证明 | 函数正确性 | 中 | 陡峭 |

### 1.3 本指南目标

- 提供可直接运行的代码示例
- 覆盖常见验证场景
- 包含完整的 CI/CD 集成方案
- 提供故障排查指南

---

## 2. Kani 模型检查器

### 2.1 安装和配置

#### 2.1.1 系统要求

```bash
# 最低要求
- Rust 1.70+ (推荐最新稳定版)
- Python 3.8+
- 至少 8GB RAM (复杂验证建议 16GB+)
- Linux/macOS/Windows WSL
```

#### 2.1.2 安装步骤

```bash
# 1. 安装 Kani 验证器
cargo install --locked kani-verifier

# 2. 安装 Kani 依赖（CBMC 模型检查器）
cargo kani setup

# 3. 验证安装
cargo kani --version
# 输出: kani 0.XX.X
```

#### 2.1.3 项目配置

```toml
# Cargo.toml 添加 Kani 支持
[package]
name = "verified_project"
version = "0.1.0"
edition = "2021"

[dev-dependencies]
kani = "0.54"  # 最新稳定版

# Kani 特定配置
[package.metadata.kani]
# 默认启用的标志
flags = ["--unwind", "10", "--unwinding-assertions"]
```

#### 2.1.4 VS Code 集成

```json
// .vscode/settings.json
{
    "rust-analyzer.checkOnSave.command": "clippy",
    "editor.formatOnSave": true,
    "rust-analyzer.cargo.features": "all",
    // Kani 专用任务
    "tasks": {
        "version": "2.0.0",
        "tasks": [
            {
                "label": "Kani: Verify Current File",
                "type": "shell",
                "command": "cargo kani",
                "problemMatcher": ["$rustc"],
                "group": "test"
            }
        ]
    }
}
```

---

### 2.2 基础属性验证

#### 2.2.1 第一个验证示例

```rust
// src/lib.rs

/// 计算两个数的和，验证不会溢出
#[cfg(kani)]
mod verification {
    use kani::proof;

    #[proof]
    fn test_addition_no_overflow() {
        // 定义任意输入（符号化变量）
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        
        // 假设条件：确保不会溢出
        kani::assume(a <= u32::MAX / 2);
        kani::assume(b <= u32::MAX / 2);
        
        // 执行操作
        let result = a + b;
        
        // 验证属性
        assert!(result >= a);
        assert!(result >= b);
        assert!(result >= a.max(b));
    }
}
```

#### 2.2.2 运行验证

```bash
# 验证单个函数
cargo kani --function test_addition_no_overflow

# 验证所有 #[proof] 函数
cargo kani

# 详细输出
cargo kani --function test_addition_no_overflow --verbose
```

#### 2.2.3 核心 API 详解

```rust
use kani::{proof, any, assume, cover, assert, expect_fail};

// ========== 核心宏和函数 ==========

// 1. #[proof] - 标记验证目标函数
#[proof]
fn my_property() {
    // 验证代码
}

// 2. any<T>() - 生成任意值（符号化变量）
let x: i32 = kani::any();  // x 可以是任何 i32 值

// 3. assume(cond) - 添加前提条件
kani::assume(x > 0);  // 只考虑 x > 0 的情况

// 4. assert!(cond) - 验证后置条件
assert!(result > 0);  // Kani 会检查这是否总是成立

// 5. cover!(cond) - 检查可达性
cover!(x == 42);  // 确保存在执行路径使得 x == 42

// 6. expect_fail(cond, msg) - 期望失败的断言（用于反例）
kani::expect_fail(x > 100 && x < 50, "不可能的条件");
```

#### 2.2.4 常见验证模式

```rust
#[cfg(kani)]
mod verification_patterns {
    use kani::{proof, any, assume, assert};

    // 模式 1: 等价性验证
    #[proof]
    fn verify_equivalence() {
        let x: u32 = any();
        assume(x < 1000);
        
        // 验证两种实现等价
        let result1 = optimized_function(x);
        let result2 = reference_function(x);
        assert_eq!(result1, result2);
    }

    // 模式 2: 反例查找
    #[proof]
    #[kani::should_panic]  // 期望这个测试失败
    fn find_counterexample() {
        let x: i32 = any();
        // 找出使以下断言失败的 x 值
        assert!(x * x >= 0);  // 总是成立，不会找到反例
    }

    // 模式 3: 状态机验证
    #[proof]
    fn verify_state_machine() {
        let mut state = State::new();
        let input: u8 = any();
        
        state.transition(input);
        
        // 验证不变式
        assert!(state.is_valid());
        assert!(!state.is_error() || state.can_recover());
    }
}
```

---

### 2.3 范围验证

#### 2.3.1 边界检查验证

```rust
/// 安全数组访问示例
pub fn safe_get(arr: &[i32], index: usize) -> Option<i32> {
    if index < arr.len() {
        Some(arr[index])
    } else {
        None
    }
}

#[cfg(kani)]
mod bounds_verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    fn verify_safe_get_bounds() {
        // 创建任意数组（限制大小以提高性能）
        let arr: [i32; 5] = kani::any();
        let index: usize = kani::any();
        
        // 执行函数
        let result = safe_get(&arr, index);
        
        // 验证：如果索引有效，返回 Some；否则返回 None
        if index < arr.len() {
            assert!(result.is_some());
            assert_eq!(result.unwrap(), arr[index]);
        } else {
            assert!(result.is_none());
        }
    }

    // 使用切片验证任意长度
    #[proof]
    fn verify_with_slice() {
        let len: usize = kani::any();
        kani::assume(len <= 10);  // 限制数组长度
        
        let arr: [i32; 10] = kani::any();
        let slice = &arr[..len];
        let index: usize = kani::any();
        
        let result = safe_get(slice, index);
        
        // 覆盖所有情况
        kani::cover!(result.is_some());
        kani::cover!(result.is_none());
    }
}
```

#### 2.3.2 溢出检查验证

```rust
/// 安全算术运算
pub fn safe_add(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

pub fn saturating_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

#[cfg(kani)]
mod overflow_verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    fn verify_checked_add() {
        let a: u32 = any();
        let b: u32 = any();
        
        match safe_add(a, b) {
            Some(sum) => {
                // 如果返回 Some，和必须正确
                assert_eq!(sum, a + b);
                // 且没有溢出
                assert!(sum >= a);
                assert!(sum >= b);
            }
            None => {
                // 如果返回 None，必定溢出
                assert!(a > u32::MAX - b);
            }
        }
    }

    #[proof]
    fn verify_saturating_add() {
        let a: u32 = any();
        let b: u32 = any();
        
        let result = saturating_add(a, b);
        
        // 验证饱和性质
        if a > u32::MAX - b {
            // 会溢出，结果应为 u32::MAX
            assert_eq!(result, u32::MAX);
        } else {
            // 不会溢出，结果应为精确和
            assert_eq!(result, a + b);
        }
        
        // 通用性质：结果不会溢出
        assert!(result >= a || result == u32::MAX);
        assert!(result >= b || result == u32::MAX);
    }

    // 验证多个运算的组合
    #[proof]
    fn verify_arithmetic_chain() {
        let a: i32 = any();
        let b: i32 = any();
        let c: i32 = any();
        
        // 限制范围防止溢出
        assume(a.abs() < 1000);
        assume(b.abs() < 1000);
        assume(c.abs() < 1000);
        
        let result = a.wrapping_add(b).wrapping_mul(c);
        
        // 验证一些代数性质（在 wrapping 算术中）
        if c == 0 {
            assert_eq!(result, 0);
        }
        if a == 0 && b == 0 {
            assert_eq!(result, 0);
        }
    }
}
```

#### 2.3.3 范围转换验证

```rust
/// 安全的类型转换
pub fn u32_to_i32(val: u32) -> Option<i32> {
    if val <= i32::MAX as u32 {
        Some(val as i32)
    } else {
        None
    }
}

pub fn i32_to_u8_clamped(val: i32) -> u8 {
    val.clamp(0, 255) as u8
}

#[cfg(kani)]
mod conversion_verification {
    use super::*;
    use kani::{proof, any, assert};

    #[proof]
    fn verify_u32_to_i32() {
        let val: u32 = any();
        
        match u32_to_i32(val) {
            Some(i) => {
                assert!(i >= 0);
                assert_eq!(i as u32, val);
            }
            None => {
                assert!(val > i32::MAX as u32);
            }
        }
    }

    #[proof]
    fn verify_clamped_conversion() {
        let val: i32 = any();
        let result = i32_to_u8_clamped(val);
        
        // 验证结果在有效范围内
        assert!(result <= 255);
        
        // 验证具体值
        if val < 0 {
            assert_eq!(result, 0);
        } else if val > 255 {
            assert_eq!(result, 255);
        } else {
            assert_eq!(result as i32, val);
        }
    }
}
```

---

### 2.4 内存安全验证

#### 2.4.1 原始指针操作验证

```rust
/// 安全的原始指针写入
/// 
/// # Safety
/// - ptr 必须有效且对齐
/// - ptr 必须指向可写的内存
pub unsafe fn write_value<T>(ptr: *mut T, value: T) {
    ptr.write(value);
}

/// 安全的原始指针读取
/// 
/// # Safety
/// - ptr 必须有效且对齐
/// - ptr 必须指向可读的内存
pub unsafe fn read_value<T: Copy>(ptr: *const T) -> T {
    ptr.read()
}

#[cfg(kani)]
mod pointer_verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    fn verify_valid_pointer_ops() {
        let mut value: i32 = any();
        let ptr: *mut i32 = &mut value;
        
        // 验证有效指针操作
        unsafe {
            write_value(ptr, 42);
            let read = read_value(ptr);
            assert_eq!(read, 42);
            assert_eq!(value, 42);
        }
    }

    #[proof]
    fn verify_pointer_arithmetic_bounds() {
        let arr: [i32; 5] = [1, 2, 3, 4, 5];
        let offset: isize = any();
        
        // 假设偏移在有效范围内
        assume(offset >= 0 && offset < arr.len() as isize);
        
        unsafe {
            let ptr = arr.as_ptr().offset(offset);
            let value = ptr.read();
            
            // 验证读取的值正确
            assert_eq!(value, arr[offset as usize]);
        }
    }
}
```

#### 2.4.2 引用有效性验证

```rust
/// 安全的引用转换
pub fn as_bytes<T: Copy>(val: &T) -> &[u8] {
    let ptr = val as *const T as *const u8;
    unsafe {
        std::slice::from_raw_parts(ptr, std::mem::size_of::<T>())
    }
}

/// 安全的别名检查
pub fn no_alias_mutation(a: &mut i32, b: &i32) {
    // Rust 编译器保证 a 和 b 不别名
    *a += 1;
    // 这里可以安全地使用 b，因为借用检查器保证它们不重叠
    let _ = *b;
}

#[cfg(kani)]
mod reference_verification {
    use super::*;
    use kani::{proof, any, assert};

    #[proof]
    fn verify_byte_conversion() {
        let val: u32 = any();
        let bytes = as_bytes(&val);
        
        // 验证字节数正确
        assert_eq!(bytes.len(), 4);
        
        // 验证可以重建原值（小端序）
        let reconstructed = u32::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3]
        ]);
        assert_eq!(reconstructed, val);
    }
}
```

#### 2.4.3 智能指针验证

```rust
use std::alloc::{alloc, dealloc, Layout};

/// 自定义 Box-like 类型
pub struct VerifiedBox<T> {
    ptr: *mut T,
}

impl<T> VerifiedBox<T> {
    pub fn new(value: T) -> Self {
        let layout = Layout::new::<T>();
        unsafe {
            let ptr = alloc(layout) as *mut T;
            if ptr.is_null() {
                panic!("Allocation failed");
            }
            ptr.write(value);
            Self { ptr }
        }
    }
    
    pub fn get(&self) -> &T {
        unsafe { &*self.ptr }
    }
    
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}

impl<T> Drop for VerifiedBox<T> {
    fn drop(&mut self) {
        unsafe {
            std::ptr::drop_in_place(self.ptr);
            let layout = Layout::new::<T>();
            dealloc(self.ptr as *mut u8, layout);
        }
    }
}

#[cfg(kani)]
mod smart_pointer_verification {
    use super::*;
    use kani::{proof, any, assert};

    #[proof]
    fn verified_box_lifecycle() {
        let value: i32 = any();
        let b = VerifiedBox::new(value);
        
        assert_eq!(*b.get(), value);
    }
}
```

---

### 2.5 并发验证

#### 2.5.1 数据竞争检测

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

/// 线程安全的计数器
pub struct AtomicCounter {
    value: AtomicUsize,
}

impl AtomicCounter {
    pub fn new() -> Self {
        Self {
            value: AtomicUsize::new(0),
        }
    }
    
    pub fn increment(&self) {
        self.value.fetch_add(1, Ordering::SeqCst);
    }
    
    pub fn get(&self) -> usize {
        self.value.load(Ordering::SeqCst)
    }
    
    /// 使用 CAS 的原子更新
    pub fn add(&self, delta: usize) -> usize {
        let mut current = self.value.load(Ordering::Relaxed);
        loop {
            let new = current + delta;
            match self.value.compare_exchange(
                current, 
                new, 
                Ordering::SeqCst, 
                Ordering::SeqCst
            ) {
                Ok(_) => return new,
                Err(actual) => current = actual,
            }
        }
    }
}

#[cfg(kani)]
mod concurrency_verification {
    use super::*;
    use kani::{proof, any, assert};
    use std::sync::Arc;
    use std::thread;

    // 注意：Kani 的并发支持有限，以下是单线程属性验证
    
    #[proof]
    fn verify_counter_monotonicity() {
        let counter = AtomicCounter::new();
        let initial = counter.get();
        
        counter.increment();
        let after_inc = counter.get();
        
        assert!(after_inc > initial);
        assert_eq!(after_inc, initial + 1);
    }

    #[proof]
    fn verify_add_returns_new_value() {
        let counter = AtomicCounter::new();
        let delta: usize = any();
        
        let result = counter.add(delta);
        
        assert_eq!(result, delta);
        assert_eq!(counter.get(), delta);
    }
}
```

#### 2.5.2 锁正确性验证

```rust
use std::sync::Mutex;

/// 线程安全的状态
pub struct ThreadSafeState {
    data: Mutex<i32>,
}

impl ThreadSafeState {
    pub fn new() -> Self {
        Self {
            data: Mutex::new(0),
        }
    }
    
    pub fn update<F>(&self, f: F) 
    where 
        F: FnOnce(i32) -> i32 
    {
        let mut guard = self.data.lock().unwrap();
        *guard = f(*guard);
    }
    
    pub fn get(&self) -> i32 {
        *self.data.lock().unwrap()
    }
}

#[cfg(kani)]
mod lock_verification {
    use super::*;
    use kani::{proof, any, assert};

    #[proof]
    fn verify_state_update() {
        let state = ThreadSafeState::new();
        let input: i32 = any();
        
        state.update(|_| input);
        
        assert_eq!(state.get(), input);
    }

    #[proof]
    fn verify_multiple_updates() {
        let state = ThreadSafeState::new();
        let a: i32 = any();
        let b: i32 = any();
        
        assume(a.checked_add(b).is_some());
        
        state.update(|_| a);
        state.update(|v| v + b);
        
        assert_eq!(state.get(), a + b);
    }
}
```

---

### 2.6 循环和递归处理

#### 2.6.1 循环展开配置

```rust
/// 数组求和
pub fn sum_array(arr: &[i32]) -> i32 {
    let mut sum = 0;
    for &val in arr {
        sum = sum.saturating_add(val);
    }
    sum
}

/// 查找元素
pub fn find_element(arr: &[i32], target: i32) -> Option<usize> {
    for (i, &val) in arr.iter().enumerate() {
        if val == target {
            return Some(i);
        }
    }
    None
}

#[cfg(kani)]
mod loop_verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    #[kani::unwind(11)]  // 数组最大10个元素 + 1
    fn verify_sum_array() {
        let arr: [i32; 10] = any();
        let len: usize = any();
        assume(len <= 10);
        
        let slice = &arr[..len];
        let sum = sum_array(slice);
        
        // 验证：和不会溢出
        // 验证：空数组和为0
        if len == 0 {
            assert_eq!(sum, 0);
        }
    }

    #[proof]
    #[kani::unwind(11)]
    fn verify_find_element() {
        let arr: [i32; 10] = any();
        let len: usize = any();
        let target: i32 = any();
        assume(len <= 10);
        
        let slice = &arr[..len];
        let result = find_element(slice, target);
        
        // 如果找到，索引有效且值匹配
        if let Some(idx) = result {
            assert!(idx < len);
            assert_eq!(slice[idx], target);
        }
    }
}
```

#### 2.6.2 递归函数验证

```rust
/// 递归计算阶乘
pub fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// 安全的阶乘（防溢出）
pub fn safe_factorial(n: u32) -> Option<u64> {
    if n > 20 {
        // 20! 是最后一个适合 u64 的阶乘
        return None;
    }
    Some(factorial(n as u64))
}

/// 递归二分查找
pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }
    
    let mid = arr.len() / 2;
    if arr[mid] == target {
        Some(mid)
    } else if arr[mid] > target {
        binary_search(&arr[..mid], target)
    } else {
        binary_search(&arr[mid + 1..], target)
            .map(|i| i + mid + 1)
    }
}

#[cfg(kani)]
mod recursion_verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    #[kani::unwind(6)]  // 限制递归深度
    fn verify_factorial() {
        let n: u32 = any();
        assume(n <= 5);  // 限制输入范围
        
        let result = safe_factorial(n);
        
        // 验证基本性质
        if n == 0 || n == 1 {
            assert_eq!(result, Some(1));
        } else {
            assert!(result.is_some());
            let r = result.unwrap();
            // n! 可被 n 整除
            assert_eq!(r % n as u64, 0);
        }
    }

    #[proof]
    #[kani::unwind(6)]
    fn verify_binary_search_sorted() {
        // 二分查找要求数组有序
        let arr: [i32; 5] = any();
        assume(arr[0] <= arr[1]);
        assume(arr[1] <= arr[2]);
        assume(arr[2] <= arr[3]);
        assume(arr[3] <= arr[4]);
        
        let target: i32 = any();
        let result = binary_search(&arr, target);
        
        // 如果找到，验证索引正确
        if let Some(idx) = result {
            assert!(idx < arr.len());
            assert_eq!(arr[idx], target);
        }
    }
}
```

---

### 2.7 与 Cargo 集成

#### 2.7.1 项目结构

```
my_project/
├── Cargo.toml
├── Cargo.lock
├── src/
│   ├── lib.rs           # 主库代码
│   └── verification/
│       ├── mod.rs       # 验证模块入口
│       ├── kani_tests.rs # Kani 专用测试
│       └── properties.rs  # 属性定义
└── kani/                # Kani 配置文件
    ├── kani.toml        # Kani 配置
    └── stubs/           # 存根实现
```

#### 2.7.2 Kani 配置文件

```toml
# kani/kani.toml
[default]
# 默认 unwind 值
unwind = 10

# 超时设置（秒）
timeout = 300

# 内存限制（MB）
memory-limit = 4096

# 并发验证数
jobs = 4

# 额外 CBMC 标志
cbmc-args = [
    "--unwinding-assertions",
    "--bounds-check",
    "--pointer-check",
    "--div-by-zero-check",
    "--signed-overflow-check",
    "--unsigned-overflow-check",
    "--pointer-overflow-check",
    "--conversion-check",
]

[profile.release]
unwind = 20
timeout = 600

[profile.quick]
unwind = 5
timeout = 60
cbmc-args = ["--unwinding-assertions"]
```

#### 2.7.3 条件编译设置

```rust
// src/lib.rs

// 主库代码
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 只在 Kani 验证时编译的模块
#[cfg(kani)]
pub mod verification;

// 测试时包含验证
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }
}
```

```rust
// src/verification/mod.rs

//! Kani 形式化验证模块
//! 
//! 运行验证: cargo kani

pub mod arithmetic;
pub mod bounds;
pub mod safety;

// 公用辅助函数
pub fn assume_valid_range<T: Ord>(val: &T, min: &T, max: &T) {
    kani::assume(*val >= *min && *val <= *max);
}
```

#### 2.7.4 Makefile/Justfile

```makefile
# Makefile

.PHONY: verify verify-quick verify-full clean-kani

# 快速验证（开发时使用）
verify-quick:
	cargo kani --profile quick

# 默认验证
verify:
	cargo kani

# 完整验证（发布前）
verify-full:
	cargo kani --profile release

# 验证单个文件
verify-file:
	cargo kani --function $(FUNC)

# 生成覆盖率报告
verify-coverage:
	cargo kani --coverage --visualize

# 清理 Kani 临时文件
clean-kani:
	rm -rf target/kani
	rm -rf kani/*.out
	rm -rf kani/logs
```

---

### 2.8 CI/CD 集成

#### 2.8.1 GitHub Actions 配置

```yaml
# .github/workflows/kani.yml
name: Kani Verification

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]
  schedule:
    # 每天凌晨运行完整验证
    - cron: '0 0 * * *'

env:
  CARGO_TERM_COLOR: always

jobs:
  kani-quick:
    name: Quick Verification
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Kani
        uses: model-checking/kani-github-action@v1
        with:
          version: '0.54'  # 指定版本
          
      - name: Run Quick Verification
        run: |
          cargo kani --profile quick --output-format=terse
          
      - name: Upload Results
        if: failure()
        uses: actions/upload-artifact@v4
        with:
          name: kani-quick-results
          path: target/kani/

  kani-full:
    name: Full Verification
    runs-on: ubuntu-latest
    needs: kani-quick
    if: github.event_name == 'schedule' || contains(github.event.head_commit.message, '[full-verify]')
    timeout-minutes: 120
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Kani
        uses: model-checking/kani-github-action@v1
        
      - name: Run Full Verification
        run: |
          cargo kani --profile release --output-format=verbose 2>&1 | tee kani-full.log
          
      - name: Generate Coverage Report
        run: |
          cargo kani --coverage --visualize
          
      - name: Upload Coverage
        uses: actions/upload-artifact@v4
        with:
          name: kani-coverage
          path: |
            target/kani/coverage/
            kani-full.log

  kani-report:
    name: Generate Report
    runs-on: ubuntu-latest
    needs: [kani-quick]
    if: always()
    steps:
      - uses: actions/checkout@v4
      
      - name: Download Results
        uses: actions/download-artifact@v4
        with:
          name: kani-quick-results
          
      - name: Generate Markdown Report
        run: |
          cat > kani-report.md << 'EOF'
          # Kani Verification Report
          
          ## Summary
          - Run Date: $(date)
          - Commit: ${{ github.sha }}
          
          ## Results
          See attached artifacts for detailed output.
          EOF
          
      - name: Comment on PR
        if: github.event_name == 'pull_request'
        uses: actions/github-script@v7
        with:
          script: |
            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.repo,
              body: '✅ Kani verification completed. See workflow run for details.'
            })
```

#### 2.8.2 GitLab CI 配置

```yaml
# .gitlab-ci.yml

stages:
  - verify
  - report

variables:
  KANI_VERSION: "0.54"
  CARGO_HOME: "$CI_PROJECT_DIR/.cargo"

.kani-base:
  image: rust:latest
  cache:
    paths:
      - .cargo/
      - target/
  before_script:
    - cargo install --locked kani-verifier@$KANI_VERSION
    - cargo kani setup

kani:quick:
  stage: verify
  extends: .kani-base
  script:
    - cargo kani --profile quick
  artifacts:
    when: always
    paths:
      - target/kani/
    expire_in: 1 week

kani:full:
  stage: verify
  extends: .kani-base
  rules:
    - if: $CI_PIPELINE_SOURCE == "schedule"
    - if: $CI_COMMIT_BRANCH == "main"
  timeout: 2h
  script:
    - cargo kani --profile release
  artifacts:
    when: always
    paths:
      - target/kani/
    expire_in: 1 month
```

#### 2.8.3 验证脚本

```bash
#!/bin/bash
# scripts/verify.sh - 本地验证脚本

set -e

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

PROFILE="${1:-default}"
FUNCTION="${2:-}"

echo "========================================="
echo "Running Kani Verification"
echo "Profile: $PROFILE"
echo "========================================="

# 检查 Kani 安装
if ! command -v cargo-kani &> /dev/null; then
    echo -e "${RED}Error: Kani not found${NC}"
    echo "Install with: cargo install --locked kani-verifier"
    exit 1
fi

# 构建验证命令
CMD="cargo kani --profile $PROFILE"

if [ -n "$FUNCTION" ]; then
    CMD="$CMD --function $FUNCTION"
fi

echo "Command: $CMD"
echo ""

# 运行验证
if $CMD; then
    echo ""
    echo -e "${GREEN}✓ Verification passed${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}✗ Verification failed${NC}"
    echo "Run with --visualize to see counterexample"
    exit 1
fi
```

---

### 2.9 实战验证案例

#### 案例 1: 排序算法验证

```rust
// src/algorithms/sort.rs

/// 插入排序实现
pub fn insertion_sort(arr: &mut [i32]) {
    for i in 1..arr.len() {
        let mut j = i;
        while j > 0 && arr[j - 1] > arr[j] {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

/// 检查数组是否有序
pub fn is_sorted(arr: &[i32]) -> bool {
    arr.windows(2).all(|w| w[0] <= w[1])
}

/// 检查两个数组包含相同元素（多重集相等）
pub fn same_elements(a: &[i32], b: &[i32]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut a_sorted = a.to_vec();
    let mut b_sorted = b.to_vec();
    a_sorted.sort();
    b_sorted.sort();
    a_sorted == b_sorted
}

#[cfg(kani)]
mod verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    #[kani::unwind(6)]
    fn verify_insertion_sort_correct() {
        let mut arr: [i32; 5] = any();
        let original = arr;
        
        insertion_sort(&mut arr);
        
        // 属性 1: 结果有序
        assert!(is_sorted(&arr));
        
        // 属性 2: 元素集合不变
        assert!(same_elements(&arr, &original));
    }

    #[proof]
    fn verify_is_sorted_properties() {
        // 空数组和单元素数组总是有序的
        let empty: [i32; 0] = [];
        assert!(is_sorted(&empty));
        
        let single: [i32; 1] = any();
        assert!(is_sorted(&single));
        
        // 有序数组的检测
        let sorted: [i32; 3] = [1, 2, 3];
        assert!(is_sorted(&sorted));
        
        // 无序数组的检测
        let unsorted: [i32; 3] = [3, 1, 2];
        assert!(!is_sorted(&unsorted));
    }
}
```

#### 案例 2: 链表操作验证

```rust
// src/collections/linked_list.rs

/// 简单单向链表节点
pub struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T> Node<T> {
    pub fn new(data: T) -> Self {
        Self { data, next: None }
    }
    
    /// 在头部插入
    pub fn prepend(self, data: T) -> Self {
        let mut new_node = Self::new(data);
        new_node.next = Some(Box::new(self));
        new_node
    }
    
    /// 获取长度
    pub fn len(&self) -> usize {
        1 + self.next.as_ref().map_or(0, |n| n.len())
    }
    
    /// 查找元素
    pub fn contains(&self, val: &T) -> bool 
    where 
        T: PartialEq 
    {
        if &self.data == val {
            true
        } else {
            self.next.as_ref().map_or(false, |n| n.contains(val))
        }
    }
}

/// 链表包装器
pub struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        Self { head: None }
    }
    
    pub fn push_front(&mut self, data: T) {
        match self.head.take() {
            Some(node) => {
                self.head = Some(Box::new(node.prepend(data)));
            }
            None => {
                self.head = Some(Box::new(Node::new(data)));
            }
        }
    }
    
    pub fn len(&self) -> usize {
        self.head.as_ref().map_or(0, |n| n.len())
    }
    
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }
}

#[cfg(kani)]
mod verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    #[kani::unwind(5)]
    fn verify_list_invariants() {
        let mut list: LinkedList<i32> = LinkedList::new();
        
        // 空列表性质
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        
        // 添加元素
        let val: i32 = any();
        list.push_front(val);
        
        assert!(!list.is_empty());
        assert_eq!(list.len(), 1);
    }

    #[proof]
    #[kani::unwind(4)]
    fn verify_push_increments_length() {
        let mut list: LinkedList<i32> = LinkedList::new();
        let n: u8 = any();
        assume(n <= 3);
        
        for _ in 0..n {
            list.push_front(any());
        }
        
        assert_eq!(list.len(), n as usize);
    }
}
```

#### 案例 3: 缓冲区操作验证

```rust
// src/io/buffer.rs

/// 环形缓冲区
pub struct RingBuffer<T, const N: usize> {
    buffer: [Option<T>; N],
    head: usize,
    tail: usize,
    count: usize,
}

impl<T: Copy + Default, const N: usize> RingBuffer<T, N> {
    pub fn new() -> Self {
        Self {
            buffer: [None; N],
            head: 0,
            tail: 0,
            count: 0,
        }
    }
    
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }
    
    pub fn is_full(&self) -> bool {
        self.count == N
    }
    
    pub fn len(&self) -> usize {
        self.count
    }
    
    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.is_full() {
            return Err(item);
        }
        self.buffer[self.tail] = Some(item);
        self.tail = (self.tail + 1) % N;
        self.count += 1;
        Ok(())
    }
    
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let item = self.buffer[self.head].take();
        self.head = (self.head + 1) % N;
        self.count -= 1;
        item
    }
    
    pub fn peek(&self) -> Option<T> {
        self.buffer[self.head].clone()
    }
}

#[cfg(kani)]
mod verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    fn verify_new_buffer() {
        let buf: RingBuffer<i32, 4> = RingBuffer::new();
        assert!(buf.is_empty());
        assert!(!buf.is_full());
        assert_eq!(buf.len(), 0);
    }

    #[proof]
    #[kani::unwind(6)]
    fn verify_push_pop() {
        let mut buf: RingBuffer<i32, 4> = RingBuffer::new();
        let items: [i32; 4] = any();
        let n: usize = any();
        assume(n <= 4);
        
        // 推入 n 个元素
        for i in 0..n {
            assert!(buf.push(items[i]).is_ok());
            assert_eq!(buf.len(), i + 1);
        }
        
        // 弹出 n 个元素
        for i in 0..n {
            assert!(!buf.is_empty());
            let popped = buf.pop();
            assert!(popped.is_some());
            assert_eq!(buf.len(), n - i - 1);
        }
        
        assert!(buf.is_empty());
    }

    #[proof]
    fn verify_push_full() {
        let mut buf: RingBuffer<i32, 2> = RingBuffer::new();
        
        // 填满缓冲区
        assert!(buf.push(1).is_ok());
        assert!(buf.push(2).is_ok());
        assert!(buf.is_full());
        
        // 再推应该失败
        let result = buf.push(3);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), 3);
    }

    #[proof]
    #[kani::unwind(6)]
    fn verify_fifo_order() {
        let mut buf: RingBuffer<i32, 4> = RingBuffer::new();
        let a: i32 = any();
        let b: i32 = any();
        
        buf.push(a).unwrap();
        buf.push(b).unwrap();
        
        // FIFO: 先进先出
        assert_eq!(buf.pop(), Some(a));
        assert_eq!(buf.pop(), Some(b));
    }
}
```

#### 案例 4: 状态机验证

```rust
// src/state_machine.rs

/// TCP 连接状态机简化版
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TcpState {
    Closed,
    Listen,
    SynSent,
    SynReceived,
    Established,
    FinWait1,
    FinWait2,
    CloseWait,
    Closing,
    LastAck,
    TimeWait,
}

#[derive(Debug)]
pub struct TcpConnection {
    state: TcpState,
    can_send: bool,
    can_receive: bool,
}

impl TcpConnection {
    pub fn new() -> Self {
        Self {
            state: TcpState::Closed,
            can_send: false,
            can_receive: false,
        }
    }
    
    pub fn open(&mut self) {
        if self.state == TcpState::Closed {
            self.state = TcpState::SynSent;
        }
    }
    
    pub fn listen(&mut self) {
        if self.state == TcpState::Closed {
            self.state = TcpState::Listen;
        }
    }
    
    pub fn syn_received(&mut self) {
        if self.state == TcpState::Listen {
            self.state = TcpState::SynReceived;
        }
    }
    
    pub fn established(&mut self) {
        match self.state {
            TcpState::SynSent | TcpState::SynReceived => {
                self.state = TcpState::Established;
                self.can_send = true;
                self.can_receive = true;
            }
            _ => {}
        }
    }
    
    pub fn close(&mut self) {
        match self.state {
            TcpState::Established => {
                self.state = TcpState::FinWait1;
                self.can_send = false;
            }
            TcpState::CloseWait => {
                self.state = TcpState::LastAck;
            }
            _ => {}
        }
    }
    
    pub fn is_valid(&self) -> bool {
        // 不变式：只有 Established 状态可以同时发送和接收
        match self.state {
            TcpState::Established => self.can_send && self.can_receive,
            TcpState::FinWait1 | TcpState::FinWait2 => !self.can_send && self.can_receive,
            TcpState::CloseWait => self.can_send && !self.can_receive,
            _ => !self.can_send && !self.can_receive,
        }
    }
}

#[cfg(kani)]
mod verification {
    use super::*;
    use kani::{proof, any, assume, assert, cover};

    #[proof]
    fn verify_state_invariants() {
        let mut conn = TcpConnection::new();
        
        // 初始状态
        assert_eq!(conn.state, TcpState::Closed);
        assert!(conn.is_valid());
        
        // 测试所有可能的转换
        conn.open();
        assert!(conn.is_valid());
        cover!(conn.state == TcpState::SynSent);
    }

    #[proof]
    fn verify_established_properties() {
        let mut conn = TcpConnection::new();
        
        conn.listen();
        conn.syn_received();
        conn.established();
        
        assert_eq!(conn.state, TcpState::Established);
        assert!(conn.can_send);
        assert!(conn.can_receive);
        assert!(conn.is_valid());
        
        conn.close();
        assert!(!conn.can_send);
        assert!(conn.is_valid());
    }

    #[proof]
    fn verify_close_from_invalid_states() {
        let mut conn = TcpConnection::new();
        
        // 从未建立连接就关闭
        conn.close();
        assert_eq!(conn.state, TcpState::Closed);  // 状态不变
    }
}
```

#### 案例 5: 加密原语验证

```rust
// src/crypto/primitives.rs

/// 常量时间比较（防时序攻击）
pub fn secure_compare(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    
    let mut result: u8 = 0;
    for i in 0..a.len() {
        result |= a[i] ^ b[i];
    }
    
    result == 0
}

/// 安全的 XOR 操作
pub fn xor_in_place(a: &mut [u8], b: &[u8]) {
    let len = a.len().min(b.len());
    for i in 0..len {
        a[i] ^= b[i];
    }
}

/// 简单的校验和计算
pub fn checksum(data: &[u8]) -> u16 {
    let mut sum: u32 = 0;
    
    // 两字节一组相加
    for chunk in data.chunks(2) {
        let word = if chunk.len() == 2 {
            ((chunk[0] as u16) << 8) | (chunk[1] as u16)
        } else {
            (chunk[0] as u16) << 8
        };
        sum += word as u32;
    }
    
    // 进位回卷
    while (sum >> 16) != 0 {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }
    
    !sum as u16
}

#[cfg(kani)]
mod verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    fn verify_secure_compare_reflexive() {
        let data: [u8; 16] = any();
        
        // 任何值与自身比较应为 true
        assert!(secure_compare(&data, &data));
    }

    #[proof]
    fn verify_secure_compare_length() {
        let a: [u8; 8] = any();
        let b: [u8; 16] = any();
        
        // 不同长度应为 false
        assert!(!secure_compare(&a, &b[..8]));
    }

    #[proof]
    fn verify_xor_properties() {
        let original: [u8; 8] = any();
        let key: [u8; 8] = any();
        
        let mut encrypted = original;
        xor_in_place(&mut encrypted, &key);
        
        // 验证：加密 != 原文（除非 key 全为0）
        // 不能直接用 assert，因为 key 可能为0
        
        // XOR 两次应恢复原文
        let mut decrypted = encrypted;
        xor_in_place(&mut decrypted, &key);
        
        assert_eq!(decrypted, original);
    }

    #[proof]
    #[kani::unwind(11)]
    fn verify_checksum_properties() {
        let data: [u8; 10] = any();
        let len: usize = any();
        assume(len <= 10);
        
        let slice = &data[..len];
        let cs = checksum(slice);
        
        // 校验和是一个 u16
        // 相同数据应有相同校验和
        let cs2 = checksum(slice);
        assert_eq!(cs, cs2);
    }
}
```

---

## 3. Aeneas 函数式验证

### 3.1 安装和设置

#### 3.1.1 系统要求

```bash
# 必需依赖
- OCaml 4.14+ (通过 opam 安装)
- Rust nightly toolchain
- Lean 4 或 Coq (用于证明)
- Git

# 可选但推荐
- elan (Lean 版本管理器)
- coq-lsp (Coq 编辑器支持)
```

#### 3.1.2 安装步骤

```bash
# 1. 安装 opam (OCaml 包管理器)
# macOS
brew install opam

# Ubuntu/Debian
sudo apt-get install opam

# 2. 初始化 opam
opam init --disable-sandboxing
eval $(opam env)

# 3. 安装 OCaml 依赖
opam switch create 4.14.0
eval $(opam env)
opam install dune menhir ocamlgraph zarith

# 4. 克隆 Aeneas
git clone https://github.com/AeneasVerif/aeneas.git
cd aeneas

# 5. 构建 Aeneas
make build

# 6. 安装到 PATH
make install  # 或手动将 _build/default/bin/aeneas 添加到 PATH

# 7. 验证安装
aeneas --version
```

#### 3.1.3 安装 Lean 4 (如果选择 Lean 后端)

```bash
# 安装 elan (Rust 的 rustup 类似工具)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source $HOME/.elan/env

# 安装 Lean 4
elan toolchain install stable
elan default stable

# 安装 Lake (Lean 包管理器)
elan run stable lake

# 验证
lean --version
```

#### 3.1.4 安装 Coq (如果选择 Coq 后端)

```bash
# 通过 opam 安装
opam install coq coqide

# 或从源码
# 参见 https://coq.inria.fr/download
```

---

### 3.2 LLBC 中间表示

#### 3.2.1 什么是 LLBC

LLBC (Low-Level Borrow Calculus) 是 Aeneas 的核心中间表示，它是 Rust MIR 的进一步抽象，专门设计用于支持形式化验证：

```
Rust Source
    ↓ (rustc)
   HIR (High-level IR)
    ↓ (rustc)
   MIR (Mid-level IR)
    ↓ (Charon)
   ULLBC (Unstructured LLBC)
    ↓ (Aeneas)
   LLBC (Structured LLBC)
    ↓ (Aeneas 后端)
   Lean / Coq / F* / HOL4
```

#### 3.2.2 LLBC 关键特性

| 特性 | 描述 | 用途 |
|------|------|------|
| **区域 (Regions)** | 生命周期的抽象表示 | 验证借用有效性 |
| **贷款 (Loans)** | 可变/不可变借用的显式表示 | 跟踪所有权变化 |
| **投影 (Projections)** | 结构体字段访问 | 精确别名分析 |
| **擦除 (End)** | 生命周期结束标记 | 自动资源管理 |

#### 3.2.3 示例：Rust 到 LLBC 的转换

```rust
// Rust 源代码
fn swap<T>(a: &mut T, b: &mut T) {
    std::mem::swap(a, b);
}

fn use_after_move() {
    let x = vec![1, 2, 3];
    let y = x;  // x 被移动
    // println!("{:?}", x);  // 错误：使用了已移动的值
    println!("{:?}", y);  // OK
}
```

```lean4
-- 生成的 LLBC (概念表示)
-- LLBC 显式跟踪所有权状态

def swap (T : Type) (a : RefMut T) (b : RefMut T) : Unit :=
  -- LLBC 显式处理可变引用
  let tmp := !a  -- 解引用 a
  a := !b        -- 写入 a
  b := tmp       -- 写入 b
  
def use_after_move : Unit :=
  let x := Vec.mk [1, 2, 3]
  let y := move x  -- 'move' 显式标记
  -- x 在此不可用
  print y
```

---

### 3.3 到 Lean/Coq 的转换

#### 3.3.1 Charon 前端

Charon 负责将 Rust MIR 转换为 ULLBC：

```bash
# 安装 Charon
cargo install charon

# 基本用法
charon --input src/lib.rs --output output.llbc

# 或作为 cargo 插件
cargo charon
```

#### 3.3.2 Aeneas 转换流程

```bash
# 完整转换流程

# 1. 准备 Rust 项目
cd my_rust_project

# 2. 生成 LLBC
charon --input src/lib.rs
# 输出: ./llbc/myproject.llbc

# 3. 转换到 Lean
aeneas -backend lean ./llbc/myproject.llbc -o ./lean/

# 4. 转换到 Coq
aeneas -backend coq ./llbc/myproject.llbc -o ./coq/

# 5. 查看帮助
aeneas --help
```

#### 3.3.3 生成的 Lean 4 代码结构

```lean4
-- myproject.lean (Aeneas 生成)

import Aeneas
open Aeneas

namespace MyProject

-- 生成的类型定义
structure Point where
  x : I32
  y : I32
  deriving Inhabited

-- 生成的函数签名（包含所有权信息）
def translate (p : Point) : Point :=
  { x := p.y, y := p.x }

-- 生成的证明义务（关于移动的谓词）
-- Aeneas 自动生成所有权相关的定理

end MyProject
```

#### 3.3.4 生成的 Coq 代码结构

```coq
(* myproject.v (Aeneas 生成) *)

Require Import Aeneas.Aeneas.
From Aeneas Require Import std.
Import std.

Module MyProject.

(* 类型定义 *)
Record point : Type := {
  point_x : i32;
  point_y : i32;
}.

(* 函数定义 *)
Definition translate (p : point) : point :=
  {| point_x := point_y p; point_y := point_x p |}.

(* 生成的引理 *)
(* 证明移动语义正确性 *)

End MyProject.
```

---

### 3.4 证明编写基础

#### 3.4.1 Lean 4 证明基础

```lean4
-- basic_proofs.lean
import Aeneas
open Aeneas

namespace Tutorial

-- ========== 简单等式证明 ==========

-- 定义一个简单的加法函数
def my_add (a b : Nat) : Nat := a + b

-- 定理：加法交换律
theorem add_commutative (a b : Nat) : my_add a b = my_add b a := by
  simp [my_add, Nat.add_comm]

-- ========== 归纳证明 ==========

-- 自定义列表长度函数
def list_length {α : Type} : List α → Nat
  | [] => 0
  | _ :: tail => 1 + list_length tail

-- 定理：append 后长度等于长度之和
theorem length_append {α : Type} (xs ys : List α) :
  list_length (xs ++ ys) = list_length xs + list_length ys := by
  induction xs with
  | nil => simp [list_length]
  | cons x xs ih => 
    simp [list_length]
    rw [ih]
    simp [Nat.add_assoc]

-- ========== 所有权相关证明 ==========

-- 验证移动后原变量不可用
structure UniqueId where
  id : Nat
deriving Inhabited

def use_id (u : UniqueId) : Nat := u.id

-- 证明：使用后消耗值
theorem use_id_consumes (u : UniqueId) : ∃ n : Nat, use_id u = n := by
  exists u.id

end Tutorial
```

#### 3.4.2 Coq 证明基础

```coq
(* basic_proofs.v *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Module Tutorial.

(* ========== 简单等式证明 ========== *)

Definition my_add (a b : nat) : nat := a + b.

(* 定理：加法交换律 *)
Theorem add_commutative : forall a b : nat,
  my_add a b = my_add b a.
Proof.
  intros a b.
  unfold my_add.
  apply Nat.add_comm.
Qed.

(* ========== 归纳证明 ========== *)

Fixpoint list_length {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: tail => S (list_length tail)
  end.

(* 定理：append 后长度等于长度之和 *)
Theorem length_append : forall (A : Type) (xs ys : list A),
  list_length (xs ++ ys) = list_length xs + list_length ys.
Proof.
  intros A xs ys.
  induction xs as [| x xs' IH].
  - (* 基本情况：空列表 *)
    simpl.
    reflexivity.
  - (* 归纳步骤 *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(* ========== 使用 SSReflect（推荐） ========== *)

From mathcomp Require Import all_ssreflect.

Theorem addnC : forall m n : nat, m + n = n + m.
Proof.
  move=> m n.
  by rewrite addnC.
Qed.

End Tutorial.
```

#### 3.4.3 常用证明策略

| 策略 (Lean) | 策略 (Coq) | 用途 |
|------------|-----------|------|
| `intro` | `intro` / `intros` | 引入假设 |
| `apply` | `apply` | 应用定理 |
| `simp` | `simpl` / `cbn` | 简化表达式 |
| `rw` | `rewrite` | 重写等式 |
| `induction` | `induction` | 归纳证明 |
| `cases` | `destruct` | 分情况分析 |
| `exact` | `exact` | 精确匹配 |
| `trivial` | `trivial` | 尝试简单证明 |

---

### 3.5 与 Rust 代码的对应关系

#### 3.5.1 所有权映射

```rust
// Rust 代码
fn ownership_example() {
    let x = 5;           // x: i32
    let y = x;           // 复制 (i32 实现 Copy)
    
    let s = String::from("hello");  // s: String
    let t = s;                      // 移动，s 无效
    // println!("{}", s);           // 编译错误！
    println!("{}", t);              // OK
}
```

```lean4
-- 生成的 Lean 代码（概念）

def ownership_example : Unit :=
  let x : I32 := 5
  let y : I32 := x       -- 复制，两者都有效
  
  let s : String := String.from "hello"
  let t : String := move s  -- 移动，s 不再有效
  -- 任何使用 s 的代码都会生成证明错误
  let _ := print t
```

#### 3.5.2 借用映射

```rust
// 不可变借用
fn borrow_example(v: &Vec<i32>) -> i32 {
    v[0]
}

// 可变借用
fn modify_example(v: &mut Vec<i32>) {
    v.push(42);
}

// 多借用
fn multi_borrow() {
    let mut x = 5;
    let y = &x;      // 不可变借用
    let z = &x;      // 另一个不可变借用 - OK
    // let w = &mut x; // 错误！
    println!("{} {}", y, z);
}
```

```lean4
-- Lean 表示（概念）

-- 不可变借用生成共享引用
def borrow_example (v : SharedRef (Vec I32)) : I32 :=
  v.index 0

-- 可变借用生成可变引用
def modify_example (v : MutRef (Vec I32)) : Unit :=
  v.push 42

-- 借用检查在转换时验证
-- 无法转换违反借用规则的代码
```

---

### 3.6 验证案例

#### 案例 1: 所有权验证

```rust
// src/ownership.rs

/// 简单的资源管理器
pub struct Resource {
    id: u64,
    active: bool,
}

impl Resource {
    pub fn new(id: u64) -> Self {
        Self { id, active: true }
    }
    
    pub fn consume(self) -> u64 {
        self.id
    }
    
    pub fn is_active(&self) -> bool {
        self.active
    }
}

/// 资源传输函数
pub fn transfer_ownership(from: Resource, to_id: u64) -> Resource {
    let _ = from.consume();
    Resource::new(to_id)
}
```

```bash
# 转换命令
charon --input src/ownership.rs
aeneas -backend lean llbc/ownership.llbc -o lean/
```

```lean4
-- lean/Ownership.lean (部分生成 + 手动证明)

import Aeneas
open Aeneas Std Result

namespace Ownership

-- 生成的类型
def Resource := {
  id : U64,
  active : Bool
}

-- 生成的函数
def Resource.new (id : U64) : Resource := {
  id := id,
  active := true
}

def Resource.consume (self : Resource) : U64 :=
  self.id

-- 手动添加的证明
theorem consume_after_new (id : U64) :
  Resource.consume (Resource.new id) = id := by
  simp [Resource.new, Resource.consume]

-- 验证所有权转移
def transfer_ownership (from : Resource) (to_id : U64) : Resource :=
  let _ := Resource.consume from
  Resource.new to_id

-- 证明：转移后获得新资源
theorem transfer_creates_new (from : Resource) (to_id : U64) :
  (transfer_ownership from to_id).id = to_id := by
  simp [transfer_ownership, Resource.new]

-- 证明：旧资源被消耗
theorem transfer_consumes_old (from : Resource) (to_id : U64) :
  -- 无法访问 'from'，因为它已被移动
  True := by
  -- Lean 类型系统保证这一点
  trivial

end Ownership
```

#### 案例 2: 借用验证

```rust
// src/borrowing.rs

/// 交换数组元素
pub fn swap_elements(arr: &mut [i32], i: usize, j: usize) {
    if i < arr.len() && j < arr.len() {
        arr.swap(i, j);
    }
}

/// 查找并修改
pub fn find_and_double(arr: &mut [i32], target: i32) -> bool {
    for i in 0..arr.len() {
        if arr[i] == target {
            arr[i] *= 2;
            return true;
        }
    }
    false
}

/// 不可变遍历
pub fn sum_elements(arr: &[i32]) -> i32 {
    arr.iter().sum()
}
```

```lean4
-- lean/Borrowing.lean

import Aeneas
open Aeneas Std

namespace Borrowing

-- swap_elements 的验证
-- 重点：证明借用规则被遵守

def swap_elements (arr : MutRef (Slice I32)) (i j : Usize) : Unit :=
  if i < arr.length && j < arr.length then
    arr.swap i j
  else
    ()

-- 定理：交换后数组长度不变
theorem swap_preserves_length 
  (arr : MutRef (Slice I32)) (i j : Usize) :
  let arr' := swap_elements arr i j
  arr'.length = arr.length := by
  simp [swap_elements]
  split
  · simp [Slice.swap_preserves_length]
  · rfl

-- find_and_double 的验证
def find_and_double (arr : MutRef (Slice I32)) (target : I32) : Bool :=
  let rec loop (i : Usize) : Bool :=
    if i < arr.length then
      if arr.index i = target then
        arr.update i (target * 2)
        true
      else
        loop (i + 1)
    else
      false
  loop 0

-- 定理：如果找到并修改，元素值被加倍
theorem find_and_double_correct 
  (arr : MutRef (Slice I32)) (target : I32) :
  find_and_double arr target = true ->
  ∃ i : Usize, i < arr.length ∧ arr.index i = target * 2 := by
  intro h_found
  -- 展开递归定义并证明
  sorry  -- 完整证明需要归纳

-- sum_elements 的验证
def sum_elements (arr : SharedRef (Slice I32)) : I32 :=
  arr.iter.foldl 0 (fun acc x => acc + x)

-- 定理：空数组的和为 0
theorem sum_empty : sum_elements #[] = 0 := by
  simp [sum_elements]

end Borrowing
```

#### 案例 3: 递归函数验证

```rust
// src/recursion.rs

/// 递归列表求和
pub fn recursive_sum(list: &[i32]) -> i32 {
    match list {
        [] => 0,
        [head, tail @ ..] => head + recursive_sum(tail),
    }
}

/// 尾递归阶乘
pub fn tail_factorial(n: u64) -> u64 {
    fn fact_acc(n: u64, acc: u64) -> u64 {
        if n == 0 {
            acc
        } else {
            fact_acc(n - 1, acc * n)
        }
    }
    fact_acc(n, 1)
}

/// 二分查找（递归）
pub fn recursive_binary_search(arr: &[i32], target: i32) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }
    
    let mid = arr.len() / 2;
    if arr[mid] == target {
        Some(mid)
    } else if arr[mid] > target {
        recursive_binary_search(&arr[..mid], target)
    } else {
        recursive_binary_search(&arr[mid + 1..], target)
            .map(|i| i + mid + 1)
    }
}
```

```lean4
-- lean/Recursion.lean

import Aeneas
open Aeneas Std

namespace Recursion

-- ========== recursive_sum 验证 ==========

def recursive_sum (list : Slice I32) : I32 :=
  match list with
  | [] => 0
  | head :: tail => head + recursive_sum tail

-- 定理：空列表的和为 0
theorem sum_empty : recursive_sum #[] = 0 := by
  simp [recursive_sum]

-- 定理：和的递归性质
theorem sum_cons (head : I32) (tail : Slice I32) :
  recursive_sum (head :: tail) = head + recursive_sum tail := by
  simp [recursive_sum]

-- 定理：和与迭代版本等价（如果提供）
-- theorem sum_eq_iter_sum : recursive_sum list = list.sum := ...

-- ========== tail_factorial 验证 ==========

def fact_acc (n acc : U64) : U64 :=
  if n = 0 then
    acc
  else
    fact_acc (n - 1) (acc * n)

def tail_factorial (n : U64) : U64 :=
  fact_acc n 1

-- 定理：fact_acc 的正确性
theorem fact_acc_correct (n acc : U64) :
  fact_acc n acc = acc * factorial n := by
  induction n with
  | zero => 
    simp [fact_acc, factorial]
  | succ n ih =>
    simp [fact_acc, factorial, ih]
    ring

-- 定理：tail_factorial 计算阶乘
theorem tail_factorial_correct (n : U64) :
  tail_factorial n = factorial n := by
  simp [tail_factorial, fact_acc_correct]

-- ========== 二分查找验证 ==========

-- 假设：数组是有序的（前置条件）
def Sorted (arr : Slice I32) : Prop :=
  ∀ (i j : Nat), i < j → j < arr.length → arr[i] ≤ arr[j]

def recursive_binary_search 
  (arr : Slice I32) (target : I32) : Option Usize :=
  if arr.isEmpty then
    none
  else
    let mid := arr.length / 2
    if arr[mid] = target then
      some mid
    else if arr[mid] > target then
      recursive_binary_search (arr.take mid) target
    else
      recursive_binary_search (arr.drop (mid + 1)) target
      |>.map (fun i => i + mid + 1)

-- 定理：如果返回 Some i，则 arr[i] = target
theorem binary_search_found 
  (arr : Slice I32) (target : I32) (i : Usize) :
  Sorted arr →
  recursive_binary_search arr target = some i →
  i < arr.length ∧ arr[i] = target := by
  intro h_sorted h_found
  -- 对数组长度进行归纳
  induction arr using Slice.inductionOn with
  | empty => 
    simp [recursive_binary_search] at h_found
  | cons head tail ih =>
    simp [recursive_binary_search] at h_found
    split_ifs at h_found with h1 h2
    · -- 找到目标
      simp [h1]
    · -- 在左半部分搜索
      sorry -- 需要更多辅助引理
    · -- 在右半部分搜索
      sorry

-- 定理：如果目标在数组中，必定能找到
theorem binary_search_complete 
  (arr : Slice I32) (target : I32) (i : Usize) :
  Sorted arr →
  i < arr.length →
  arr[i] = target →
  ∃ j : Usize, recursive_binary_search arr target = some j := by
  sorry -- 完整证明

end Recursion
```

---

## 4. Miri 未定义行为检测

### 4.1 安装和运行

#### 4.1.1 安装 Miri

```bash
# 安装 Miri（需要 nightly Rust）
rustup component add miri

# 如果 nightly 未安装
rustup toolchain install nightly
rustup component add miri --toolchain nightly

# 验证安装
miri --version
```

#### 4.1.2 基本用法

```bash
# 运行单个文件
cargo miri run

# 运行测试
cargo miri test

# 运行特定测试
cargo miri test test_name

# 详细输出
cargo miri run -- --verbose

# 检查特定目标
cargo miri run --bin my_binary
```

#### 4.1.3 配置选项

```bash
# 环境变量配置

# 启用详细日志
MIRIFLAGS="-Zmiri-backtrace=full" cargo miri test

# 禁用隔离（允许文件系统/网络访问）
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri run

# 启用数据竞争检测
cargo miri test

# 设置树借用模式
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 多个标志组合
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-backtrace=full" cargo miri run
```

---

### 4.2 Stacked Borrows vs Tree Borrows

#### 4.2.1 两种别名模型的对比

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| **严格程度** | 更严格 | 更宽松 |
| **与 LLVM 对应** | 更接近 LLVM 优化假设 | 更灵活 |
| **误报率** | 较高 | 较低 |
| **验证通过率** | 较低 | 较高 |
| **推荐使用** | 严格验证场景 | 一般开发 |

#### 4.2.2 Stacked Borrows 示例

```rust
// stacked_borrows_example.rs

fn stacked_borrows_violation() {
    let mut x = 5;
    let y = &mut x;  // 创建可变引用
    let z = &mut *y; // 从 y 创建新的可变引用
    
    // 在 z 仍然有效时使用 y
    // 在 Stacked Borrows 下这是未定义行为
    *y = 10;  // 错误！y 被 z "弹出"了
    *z = 20;  // z 仍然有效
}

fn main() {
    stacked_borrows_violation();
}
```

```bash
# 使用 Stacked Borrows 运行（默认）
cargo miri run --example stacked_borrows

# 输出：
# error: Undefined Behavior: attempting to reborrow
# -> stacked_borrows_example.rs:10:5
```

#### 4.2.3 Tree Borrows 示例

```rust
// tree_borrows_example.rs

fn tree_borrows_ok() {
    let mut x = 5;
    let y = &mut x;  // 创建可变引用
    let z = &mut *y; // 从 y 创建新的可变引用
    
    // 在 Tree Borrows 下，这是允许的
    // y 和 z 被视为同一树的子节点
    *y = 10;  // OK in Tree Borrows
    *z = 20;  // OK
}

fn tree_borrows_violation() {
    let mut x = 5;
    let y = &x;      // 不可变借用
    let z = &mut x;  // 错误：不能与活跃的可变借用共存
    
    println!("{}", y);  // 使用 y
    *z = 10;
}

fn main() {
    tree_borrows_ok();
    // tree_borrows_violation();  // 这会报错
}
```

```bash
# 使用 Tree Borrows 运行
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri run --example tree_borrows
```

#### 4.2.4 选择合适的模型

```toml
# .cargo/config.toml
# 为项目配置默认 Miri 设置

[env]
MIRIFLAGS = "-Zmiri-tree-borrows -Zmiri-disable-isolation"
```

---

### 4.3 常见 UB 检测

#### 4.3.1 使用已释放内存

```rust
// use_after_free.rs

fn use_after_free() {
    let ptr: *const i32;
    {
        let x = 42;
        ptr = &x;  // ptr 指向局部变量
    }  // x 在这里被释放
    
    // 使用已释放的内存 - UB!
    unsafe {
        println!("{}", *ptr);  // Miri 会报错
    }
}

fn dangling_reference() -> &'static i32 {
    let x = 42;
    &x  // 错误：返回指向局部变量的引用
}

fn main() {
    use_after_free();
    // dangling_reference();
}
```

```bash
cargo miri run --example use_after_free

# 输出：
# error: Undefined Behavior: pointer to alloc1403 was dereferenced after this allocation got freed
```

#### 4.3.2 数据竞争

```rust
// data_race.rs
use std::thread;

fn data_race() {
    let mut x = 0;
    let ptr: *mut i32 = &mut x;
    
    thread::scope(|s| {
        s.spawn(|| unsafe {
            *ptr = 1;  // 线程 1 写入
        });
        s.spawn(|| unsafe {
            *ptr = 2;  // 线程 2 同时写入 - 数据竞争！
        });
    });
}

fn main() {
    data_race();
}
```

```bash
cargo miri run --example data_race

# 输出：
# error: Undefined Behavior: Data race detected
```

#### 4.3.3 未对齐访问

```rust
// unaligned_access.rs

fn unaligned_read() {
    let bytes: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    
    // 尝试从未对齐地址读取 u64
    let ptr = bytes.as_ptr().wrapping_add(1) as *const u64;
    
    unsafe {
        let val = *ptr;  // 未对齐读取 - UB！
        println!("{}", val);
    }
}

fn aligned_read() {
    let bytes: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    
    // 正确：从对齐地址读取
    let ptr = bytes.as_ptr() as *const u64;
    
    unsafe {
        // 确保对齐
        assert_eq!(ptr.align_offset(std::mem::align_of::<u64>()), 0);
        let val = *ptr;
        println!("{}", val);
    }
}

fn main() {
    // unaligned_read();
    aligned_read();
}
```

#### 4.3.4 越界访问

```rust
// out_of_bounds.rs

fn out_of_bounds_access() {
    let arr = [1, 2, 3];
    
    unsafe {
        // 越界读取
        let val = *arr.as_ptr().wrapping_add(10);  // Miri 报错
        println!("{}", val);
    }
}

fn buffer_overflow() {
    let mut buf = vec![0; 10];
    
    unsafe {
        std::ptr::write(buf.as_mut_ptr().wrapping_add(20), 42);  // 溢出！
    }
}

fn main() {
    // out_of_bounds_access();
    // buffer_overflow();
}
```

#### 4.3.5 无效枚举值

```rust
// invalid_enum.rs

#[repr(u8)]
enum Color {
    Red = 0,
    Green = 1,
    Blue = 2,
}

fn invalid_enum_value() {
    let val: u8 = 255;
    
    unsafe {
        let color: Color = std::mem::transmute(val);  // 无效值！
        match color {
            Color::Red => println!("Red"),
            Color::Green => println!("Green"),
            Color::Blue => println!("Blue"),
        }
    }
}

fn main() {
    invalid_enum_value();
}
```

---

### 4.4 与测试框架集成

#### 4.4.1 配置 Cargo.toml

```toml
# Cargo.toml

[package]
name = "my_project"
version = "0.1.0"
edition = "2021"

[dev-dependencies]
# 测试辅助库
proptest = "1.4"  # 属性测试

[[test]]
name = "miri_tests"
path = "tests/miri_tests.rs"
```

#### 4.4.2 编写 Miri 测试

```rust
// tests/miri_tests.rs

//! Miri 专用测试
//! 
//! 运行：cargo miri test

/// 测试内存安全
#[test]
fn test_safe_vec_operations() {
    let mut vec = Vec::with_capacity(10);
    
    for i in 0..10 {
        vec.push(i);
    }
    
    assert_eq!(vec.len(), 10);
    assert_eq!(vec.capacity(), 10);
}

/// 测试引用有效性
#[test]
fn test_reference_lifetime() {
    let data = vec![1, 2, 3, 4, 5];
    let sum: i32 = data.iter().sum();
    assert_eq!(sum, 15);
}

/// 测试并发（在 Miri 中顺序执行）
#[test]
fn test_concurrent_access() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    let counter = Arc::new(AtomicUsize::new(0));
    
    std::thread::scope(|s| {
        for _ in 0..4 {
            let c = Arc::clone(&counter);
            s.spawn(move || {
                c.fetch_add(1, Ordering::SeqCst);
            });
        }
    });
    
    assert_eq!(counter.load(Ordering::SeqCst), 4);
}

/// 测试 unsafe 代码块
#[test]
fn test_safe_unsafe_block() {
    let mut data = [1, 2, 3, 4, 5];
    
    // 安全的 unsafe 用法
    unsafe {
        let ptr = data.as_mut_ptr();
        *ptr.add(0) = 10;
        *ptr.add(1) = 20;
    }
    
    assert_eq!(data[0], 10);
    assert_eq!(data[1], 20);
}
```

#### 4.4.3 CI/CD 集成

```yaml
# .github/workflows/miri.yml
name: Miri Tests

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  miri:
    name: Miri Undefined Behavior Checks
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust nightly
        uses: dtolnay/rust-toolchain@nightly
        with:
          components: miri
      
      - name: Run Miri tests
        run: |
          cargo miri test --verbose
        env:
          MIRIFLAGS: "-Zmiri-tree-borrows -Zmiri-backtrace=short"
      
      - name: Run Miri on examples
        run: |
          cargo miri run --example basic
        env:
          MIRIFLAGS: "-Zmiri-disable-isolation"
```

---

## 5. 形式化验证策略

### 5.1 何时使用何种工具

#### 5.1.1 工具选择决策树

```
需要形式化验证？
├── 是 → 需要证明什么？
│   ├── 内存安全（无 UB）
│   │   ├── 快速检查 → Miri
│   │   └── 深度证明 → Aeneas + 定理证明器
│   ├── 安全属性（溢出、边界）
│   │   └── Kani 模型检查
│   ├── 并发正确性
│   │   ├── 数据竞争检测 → Miri
│   │   └── 协议验证 → Kani
│   └── 函数正确性
│       └── Aeneas + Lean/Coq
└── 否 → 传统测试
    ├── 单元测试
    ├── 集成测试
    └── 模糊测试
```

#### 5.1.2 各工具最佳场景

| 场景 | 推荐工具 | 替代工具 | 不推荐 |
|------|----------|----------|--------|
| **安全检查** | | | |
| 数组越界 | Kani | Miri | Aeneas |
| 整数溢出 | Kani | - | Miri |
| 内存泄漏 | Miri | - | Kani |
| 使用已释放 | Miri | - | - |
| 数据竞争 | Miri | Kani | - |
| **正确性证明** | | | |
| 算法正确性 | Aeneas | Kani | - |
| 状态机验证 | Kani | Aeneas | - |
| 协议实现 | Aeneas | Kani | - |
| **开发阶段** | | | |
| 开发期检查 | Miri | - | - |
| 代码审查前 | Kani | - | - |
| 发布前验证 | Aeneas | Kani | - |

---

### 5.2 验证覆盖度规划

#### 5.2.1 分级验证策略

```rust
// src/lib.rs

//! # 分级验证示例
//! 
//! ## Level 0: Miri 检查（每次提交）
//! - 确保无未定义行为
//! - 快速反馈
//! 
//! ## Level 1: Kani 验证（每次 PR）
//! - 安全属性验证
//! - 边界检查
//! 
//! ## Level 2: Aeneas 证明（关键模块）
//! - 函数正确性
//! - 数学性质证明

// ========== Level 0: 基础内存安全 ==========

pub struct SafeBuffer {
    data: Vec<u8>,
}

impl SafeBuffer {
    pub fn new(size: usize) -> Self {
        Self {
            data: vec![0; size],
        }
    }
    
    pub fn get(&self, index: usize) -> Option<u8> {
        self.data.get(index).copied()
    }
    
    pub fn set(&mut self, index: usize, value: u8) -> bool {
        if let Some(ptr) = self.data.get_mut(index) {
            *ptr = value;
            true
        } else {
            false
        }
    }
}

// ========== Level 1: Kani 安全验证 ==========

#[cfg(kani)]
mod kani_verification {
    use super::*;
    use kani::{proof, any, assume, assert};

    #[proof]
    #[kani::unwind(11)]
    fn verify_buffer_operations() {
        let size: usize = any();
        assume(size <= 10);
        
        let mut buf = SafeBuffer::new(size);
        let index: usize = any();
        let value: u8 = any();
        
        // 验证 get
        let result = buf.get(index);
        if index < size {
            assert_eq!(result, Some(0));
        } else {
            assert_eq!(result, None);
        }
        
        // 验证 set
        let success = buf.set(index, value);
        assert_eq!(success, index < size);
        
        if success {
            assert_eq!(buf.get(index), Some(value));
        }
    }
}

// ========== Level 2: Aeneas 正确性证明 ==========

/// 需要证明的复杂算法
/// 
/// 经过 Aeneas 转换后，在 Lean 中证明：
/// - 对于所有输入，输出满足规范
/// - 终止性
/// - 复杂度界限
pub fn complex_algorithm(input: &[i32]) -> Vec<i32> {
    // 复杂实现...
    input.to_vec()
}
```

#### 5.2.2 验证矩阵模板

| 模块 | Miri | Kani | Aeneas | 优先级 |
|------|------|------|--------|--------|
| 核心数据结构 | ✓ | ✓ | 可选 | 高 |
| 加密原语 | ✓ | ✓ | ✓ | 高 |
| 网络协议 | ✓ | ✓ | ✓ | 高 |
| 文件系统操作 | ✓ | ✓ | - | 中 |
| UI 代码 | ✓ | - | - | 低 |
| 测试代码 | ✓ | - | - | 低 |

---

### 5.3 与测试金字塔的关系

#### 5.3.1 扩展的验证金字塔

```
                    △
                   /  \
                  / E2E \
                 /  Test \
                /─────────\
               / Integration \
              /     Test      \
             /─────────────────\
            /     Unit Test     \
           /─────────────────────\
          /     Property Test     \
         /─────────────────────────\
        /       Fuzzing Test        \
       /─────────────────────────────\
      /         Miri (UB Check)        \
     /───────────────────────────────────\
    /        Kani (Safety Properties)      \
   /─────────────────────────────────────────\
  /       Aeneas (Functional Correctness)      \
 /─────────────────────────────────────────────────\
/               Formal Specification                  \
────────────────────────────────────────────────────────
```

#### 5.3.2 各层职责

| 层级 | 工具/方法 | 目的 | 频率 |
|------|-----------|------|------|
| **形式化规范** | 数学规范 | 定义正确性 | 设计时 |
| **函数正确性** | Aeneas | 证明实现符合规范 | 关键模块 |
| **安全属性** | Kani | 验证安全不变式 | 每次发布 |
| **UB 检测** | Miri | 检测未定义行为 | 每次提交 |
| **模糊测试** | cargo-fuzz | 发现边界情况 | 持续运行 |
| **属性测试** | proptest | 生成测试用例 | 每次构建 |
| **单元测试** | built-in | 验证具体行为 | 每次提交 |
| **集成测试** | built-in | 验证组合行为 | 每次 PR |
| **E2E 测试** | 自定义框架 | 验证完整流程 | 发布前 |

#### 5.3.3 投入比例建议

```
对于安全关键项目：
- 形式化验证: 30%（Kani + Aeneas）
- 动态检查: 20%（Miri + 测试）
- 传统测试: 50%

对于一般项目：
- 形式化验证: 10%（Kani 关键模块）
- 动态检查: 15%（Miri + 测试）
- 传统测试: 75%
```

---

## 6. 工具对比总结

### 6.1 功能对比

| 特性 | Kani | Aeneas | Miri |
|------|------|--------|------|
| **验证类型** | 模型检查 | 定理证明 | 动态分析 |
| **自动化** | 全自动 | 半自动 | 全自动 |
| **证明强度** | 属性验证 | 完全正确性 | UB 检测 |
| **Rust 支持** | 优秀 | 良好 | 完美 |
| **unsafe 支持** | 部分 | 有限 | 完整 |
| **并发支持** | 基础 | 有限 | 数据竞争检测 |
| **学习曲线** | 中等 | 陡峭 | 低 |
| **运行时间** | 中等 | 长（证明编写）| 快 |

### 6.2 适用场景对比

```markdown
### 安全关键系统（如密码学、航空航天）
- 推荐组合: Miri + Kani + Aeneas
- 投入比例: 40% 形式化, 60% 测试

### 系统编程（操作系统、嵌入式）
- 推荐组合: Miri + Kani
- 投入比例: 20% 形式化, 80% 测试

### 应用程序开发
- 推荐组合: Miri
- 投入比例: 5% 形式化, 95% 测试

### 开源库/框架
- 推荐组合: Miri + Kani（关键路径）
- 投入比例: 15% 形式化, 85% 测试
```

---

## 7. 参考资源

### 7.1 官方文档

| 资源 | 链接 | 描述 |
|------|------|------|
| **Kani 文档** | https://model-checking.github.io/kani/ | 完整的 Kani 用户指南 |
| **Kani GitHub** | https://github.com/model-checking/kani | 源码和问题跟踪 |
| **Aeneas 文档** | https://aeneasverif.github.io/aeneas/ | Aeneas 官方文档 |
| **Aeneas GitHub** | https://github.com/AeneasVerif/aeneas | 源码和示例 |
| **Charon GitHub** | https://github.com/AeneasVerif/charon | Rust 到 LLBC 转换器 |
| **Miri 文档** | https://github.com/rust-lang/miri | Miri README 和文档 |
| **Rust 不安全指南** | https://doc.rust-lang.org/nomicon/ | Rust 不安全代码指南 |

### 7.2 学术论文

1. **Kani/CBMC 相关**:
   - "Bounded Model Checking for Software" (Clarke et al.)
   - "The CBMC Bounded Model Checker" (Kroening & Tautschnig)

2. **Aeneas 相关**:
   - "Aeneas: Rust Verification by Functional Translation" (Ho & Protzenko)
   - "RustBelt: Securing the Foundations of the Rust Programming Language" (Jung et al.)

3. **Miri 相关**:
   - "Stacked Borrows: An Aliasing Model for Rust" (Jung et al.)
   - "Tree Borrows: A New Aliasing Model for Rust"

### 7.3 社区资源

- **Rust 形式化方法工作组**: https://rust-formal-methods.github.io/
- **Rust 安全工作组**: https://www.rust-lang.org/governance/wg-secure-code
- **Zulip 讨论**: https://rust-lang.zulipchat.com/#narrow/stream/269128-miri

### 7.4 示例项目

```bash
# Kani 示例
git clone https://github.com/model-checking/kani.git
cd kani/tests/kani

# Aeneas 示例
git clone https://github.com/AeneasVerif/aeneas.git
cd aeneas/tests

# Rust 形式化方法示例集合
git clone https://github.com/rust-formal-methods/rust-formal-methods.github.io.git
```

---

## 附录

### A. 常见错误速查表

| 错误 | 可能原因 | 解决方案 |
|------|----------|----------|
| **Kani: "unwinding assertion failed"** | 循环边界不足 | 增加 `#[kani::unwind(N)]` |
| **Kani: "out of memory"** | 状态空间爆炸 | 简化假设，减小输入范围 |
| **Aeneas: "unsupported feature"** | 使用不受支持的 Rust 特性 | 重写代码，避免该特性 |
| **Aeneas: "lifetime error"** | 借用检查失败 | 确保代码能通过 rustc |
| **Miri: "data race"** | 并发访问冲突 | 使用适当同步原语 |
| **Miri: "stacked borrows"** | 别名规则违反 | 使用 `-Zmiri-tree-borrows` 或重构代码 |

### B. 性能优化技巧

#### Kani 优化

```rust
// 1. 使用 kani::any_where 替代 assume
let x: u32 = kani::any_where(|x| *x < 100);  // 更高效

// 2. 限制输入范围
assume(len <= 10);  // 越小越好

// 3. 使用模块化验证
#[proof]
fn verify_small_component() { ... }  // 而非整个系统
```

#### Aeneas 优化

```rust
// 1. 简化类型
// 使用简单结构体而非复杂泛型

// 2. 减少 unsafe 代码
// Aeneas 对 safe Rust 支持更好

// 3. 分模块验证
// 将大文件拆分为小模块
```

#### Miri 优化

```bash
# 1. 只测试关键代码
cargo miri test --package critical_crate

# 2. 使用 Tree Borrows 减少误报
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test
```

---

> **文档版本**: 1.0.0  
> **最后更新**: 2026-02-28  
> **维护者**: Rust 形式化验证研究组  
> **反馈**: 欢迎通过 issue 提交改进建议

---

*本指南旨在提供 Rust 形式化验证工具的实际操作指南。随着工具的发展，部分内容可能需要更新。建议参考各工具的官方文档获取最新信息。*
