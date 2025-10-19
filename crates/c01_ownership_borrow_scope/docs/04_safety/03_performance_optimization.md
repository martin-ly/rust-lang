# 性能优化 - Performance Optimization

**版本**: 2.0  
**最后更新**: 2025-01-27  
**状态**: 完整版（已扩展）  

## 📋 目录

- [性能优化 - Performance Optimization](#性能优化---performance-optimization)
  - [📋 目录](#-目录)
  - [1. 零成本抽象深入](#1-零成本抽象深入)
    - [1.1 零成本抽象原理](#11-零成本抽象原理)
    - [1.2 迭代器优化](#12-迭代器优化)
    - [1.3 泛型单态化](#13-泛型单态化)
    - [1.4 内联优化](#14-内联优化)
  - [2. 内存分配优化](#2-内存分配优化)
    - [2.1 栈 vs 堆分配](#21-栈-vs-堆分配)
    - [2.2 智能指针选择](#22-智能指针选择)
    - [2.3 容器预分配](#23-容器预分配)
    - [2.4 自定义分配器](#24-自定义分配器)
    - [2.5 内存池技术](#25-内存池技术)
  - [3. 避免不必要的复制](#3-避免不必要的复制)
    - [3.1 使用借用](#31-使用借用)
    - [3.2 Cow 类型优化](#32-cow-类型优化)
    - [3.3 移动语义](#33-移动语义)
  - [4. 内存布局优化](#4-内存布局优化)
    - [4.1 结构体字段排序](#41-结构体字段排序)
    - [4.2 枚举优化](#42-枚举优化)
    - [4.3 缓存友好设计](#43-缓存友好设计)
  - [5. 性能分析工具](#5-性能分析工具)
    - [5.1 Cargo Flamegraph](#51-cargo-flamegraph)
    - [5.2 Criterion Benchmarking](#52-criterion-benchmarking)
    - [5.3 Perf 工具](#53-perf-工具)
    - [5.4 Valgrind 内存分析](#54-valgrind-内存分析)
  - [6. 编译优化](#6-编译优化)
    - [6.1 编译配置优化](#61-编译配置优化)
    - [6.2 LTO (Link Time Optimization)](#62-lto-link-time-optimization)
    - [6.3 PGO (Profile Guided Optimization)](#63-pgo-profile-guided-optimization)
    - [6.4 代码生成优化](#64-代码生成优化)
  - [7. 算法和数据结构优化](#7-算法和数据结构优化)
    - [7.1 容器选择](#71-容器选择)
    - [7.2 算法复杂度](#72-算法复杂度)
    - [7.3 并行算法](#73-并行算法)
  - [8. 实际优化案例](#8-实际优化案例)
    - [8.1 HTTP 服务器优化](#81-http-服务器优化)
    - [8.2 数据处理优化](#82-数据处理优化)
    - [8.3 JSON 解析优化](#83-json-解析优化)
  - [📚 总结](#-总结)
    - [1. 零成本抽象](#1-零成本抽象)
    - [2. 内存管理](#2-内存管理)
    - [3. 避免复制](#3-避免复制)
    - [4. 数据布局](#4-数据布局)
    - [5. 性能分析](#5-性能分析)
    - [6. 编译优化1](#6-编译优化1)
    - [7. 算法优化](#7-算法优化)
    - [性能优化流程](#性能优化流程)

## 1. 零成本抽象深入

### 1.1 零成本抽象原理

Rust 的零成本抽象意味着：你使用的抽象不会比手写的底层代码慢。

```rust
// 零成本抽象示例

// 高级抽象：使用迭代器
fn sum_with_iterator(data: &[i32]) -> i32 {
    data.iter().sum()
}

// 手写循环
fn sum_with_loop(data: &[i32]) -> i32 {
    let mut sum = 0;
    for &item in data {
        sum += item;
    }
    sum
}

// 编译后的汇编代码几乎相同！

// 验证零成本抽象
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_performance_equivalence() {
        let data: Vec<i32> = (0..1000).collect();
        
        // 两种方式性能相同
        assert_eq!(
            sum_with_iterator(&data),
            sum_with_loop(&data)
        );
    }
}
```

### 1.2 迭代器优化

迭代器链会被编译器优化为单次遍历。

```rust
// 迭代器优化示例

// ❌ 低效：多次遍历
fn inefficient_processing(data: &[i32]) -> Vec<i32> {
    let filtered: Vec<_> = data.iter()
        .filter(|&&x| x > 0)
        .collect();
    
    let doubled: Vec<_> = filtered.iter()
        .map(|&x| x * 2)
        .collect();
    
    doubled
}

// ✅ 高效：单次遍历
fn efficient_processing(data: &[i32]) -> Vec<i32> {
    data.iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .collect()
}

// 迭代器适配器的零成本
fn iterator_chain_optimization() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 复杂的迭代器链
    let result: Vec<_> = data.iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * x)
        .filter(|&x| x > 10)
        .take(3)
        .collect();
    
    // 编译器会优化为单次遍历
    println!("{:?}", result);
}

// 避免不必要的 collect
fn avoid_unnecessary_collect() {
    let data = vec![1, 2, 3, 4, 5];
    
    // ❌ 不必要的 collect
    let sum1: i32 = data.iter()
        .filter(|&&x| x > 2)
        .collect::<Vec<_>>()
        .iter()
        .sum();
    
    // ✅ 直接计算
    let sum2: i32 = data.iter()
        .filter(|&&x| x > 2)
        .sum();
}

// 迭代器 vs 索引访问
fn iterator_vs_index(data: &[i32]) -> i32 {
    // ✅ 推荐：使用迭代器
    data.iter().sum()
    
    // ⚠️ 索引访问可能较慢
    // let mut sum = 0;
    // for i in 0..data.len() {
    //     sum += data[i]; // 边界检查开销
    // }
    // sum
}
```

### 1.3 泛型单态化

Rust 的泛型在编译时进行单态化，生成特定类型的代码。

```rust
// 泛型单态化示例

// 泛型函数
fn generic_add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}

// 使用不同类型
fn monomorphization_example() {
    // 编译器为每种类型生成专门的代码
    let int_result = generic_add(1, 2);        // 生成 i32 版本
    let float_result = generic_add(1.0, 2.0);  // 生成 f64 版本
    let string_result = generic_add(
        String::from("Hello, "),
        String::from("World!")
    );  // 生成 String 版本
}

// 单态化的权衡
// 优点：运行时性能最优，无虚函数调用
// 缺点：增加二进制大小

// 控制二进制大小
#[inline(never)]  // 防止内联减少代码膨胀
fn large_generic_function<T: Clone>(value: T) -> T {
    // 大型函数体
    value.clone()
}

// 使用 trait 对象减少代码膨胀
fn use_trait_object() {
    // 单态化：每种类型一份代码
    fn process_generic<T: std::fmt::Display>(value: &T) {
        println!("{}", value);
    }
    
    // trait 对象：共享代码
    fn process_dynamic(value: &dyn std::fmt::Display) {
        println!("{}", value);
    }
    
    // 选择取决于性能需求
}
```

### 1.4 内联优化

内联可以消除函数调用开销。

```rust
// 内联优化示例

// 自动内联：小函数通常会自动内联
fn small_function(x: i32) -> i32 {
    x * 2
}

// 强制内联
#[inline(always)]
fn critical_function(x: i32) -> i32 {
    x + 1
}

// 建议内联
#[inline]
fn moderate_function(x: i32) -> i32 {
    x * x + x
}

// 禁止内联
#[inline(never)]
fn large_function(data: &[i32]) -> i32 {
    // 大型函数不应内联
    data.iter().sum()
}

// 内联的实际应用
struct Point {
    x: f64,
    y: f64,
}

impl Point {
    // 小方法应该内联
    #[inline]
    fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }
    
    // 计算密集的小方法
    #[inline]
    fn distance_squared(&self, other: &Point) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        dx * dx + dy * dy
    }
    
    // 复杂方法不内联
    #[inline(never)]
    fn complex_calculation(&self) -> f64 {
        // 复杂计算...
        self.x.sin() + self.y.cos()
    }
}

// 跨 crate 内联
// 需要在公共 API 上使用 #[inline]
#[inline]
pub fn public_hot_function(x: i32) -> i32 {
    x * 2
}
```

## 2. 内存分配优化

### 2.1 栈 vs 堆分配

栈分配比堆分配快得多。

```rust
// 栈 vs 堆分配示例

// ✅ 栈分配：快速
fn stack_allocation() {
    let array = [0; 100];  // 栈上分配
    // 自动释放，无分配器开销
}

// ⚠️ 堆分配：较慢
fn heap_allocation() {
    let vec = vec![0; 100];  // 堆上分配
    // 需要分配器调用，较慢
}

// 大对象使用 Box
fn large_object_on_heap() {
    // ❌ 栈溢出风险
    // let large_array = [0; 1_000_000];
    
    // ✅ 使用 Box 放在堆上
    let large_array = Box::new([0; 1_000_000]);
}

// 小对象优先栈分配
fn small_object_optimization() {
    // 小数组：栈分配
    let small = [0; 10];
    
    // 小结构体：栈分配
    struct SmallStruct {
        x: i32,
        y: i32,
    }
    let s = SmallStruct { x: 1, y: 2 };
}

// 避免不必要的 Box
fn avoid_unnecessary_box() {
    // ❌ 不必要的装箱
    fn bad_function(x: Box<i32>) {
        println!("{}", x);
    }
    
    // ✅ 直接传值
    fn good_function(x: i32) {
        println!("{}", x);
    }
}

// 栈分配的限制
const STACK_SIZE: usize = 8 * 1024 * 1024; // 通常 8MB

fn understand_stack_limits() {
    // ✅ 可以：小数组
    let small = [0u8; 1024];
    
    // ⚠️ 危险：大数组可能栈溢出
    // let large = [0u8; 10_000_000];
    
    // ✅ 安全：使用堆
    let large = vec![0u8; 10_000_000];
}
```

### 2.2 智能指针选择

选择合适的智能指针可以优化性能。

```rust
use std::rc::Rc;
use std::sync::Arc;

// 智能指针选择指南

// Box<T>: 单一所有权，无额外开销
fn use_box() {
    let data = Box::new(vec![1, 2, 3]);
    // 最轻量，只是堆分配
}

// Rc<T>: 单线程引用计数
fn use_rc() {
    let data = Rc::new(vec![1, 2, 3]);
    let data2 = Rc::clone(&data);
    // 引用计数，非原子操作，较快
}

// Arc<T>: 线程安全引用计数
fn use_arc() {
    let data = Arc::new(vec![1, 2, 3]);
    let data2 = Arc::clone(&data);
    // 原子引用计数，线程安全，稍慢
}

// 性能对比
use std::time::Instant;

fn compare_smart_pointers() {
    const N: usize = 1_000_000;
    
    // Box: 最快（无引用计数）
    let start = Instant::now();
    for _ in 0..N {
        let _ = Box::new(42);
    }
    println!("Box: {:?}", start.elapsed());
    
    // Rc: 中等（非原子引用计数）
    let start = Instant::now();
    let rc = Rc::new(42);
    for _ in 0..N {
        let _ = Rc::clone(&rc);
    }
    println!("Rc: {:?}", start.elapsed());
    
    // Arc: 较慢（原子引用计数）
    let start = Instant::now();
    let arc = Arc::new(42);
    for _ in 0..N {
        let _ = Arc::clone(&arc);
    }
    println!("Arc: {:?}", start.elapsed());
}

// 选择建议
// - 单一所有权 → Box<T>
// - 单线程共享 → Rc<T>
// - 多线程共享 → Arc<T>
// - 不可变数据 → Arc<T> 不需要 Mutex
// - 可变数据 → Arc<Mutex<T>> 或 Arc<RwLock<T>>
```

### 2.3 容器预分配

预分配容量可以避免多次重新分配。

```rust
// 容器预分配示例

// ❌ 低效：多次重新分配
fn without_preallocation() {
    let mut vec = Vec::new();
    for i in 0..1000 {
        vec.push(i);  // 可能触发多次重新分配
    }
}

// ✅ 高效：预分配容量
fn with_preallocation() {
    let mut vec = Vec::with_capacity(1000);
    for i in 0..1000 {
        vec.push(i);  // 不会重新分配
    }
}

// HashMap 预分配
use std::collections::HashMap;

fn hashmap_preallocation() {
    // ❌ 未预分配
    let mut map1 = HashMap::new();
    for i in 0..1000 {
        map1.insert(i, i * 2);
    }
    
    // ✅ 预分配
    let mut map2 = HashMap::with_capacity(1000);
    for i in 0..1000 {
        map2.insert(i, i * 2);
    }
}

// String 预分配
fn string_preallocation() {
    // ❌ 多次分配
    let mut s1 = String::new();
    for i in 0..100 {
        s1.push_str(&i.to_string());
    }
    
    // ✅ 预估容量
    let mut s2 = String::with_capacity(300);
    for i in 0..100 {
        s2.push_str(&i.to_string());
    }
}

// 性能测试
use std::time::Instant;

fn benchmark_preallocation() {
    const N: usize = 100_000;
    
    // 无预分配
    let start = Instant::now();
    let mut vec1 = Vec::new();
    for i in 0..N {
        vec1.push(i);
    }
    println!("Without capacity: {:?}", start.elapsed());
    
    // 有预分配
    let start = Instant::now();
    let mut vec2 = Vec::with_capacity(N);
    for i in 0..N {
        vec2.push(i);
    }
    println!("With capacity: {:?}", start.elapsed());
}
```

### 2.4 自定义分配器

Rust 支持自定义内存分配器。

```rust
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

// 自定义分配器：追踪内存使用
struct TrackingAllocator;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ret = System.alloc(layout);
        if !ret.is_null() {
            ALLOCATED.fetch_add(layout.size(), Ordering::SeqCst);
        }
        ret
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
        ALLOCATED.fetch_sub(layout.size(), Ordering::SeqCst);
    }
}

// 使用自定义分配器
#[global_allocator]
static GLOBAL: TrackingAllocator = TrackingAllocator;

// 查询内存使用
pub fn allocated_bytes() -> usize {
    ALLOCATED.load(Ordering::SeqCst)
}

// 其他分配器选择
// - jemalloc: 高性能通用分配器
// - mimalloc: Microsoft 的高性能分配器
// - tcmalloc: Google 的线程缓存分配器

// 使用 jemalloc 示例
// [dependencies]
// jemallocator = "0.5"

// use jemallocator::Jemalloc;
// #[global_allocator]
// static GLOBAL: Jemalloc = Jemalloc;
```

### 2.5 内存池技术

内存池可以减少分配开销。

```rust
// 简单的内存池实现

struct Pool<T> {
    items: Vec<Box<T>>,
}

impl<T> Pool<T> {
    fn new() -> Self {
        Self { items: Vec::new() }
    }
    
    fn with_capacity(capacity: usize) -> Self {
        Self {
            items: Vec::with_capacity(capacity),
        }
    }
    
    // 从池中获取
    fn acquire(&mut self) -> Box<T>
    where
        T: Default,
    {
        self.items.pop().unwrap_or_else(|| Box::new(T::default()))
    }
    
    // 归还到池中
    fn release(&mut self, item: Box<T>) {
        self.items.push(item);
    }
}

// 使用内存池
fn use_memory_pool() {
    let mut pool = Pool::<Vec<i32>>::with_capacity(10);
    
    // 获取对象
    let mut vec = pool.acquire();
    vec.push(1);
    vec.push(2);
    
    // 归还对象
    vec.clear();
    pool.release(vec);
    
    // 再次使用（重用已分配的内存）
    let vec2 = pool.acquire();
}

// 实际应用中推荐使用成熟的池库
// - typed-arena: 类型化内存池
// - bumpalo: bump 分配器
// - object-pool: 对象池
```

## 3. 避免不必要的复制

### 3.1 使用借用

借用避免了数据复制。

```rust
// 使用借用避免复制

// ❌ 不好：复制整个向量
fn bad_process(data: Vec<i32>) -> i32 {
    data.iter().sum()
    // data 被移动，调用者失去所有权
}

// ✅ 好：使用借用
fn good_process(data: &[i32]) -> i32 {
    data.iter().sum()
    // 只借用，无复制
}

// 字符串处理
fn string_processing() {
    let s = String::from("Hello, World!");
    
    // ❌ 不必要的克隆
    fn bad_print(s: String) {
        println!("{}", s);
    }
    // bad_print(s.clone());
    
    // ✅ 使用借用
    fn good_print(s: &str) {
        println!("{}", s);
    }
    good_print(&s);
}

// 返回值优化
fn return_value_optimization() {
    // ✅ 编译器优化：移动而非复制
    fn create_large_vec() -> Vec<i32> {
        vec![0; 1000]
        // 移动语义，无复制
    }
    
    let vec = create_large_vec();
}
```

### 3.2 Cow 类型优化

`Cow` (Clone on Write) 延迟克隆直到需要修改。

```rust
use std::borrow::Cow;

// Cow 类型优化示例

// 可能修改也可能不修改的函数
fn maybe_modify(s: &str) -> Cow<str> {
    if s.contains("bad") {
        // 需要修改：克隆
        Cow::Owned(s.replace("bad", "good"))
    } else {
        // 不需要修改：借用
        Cow::Borrowed(s)
    }
}

fn use_cow() {
    let s1 = "This is good";
    let result1 = maybe_modify(s1);
    // 无克隆，result1 借用 s1
    
    let s2 = "This is bad";
    let result2 = maybe_modify(s2);
    // 发生克隆，result2 拥有新字符串
}

// Cow 在配置中的应用
struct Config<'a> {
    name: Cow<'a, str>,
    path: Cow<'a, str>,
}

impl<'a> Config<'a> {
    // 接受借用或拥有的字符串
    fn new(name: impl Into<Cow<'a, str>>, path: impl Into<Cow<'a, str>>) -> Self {
        Self {
            name: name.into(),
            path: path.into(),
        }
    }
}

fn use_config() {
    // 使用静态字符串（无分配）
    let config1 = Config::new("app", "/usr/local/bin");
    
    // 使用 String（有分配）
    let name = String::from("my_app");
    let config2 = Config::new(name, "/usr/local/bin");
}

// Cow 用于 Vec
fn cow_with_vec() {
    let data = vec![1, 2, 3, 4, 5];
    
    fn maybe_modify_vec(v: &[i32]) -> Cow<[i32]> {
        if v.len() > 3 {
            // 需要修改
            let mut owned = v.to_vec();
            owned.truncate(3);
            Cow::Owned(owned)
        } else {
            // 不需要修改
            Cow::Borrowed(v)
        }
    }
    
    let result = maybe_modify_vec(&data);
}
```

### 3.3 移动语义

理解移动语义可以避免不必要的复制。

```rust
// 移动语义示例

// 移动 vs 复制
fn move_vs_copy() {
    // Copy 类型：自动复制
    let x = 42;
    let y = x;  // 复制
    println!("{} {}", x, y);  // x 仍然有效
    
    // Move 类型：移动所有权
    let s1 = String::from("hello");
    let s2 = s1;  // 移动
    // println!("{}", s1);  // ❌ 编译错误：s1 已被移动
    println!("{}", s2);
}

// 函数参数的移动
fn function_moves() {
    fn take_ownership(s: String) {
        println!("{}", s);
    }  // s 在这里被释放
    
    let s = String::from("hello");
    take_ownership(s);
    // s 已被移动，不能再使用
}

// 返回值的移动
fn return_moves() {
    fn give_ownership() -> String {
        String::from("hello")
    }  // 移动出函数
    
    let s = give_ownership();
    // s 拥有返回的 String
}

// 避免克隆的技巧
fn avoid_clone() {
    let mut data = vec![1, 2, 3];
    
    // ❌ 不必要的克隆
    fn bad_process(v: Vec<i32>) -> Vec<i32> {
        // 处理...
        v
    }
    // let result = bad_process(data.clone());
    
    // ✅ 使用借用
    fn good_process(v: &mut Vec<i32>) {
        v.push(4);
    }
    good_process(&mut data);
}
```

## 4. 内存布局优化

### 4.1 结构体字段排序

字段顺序影响内存使用和性能。

```rust
use std::mem;

// 结构体字段排序优化

// ❌ 低效：字段顺序不佳
struct BadLayout {
    a: u8,   // 1 byte
    b: u64,  // 8 bytes (需要 7 bytes 填充)
    c: u16,  // 2 bytes
    d: u32,  // 4 bytes
}

// ✅ 高效：按大小降序排列
struct GoodLayout {
    b: u64,  // 8 bytes
    d: u32,  // 4 bytes
    c: u16,  // 2 bytes
    a: u8,   // 1 byte
    // 总共 15 bytes + 1 byte 填充 = 16 bytes
}

fn compare_layouts() {
    println!("BadLayout size: {}", mem::size_of::<BadLayout>());   // 24 bytes
    println!("GoodLayout size: {}", mem::size_of::<GoodLayout>()); // 16 bytes
}

// 使用 repr 属性控制布局
#[repr(C)]  // C 语言兼容布局
struct CLayout {
    a: u8,
    b: u32,
}

#[repr(packed)]  // 紧凑布局（无填充）
struct PackedLayout {
    a: u8,
    b: u32,
}

#[repr(align(64))]  // 指定对齐
struct AlignedLayout {
    data: [u8; 32],
}

// 实际应用
struct OptimizedPoint {
    x: f64,  // 8 bytes
    y: f64,  // 8 bytes
    id: u32, // 4 bytes
    flags: u16, // 2 bytes
    _padding: [u8; 2], // 显式填充
}  // 总共 24 bytes，缓存行对齐友好
```

### 4.2 枚举优化

枚举的内存布局可以优化。

```rust
// 枚举优化示例

// ❌ 低效：大枚举变体
enum BadEnum {
    Small(u8),
    Large([u8; 1000]),  // 使整个枚举变大
}

// ✅ 高效：使用 Box 包装大变体
enum GoodEnum {
    Small(u8),
    Large(Box<[u8; 1000]>),  // 只存储指针
}

fn compare_enum_sizes() {
    use std::mem::size_of;
    
    println!("BadEnum: {} bytes", size_of::<BadEnum>());    // ~1008 bytes
    println!("GoodEnum: {} bytes", size_of::<GoodEnum>());  // ~16 bytes
}

// Option 优化
// Rust 对 Option<&T> 和 Option<Box<T>> 进行了优化
fn option_optimization() {
    use std::mem::size_of;
    
    // Option<&T> 和 &T 大小相同（使用空指针表示 None）
    println!("&i32: {}", size_of::<&i32>());        // 8 bytes
    println!("Option<&i32>: {}", size_of::<Option<&i32>>());  // 8 bytes
    
    // Option<Box<T>> 也类似
    println!("Box<i32>: {}", size_of::<Box<i32>>());  // 8 bytes
    println!("Option<Box<i32>>: {}", size_of::<Option<Box<i32>>>());  // 8 bytes
}

// 使用 NonNull 优化
use std::ptr::NonNull;

enum OptimizedEnum<T> {
    None,
    Some(NonNull<T>),  // 保证非空
}
```

### 4.3 缓存友好设计

考虑 CPU 缓存的数据布局。

```rust
// 缓存友好设计

// ❌ 缓存不友好：AoS (Array of Structs)
struct ParticleAoS {
    x: f32,
    y: f32,
    z: f32,
    vx: f32,
    vy: f32,
    vz: f32,
}

fn update_aos(particles: &mut [ParticleAoS]) {
    for p in particles {
        p.x += p.vx;  // 跳跃访问内存
        p.y += p.vy;
        p.z += p.vz;
    }
}

// ✅ 缓存友好：SoA (Struct of Arrays)
struct ParticlesSoA {
    x: Vec<f32>,
    y: Vec<f32>,
    z: Vec<f32>,
    vx: Vec<f32>,
    vy: Vec<f32>,
    vz: Vec<f32>,
}

fn update_soa(particles: &mut ParticlesSoA) {
    let len = particles.x.len();
    for i in 0..len {
        particles.x[i] += particles.vx[i];  // 连续内存访问
        particles.y[i] += particles.vy[i];
        particles.z[i] += particles.vz[i];
    }
}

// 混合方式：小结构体分组
struct ParticleGroup {
    positions: Vec<[f32; 3]>,  // xyz 组
    velocities: Vec<[f32; 3]>, // vxvyvz 组
}

// 缓存行对齐
const CACHE_LINE_SIZE: usize = 64;

#[repr(align(64))]
struct CacheAligned {
    data: [u8; 64],
}

// 避免伪共享
#[repr(align(64))]
struct PaddedCounter {
    value: std::sync::atomic::AtomicUsize,
    _padding: [u8; 64 - std::mem::size_of::<std::sync::atomic::AtomicUsize>()],
}
```

## 5. 性能分析工具

### 5.1 Cargo Flamegraph

生成火焰图分析性能瓶颈。

```bash
# 安装 cargo-flamegraph
cargo install flamegraph

# 生成火焰图
cargo flamegraph --bin my_app

# 带参数运行
cargo flamegraph --bin my_app -- --input data.txt

# 指定输出文件
cargo flamegraph --output my-flamegraph.svg
```

```rust
// 示例：性能分析目标代码
fn heavy_computation() {
    let mut sum = 0;
    for i in 0..1_000_000 {
        sum += expensive_function(i);
    }
    println!("Sum: {}", sum);
}

fn expensive_function(n: i32) -> i32 {
    // 模拟耗时操作
    (0..100).map(|x| x * n).sum()
}

fn main() {
    heavy_computation();
}
```

### 5.2 Criterion Benchmarking

精确的性能基准测试。

```rust
// Cargo.toml
// [dev-dependencies]
// criterion = "0.5"

use criterion::{black_box, criterion_group, criterion_main, Criterion};

// 基准测试函数
fn fibonacci_recursive(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci_recursive(n - 1) + fibonacci_recursive(n - 2),
    }
}

fn fibonacci_iterative(n: u64) -> u64 {
    let mut a = 0;
    let mut b = 1;
    for _ in 0..n {
        let temp = a;
        a = b;
        b = temp + b;
    }
    a
}

// 基准测试
fn fibonacci_benchmark(c: &mut Criterion) {
    c.bench_function("fibonacci recursive 20", |b| {
        b.iter(|| fibonacci_recursive(black_box(20)))
    });

    c.bench_function("fibonacci iterative 20", |b| {
        b.iter(|| fibonacci_iterative(black_box(20)))
    });
}

criterion_group!(benches, fibonacci_benchmark);
criterion_main!(benches);

// 运行基准测试
// cargo bench
```

### 5.3 Perf 工具

Linux 上的性能分析工具。

```bash
# 记录性能数据
perf record --call-graph=dwarf cargo run --release

# 查看报告
perf report

# CPU 缓存分析
perf stat -e cache-references,cache-misses cargo run --release

# 分支预测分析
perf stat -e branches,branch-misses cargo run --release
```

### 5.4 Valgrind 内存分析

分析内存使用和缓存性能。

```bash
# 安装 valgrind
# Linux: sudo apt-get install valgrind
# macOS: brew install valgrind

# 内存泄漏检查
valgrind --leak-check=full --show-leak-kinds=all ./target/release/my_app

# 缓存性能分析
valgrind --tool=cachegrind ./target/release/my_app

# 调用图分析
valgrind --tool=callgrind ./target/release/my_app
```

## 6. 编译优化

### 6.1 编译配置优化

优化 Cargo.toml 中的编译配置。

```toml
# Cargo.toml

[profile.release]
# 优化级别
opt-level = 3         # 0-3, s(size), z(size aggressive)

# LTO (Link Time Optimization)
lto = true            # 或 "thin" 或 "fat"

# 代码生成单元
codegen-units = 1     # 减少单元提升优化（增加编译时间）

# 调试信息
debug = false         # 减小二进制大小

# 溢出检查
overflow-checks = false  # 禁用整数溢出检查（提升性能）

# panic 策略
panic = 'abort'       # 使用 abort 而非 unwind

# Strip 符号
strip = true          # 移除符号信息

# 增量编译
incremental = false   # release 构建禁用增量编译

[profile.release.package."*"]
# 优化依赖项
opt-level = 3

# 开发配置
[profile.dev]
opt-level = 1         # 轻度优化，加快编译
incremental = true    # 启用增量编译

# 自定义 profile
[profile.bench]
inherits = "release"
debug = true          # 保留调试信息用于性能分析
```

### 6.2 LTO (Link Time Optimization)

链接时优化可以显著提升性能。

```toml
# Cargo.toml

[profile.release]
# Thin LTO：较快，适度优化
lto = "thin"

# Fat LTO：较慢，最大优化
# lto = "fat"  # 或 lto = true
```

```rust
// LTO 能够：
// 1. 内联跨 crate 的函数
// 2. 消除死代码
// 3. 优化函数调用
// 4. 常量传播

// 示例：跨 crate 内联
// lib.rs
#[inline]
pub fn hot_function(x: i32) -> i32 {
    x * 2
}

// main.rs
use my_lib::hot_function;

fn main() {
    let result = hot_function(21);
    // 启用 LTO 后，hot_function 可能被内联
}
```

### 6.3 PGO (Profile Guided Optimization)

基于运行时数据的优化。

```bash
# 步骤 1: 构建插桩版本
RUSTFLAGS="-Cprofile-generate=/tmp/pgo-data" \
cargo build --release

# 步骤 2: 运行程序收集数据
./target/release/my_app

# 步骤 3: 使用收集的数据重新构建
RUSTFLAGS="-Cprofile-use=/tmp/pgo-data/merged.profdata" \
cargo build --release
```

### 6.4 代码生成优化

```toml
# Cargo.toml

[profile.release]
# 目标 CPU
# native: 针对当前 CPU 优化
# 特定 CPU: "haswell", "skylake" 等
# target-cpu = "native"

# 目标特性
# target-features = "+avx2,+fma"
```

```rust
// CPU 特性检测
#[cfg(target_feature = "avx2")]
fn optimized_version() {
    // AVX2 优化版本
}

#[cfg(not(target_feature = "avx2"))]
fn fallback_version() {
    // 通用版本
}

// 运行时特性检测
fn runtime_dispatch() {
    if is_x86_feature_detected!("avx2") {
        // 使用 AVX2
    } else {
        // 使用通用实现
    }
}
```

## 7. 算法和数据结构优化

### 7.1 容器选择

选择合适的容器对性能至关重要。

```rust
use std::collections::{Vec, VecDeque, LinkedList, HashMap, BTreeMap, HashSet, BTreeSet};

// 容器选择指南

// Vec<T>: 默认选择
// - 顺序访问: O(1)
// - 随机访问: O(1)
// - 尾部插入/删除: 摊销 O(1)
// - 中间插入/删除: O(n)
fn use_vec() {
    let mut vec = Vec::new();
    vec.push(1);        // O(1)
    vec.push(2);
    let x = vec[0];     // O(1)
    vec.pop();          // O(1)
}

// VecDeque<T>: 双端队列
// - 两端插入/删除: O(1)
// - 随机访问: O(1)
fn use_vecdeque() {
    let mut deque = VecDeque::new();
    deque.push_front(1);  // O(1)
    deque.push_back(2);   // O(1)
}

// LinkedList<T>: 链表（通常不推荐）
// - 插入/删除: O(1) (如果有迭代器)
// - 查找: O(n)
// - 内存开销大
fn use_linkedlist() {
    let mut list = LinkedList::new();
    list.push_back(1);
    // 通常 Vec 或 VecDeque 更快
}

// HashMap<K, V>: 哈希表
// - 插入/查找/删除: 平均 O(1)
// - 无序
fn use_hashmap() {
    let mut map = HashMap::new();
    map.insert("key", "value");  // 平均 O(1)
    map.get("key");              // 平均 O(1)
}

// BTreeMap<K, V>: B树
// - 插入/查找/删除: O(log n)
// - 有序
// - 范围查询高效
fn use_btreemap() {
    let mut map = BTreeMap::new();
    map.insert(1, "one");
    map.range(1..10);  // 范围查询
}

// 性能对比建议
// - 小数据量(<100): Vec 几乎总是最快
// - 需要快速随机访问: Vec
// - 需要快速插入/删除: HashMap 或 HashSet
// - 需要排序: BTreeMap 或 BTreeSet
// - 需要范围查询: BTreeMap
```

### 7.2 算法复杂度

选择正确的算法复杂度。

```rust
// 算法复杂度优化

// ❌ O(n²): 嵌套循环
fn find_duplicates_slow(data: &[i32]) -> Vec<i32> {
    let mut duplicates = Vec::new();
    for i in 0..data.len() {
        for j in (i + 1)..data.len() {
            if data[i] == data[j] {
                duplicates.push(data[i]);
                break;
            }
        }
    }
    duplicates
}

// ✅ O(n): 使用 HashSet
use std::collections::HashSet;

fn find_duplicates_fast(data: &[i32]) -> Vec<i32> {
    let mut seen = HashSet::new();
    let mut duplicates = HashSet::new();
    
    for &item in data {
        if !seen.insert(item) {
            duplicates.insert(item);
        }
    }
    
    duplicates.into_iter().collect()
}

// 排序算法选择
fn sorting_algorithms() {
    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
    
    // 快速排序（不稳定）
    data.sort_unstable();  // 通常最快
    
    // 归并排序（稳定）
    data.sort();           // 稍慢但稳定
    
    // 部分排序
    data.select_nth_unstable(3);  // 只排序到第 k 个元素
}

// 二分查找
fn binary_search_example() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    
    // O(log n)
    match data.binary_search(&5) {
        Ok(index) => println!("Found at {}", index),
        Err(index) => println!("Not found, would be at {}", index),
    }
}
```

### 7.3 并行算法

使用并行计算提升性能。

```rust
// 使用 rayon 进行并行计算
// Cargo.toml: rayon = "1.7"

use rayon::prelude::*;

// 并行迭代
fn parallel_iteration() {
    let data: Vec<i32> = (0..1_000_000).collect();
    
    // 串行
    let sum1: i32 = data.iter().sum();
    
    // 并行
    let sum2: i32 = data.par_iter().sum();
}

// 并行映射
fn parallel_map() {
    let data: Vec<i32> = (0..1_000_000).collect();
    
    // 串行
    let squares1: Vec<i32> = data.iter()
        .map(|&x| x * x)
        .collect();
    
    // 并行
    let squares2: Vec<i32> = data.par_iter()
        .map(|&x| x * x)
        .collect();
}

// 并行过滤
fn parallel_filter() {
    let data: Vec<i32> = (0..1_000_000).collect();
    
    let evens: Vec<i32> = data.par_iter()
        .filter(|&&x| x % 2 == 0)
        .copied()
        .collect();
}

// 并行排序
fn parallel_sort() {
    let mut data: Vec<i32> = (0..1_000_000).rev().collect();
    data.par_sort_unstable();
}
```

## 8. 实际优化案例

### 8.1 HTTP 服务器优化

```rust
// HTTP 服务器性能优化技巧

// 1. 连接池
// use r2d2 或 deadpool

// 2. 异步 I/O
use tokio;

#[tokio::main]
async fn async_server() {
    // 使用 tokio 异步运行时
}

// 3. 零复制
use bytes::Bytes;

fn zero_copy_response(data: Bytes) -> Bytes {
    // Bytes 支持零复制共享
    data
}

// 4. 缓存
use std::sync::Arc;
use std::collections::HashMap;

struct Cache {
    data: Arc<HashMap<String, String>>,
}

// 5. 批处理
async fn batch_requests(requests: Vec<Request>) {
    // 批量处理减少往返
}
```

### 8.2 数据处理优化

```rust
// 数据处理优化案例

use std::time::Instant;

// ❌ 低效：多次遍历
fn inefficient_data_processing(data: &[i32]) -> i32 {
    let filtered: Vec<_> = data.iter()
        .filter(|&&x| x > 0)
        .collect();
    
    let doubled: Vec<_> = filtered.iter()
        .map(|&x| x * 2)
        .collect();
    
    let sum: i32 = doubled.iter().sum();
    sum
}

// ✅ 高效：单次遍历
fn efficient_data_processing(data: &[i32]) -> i32 {
    data.iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .sum()
}

// 性能对比
fn benchmark_data_processing() {
    let data: Vec<i32> = (-1000..1000).collect();
    
    let start = Instant::now();
    let result1 = inefficient_data_processing(&data);
    println!("Inefficient: {:?}", start.elapsed());
    
    let start = Instant::now();
    let result2 = efficient_data_processing(&data);
    println!("Efficient: {:?}", start.elapsed());
    
    assert_eq!(result1, result2);
}

// 并行数据处理
use rayon::prelude::*;

fn parallel_data_processing(data: &[i32]) -> i32 {
    data.par_iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .sum()
}
```

### 8.3 JSON 解析优化

```rust
// JSON 解析性能优化

// 使用 serde_json
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Data {
    id: u64,
    name: String,
    values: Vec<i32>,
}

// 1. 流式解析大文件
fn stream_parse_json() {
    // use serde_json::Deserializer;
    // let reader = std::fs::File::open("large.json").unwrap();
    // let stream = Deserializer::from_reader(reader).into_iter::<Data>();
    
    // for value in stream {
    //     // 逐个处理，不会全部加载到内存
    // }
}

// 2. 使用 simd-json 加速
// Cargo.toml: simd-json = "0.13"

// 3. 避免不必要的字符串分配
#[derive(Deserialize)]
struct BorrowedData<'a> {
    #[serde(borrow)]
    name: &'a str,  // 借用而非分配
}

// 4. 使用 Value 进行部分解析
use serde_json::Value;

fn partial_parse(json_str: &str) {
    let v: Value = serde_json::from_str(json_str).unwrap();
    // 只访问需要的字段
    if let Some(name) = v["name"].as_str() {
        println!("{}", name);
    }
}
```

## 📚 总结

Rust 性能优化的关键原则：

### 1. 零成本抽象

- 使用迭代器而非手写循环
- 利用编译器优化
- 理解单态化

### 2. 内存管理

- 优先栈分配
- 预分配容器容量
- 选择合适的智能指针
- 使用内存池

### 3. 避免复制

- 使用借用
- 利用 Cow 类型
- 理解移动语义

### 4. 数据布局

- 优化结构体字段顺序
- 使用 Box 包装大枚举
- 缓存友好设计

### 5. 性能分析

- 使用 flamegraph 找瓶颈
- 用 criterion 精确测试
- Linux 上使用 perf

### 6. 编译优化1

- 配置 release profile
- 启用 LTO
- 考虑 PGO

### 7. 算法优化

- 选择合适的容器
- 降低算法复杂度
- 使用并行计算

### 性能优化流程

1. **测量**: 先测量，找出瓶颈
2. **优化**: 针对瓶颈优化
3. **验证**: 再次测量验证效果
4. **重复**: 持续改进

---

**相关文档**：

- [性能调优](../05_practice/04_performance_tuning.md)
- [内存安全保证](./01_memory_safety.md)
- [并发安全](./02_concurrency_safety.md)

**最后更新**: 2025年1月27日  
**维护状态**: 活跃维护中  
**质量等级**: 完整版
