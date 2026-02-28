# Rust 反模式速查卡

> **用途**: 汇总 Rust 开发中的常见反模式、错误示例及避免策略
> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [Rust 反模式速查卡](#rust-反模式速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [一、模板结构](#一模板结构)
  - [二、反例数量建议](#二反例数量建议)
  - [示例：所有权反例](#示例所有权反例)
    - [反例 1: 移动后使用](#反例-1-移动后使用)
    - [反例 2: 可变借用与不可变借用冲突](#反例-2-可变借用与不可变借用冲突)
  - [四、并发反模式](#四并发反模式)
    - [反例 4: Rc 跨线程](#反例-4-rc-跨线程)
    - [反例 5: 共享可变无同步](#反例-5-共享可变无同步)
  - [五、类型系统反模式](#五类型系统反模式)
    - [反例 6: 过度泛型](#反例-6-过度泛型)
    - [反例 7: 孤儿规则违反](#反例-7-孤儿规则违反)
  - [六、异步编程反模式](#六异步编程反模式)
    - [反例 8: 在 async 中持有同步锁](#反例-8-在-async-中持有同步锁)
    - [反例 9: 忘记 await](#反例-9-忘记-await)
  - [七、错误处理反模式](#七错误处理反模式)
    - [反例 10: 滥用 unwrap](#反例-10-滥用-unwrap)
    - [反例 11: 空错误信息](#反例-11-空错误信息)
  - [八、性能反模式](#八性能反模式)
    - [反例 12: 不必要的克隆](#反例-12-不必要的克隆)
    - [反例 13: 过度使用 Box](#反例-13-过度使用-box)
  - [九、设计模式误用](#九设计模式误用)
    - [反例 14: 单产品却用 Abstract Factory](#反例-14-单产品却用-abstract-factory)
    - [反例 15: 错误使用 Singleton](#反例-15-错误使用-singleton)
  - [十、边界情况处理](#十边界情况处理)
    - [反例 16: 忽略空输入](#反例-16-忽略空输入)
    - [反例 17: 整数溢出](#反例-17-整数溢出)
  - [十一、规避策略总结](#十一规避策略总结)
  - [十二、形式化方法链接](#十二形式化方法链接)
    - [理论基础](#理论基础)
    - [形式化定义](#形式化定义)
  - [编译失败测试（compile\_fail）](#编译失败测试compile_fail)
  - [速查卡清单（已补全反例 2026-02-12）](#速查卡清单已补全反例-2026-02-12)
  - [十四、完整示例：场景 → 反模式 → 正确写法](#十四完整示例场景--反模式--正确写法)
    - [场景 1: 需要共享可变状态](#场景-1-需要共享可变状态)
    - [场景 2: 缓存全局配置](#场景-2-缓存全局配置)
    - [场景 3: 构建复杂对象](#场景-3-构建复杂对象)
    - [场景 4: 处理可能失败的操作](#场景-4-处理可能失败的操作)
    - [场景 5: 频繁字符串拼接](#场景-5-频繁字符串拼接)

---

---

## 一、模板结构

每个速查卡的反例速查小节应包含以下结构：

```markdown
        ## 反例速查

        ### 反例 1: [简短描述]

        **错误示例**:

        ```rust
        // ❌ 错误代码
        ```

        **原因**: [1-2 句话说明为什么错误]

        **修正**:

        ```rust
        // ✅ 正确做法
        ```

        ---

        ### 反例 2: [简短描述]

        （同上结构）

        ---

        ### 反例 N: [简短描述]

        （同上结构）

```

**完整结构要求**:

1. **错误示例**: 可编译/运行的错误代码
2. **原因分析**: 解释为何是错误的
3. **修正代码**: 正确的实现方式
4. **形式化说明**: 链接到对应的形式化规则

---

## 二、反例数量建议

| 速查卡类型 | 建议反例数 | 说明 |
| :--- | :--- | :--- |
| 核心概念（所有权、类型、错误处理） | 3-5 | 常见陷阱多 |
| 进阶主题（泛型、异步、宏） | 2-4 | 聚焦典型错误 |
| 工具/环境（Cargo、测试） | 2-3 | 配置与用法 |
| 其他 | 2-3 | 根据主题 |

---

## 示例：所有权反例

### 反例 1: 移动后使用

**错误示例**:

```rust
let s = String::from("hello");
let s2 = s;  // 所有权转移
println!("{}", s);  // ❌ 编译错误：s 已失效
```

**原因**: 值移动后原变量不可用。

**修正**:

```rust
let s = String::from("hello");
let s2 = s.clone();  // 或借用 &s
println!("{}", s);
```

---

### 反例 2: 可变借用与不可变借用冲突

**错误示例**:

```rust
let mut v = vec![1, 2, 3];
let r1 = &v;
let r2 = &mut v;  // ❌ 编译错误：已有不可变借用
```

**原因**: 同一时刻不能同时存在可变借用和不可变借用。

**修正**:

```rust
let mut v = vec![1, 2, 3];
let r1 = &v;
// 使用 r1 后再借出 r2
let r2 = &mut v;
```

---

## 四、并发反模式

### 反例 4: Rc 跨线程

**错误示例**:

```rust
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);
    let data_clone = data.clone();

    thread::spawn(move || {  // ❌ 编译错误
        println!("{}", data_clone);
    });
}
```

**原因**: `Rc` 不是 `Send`，跨线程会导致数据竞争，违反 [send_sync_formalization](../../research_notes/formal_methods/send_sync_formalization.md) 定义。

**修正**:

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(42);  // ✅ 使用 Arc
    let data_clone = Arc::clone(&data);

    thread::spawn(move || {
        println!("{}", data_clone);
    }).join().unwrap();
}
```

---

### 反例 5: 共享可变无同步

**错误示例**:

```rust
use std::thread;

fn main() {
    let mut data = vec![1, 2, 3];

    for i in 0..3 {
        thread::spawn(move {  // ❌ 编译错误
            data[i] += 1;
        });
    }
}
```

**原因**: 多线程共享可变数据需要同步原语。

**修正**:

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));

    let mut handles = vec![];
    for i in 0..3 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move {
            let mut guard = data.lock().unwrap();
            guard[i] += 1;
        }));
    }

    for h in handles { h.join().unwrap(); }
}
```

---

## 五、类型系统反模式

### 反例 6: 过度泛型

**错误示例**:

```rust
// ❌ 过度泛型导致代码难以理解
fn process<A, B, C, D, E, F>(a: A, b: B, c: C) -> D
where
    A: IntoIterator<Item = B>,
    B: AsRef<[C]>,
    C: Clone + Default,
    D: FromIterator<E>,
    E: From<F>,
    F: From<C>,
{
    a.into_iter()
        .flat_map(|x| x.as_ref().iter().cloned())
        .map(|c| E::from(F::from(c)))
        .collect()
}
```

**原因**: 过度抽象导致代码难以理解和维护。

**修正**:

```rust
// ✅ 具体类型优先，按需抽象
fn process(data: Vec<Vec<i32>>) -> Vec<i32> {
    data.into_iter()
        .flat_map(|v| v)
        .collect()
}

// 需要泛型时再提取
fn flatten<T>(nested: Vec<Vec<T>>) -> Vec<T> {
    nested.into_iter().flat_map(|v| v).collect()
}
```

---

### 反例 7: 孤儿规则违反

**错误示例**:

```rust
// 在本地 crate 中为外部类型实现外部 trait
impl serde::Serialize for chrono::DateTime<chrono::Utc> {
    // ❌ 编译错误：孤儿规则
}
```

**原因**: Rust 的孤儿规则防止 trait 实现冲突。

**修正**:

```rust
// ✅ 使用 newtype 模式
#[derive(Debug)]
struct MyDateTime(chrono::DateTime<chrono::Utc>);

impl serde::Serialize for MyDateTime {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}
```

---

## 六、异步编程反模式

### 反例 8: 在 async 中持有同步锁

**错误示例**:

```rust
use std::sync::Mutex;

async fn bad() {
    let data = Mutex::new(42);
    let guard = data.lock().unwrap();
    some_async_fn().await;  // ❌ 问题：锁跨 await 点
    drop(guard);
}
```

**原因**: 同步锁跨越 await 点会导致线程阻塞，降低并发性能。

**修正**:

```rust
use tokio::sync::Mutex;  // ✅ 使用异步锁

async fn good() {
    let data = Mutex::new(42);
    {
        let guard = data.lock().await;
        // 使用数据
    }  // 锁在这里释放
    some_async_fn().await;
}
```

---

### 反例 9: 忘记 await

**错误示例**:

```rust
async fn fetch_data() -> String {
    "data".to_string()
}

async fn main() {
    let data = fetch_data();  // ❌ 忘记 await
    println!("{}", data);     // 输出: "...Future"
}
```

**原因**: 异步函数返回 Future，需要 await 才能执行。

**修正**:

```rust
async fn main() {
    let data = fetch_data().await;  // ✅ 正确 await
    println!("{}", data);
}
```

---

## 七、错误处理反模式

### 反例 10: 滥用 unwrap

**错误示例**:

```rust
fn risky_function(path: &str) -> String {
    let content = std::fs::read_to_string(path).unwrap();  // ❌ 可能 panic
    content.to_uppercase()
}
```

**原因**: 生产代码中使用 unwrap 会导致程序崩溃。

**修正**:

```rust
fn safe_function(path: &str) -> Result<String, std::io::Error> {
    let content = std::fs::read_to_string(path)?;  // ✅ 传播错误
    Ok(content.to_uppercase())
}
```

---

### 反例 11: 空错误信息

**错误示例**:

```rust
fn parse_number(s: &str) -> Result<i32, String> {
    s.parse().map_err(|_| "error".to_string())  // ❌ 无意义错误信息
}
```

**原因**: 空泛的错误信息难以调试。

**修正**:

```rust
fn parse_number(s: &str) -> Result<i32, String> {
    s.parse().map_err(|e| format!("Failed to parse '{}': {}", s, e))
}
```

---

## 八、性能反模式

### 反例 12: 不必要的克隆

**错误示例**:

```rust
fn process(data: &Vec<String>) -> Vec<String> {
    data.iter()
        .map(|s| s.clone())  // ❌ 不必要的克隆
        .filter(|s| !s.is_empty())
        .collect()
}
```

**原因**: 频繁克隆会消耗内存和 CPU。

**修正**:

```rust
fn process(data: &[String]) -> impl Iterator<Item = &String> {
    data.iter().filter(|s| !s.is_empty())  // ✅ 返回引用迭代器
}

// 或返回新集合但不克隆每个元素
fn process_owned(data: Vec<String>) -> Vec<String> {
    data.into_iter().filter(|s| !s.is_empty()).collect()
}
```

---

### 反例 13: 过度使用 Box

**错误示例**:

```rust
struct BadData {
    value: Box<i32>,      // ❌ 不必要
    name: Box<String>,    // ❌ 不必要
    items: Box<Vec<i32>>, // ❌ 不必要
}
```

**原因**: 小类型使用 Box 会增加间接访问开销。

**修正**:

```rust
struct GoodData {
    value: i32,
    name: String,      // String 本身已堆分配
    items: Vec<i32>,   // Vec 本身已堆分配
}
```

---

## 九、设计模式误用

### 反例 14: 单产品却用 Abstract Factory

**错误示例**:

```rust
// ❌ 过度设计：只有一种按钮却定义产品族
trait ButtonFactory {
    fn create_button(&self) -> Box<dyn Button>;
    fn create_checkbox(&self) -> Box<dyn Checkbox>;
}

struct WindowsFactory;
impl ButtonFactory for WindowsFactory { ... }

// 但实际上只有一种 WindowsButton
```

**原因**: 简单场景使用复杂模式是过度设计。

**修正**:

```rust
// ✅ 简单工厂或直接使用构造函数
struct Button {
    label: String,
}

impl Button {
    fn new(label: &str) -> Self {
        Self { label: label.to_string() }
    }
}
```

---

### 反例 15: 错误使用 Singleton

**错误示例**:

```rust
// ❌ 全局可变状态
static mut CONFIG: Option<Config> = None;

fn get_config() -> &'static mut Config {
    unsafe {
        CONFIG.get_or_insert_with(|| Config::default())
    }
}
```

**原因**: 全局可变状态不安全，易导致数据竞争。

**修正**:

```rust
// ✅ 使用 std::sync::OnceLock
use std::sync::OnceLock;

static CONFIG: OnceLock<Config> = OnceLock::new();

fn get_config() -> &'static Config {
    CONFIG.get_or_init(|| Config::default())
}
```

---

## 十、边界情况处理

### 反例 16: 忽略空输入

**错误示例**:

```rust
fn average(numbers: &[f64]) -> f64 {
    let sum: f64 = numbers.iter().sum();
    sum / numbers.len() as f64  // ❌ 除以零
}
```

**原因**: 空切片会导致除以零 panic。

**修正**:

```rust
fn average(numbers: &[f64]) -> Option<f64> {
    if numbers.is_empty() {
        return None;
    }
    let sum: f64 = numbers.iter().sum();
    Some(sum / numbers.len() as f64)
}
```

---

### 反例 17: 整数溢出

**错误示例**:

```rust
fn factorial(n: u32) -> u32 {
    if n == 0 { 1 } else { n * factorial(n - 1) }  // ❌ 可能溢出
}
```

**原因**: 大输入会导致整数溢出（debug 模式 panic）。

**修正**:

```rust
fn factorial(n: u32) -> Option<u32> {
    let mut result = 1u32;
    for i in 1..=n {
        result = result.checked_mul(i)?;
    }
    Some(result)
}

// 或使用大整数
fn factorial_big(n: u32) -> num_bigint::BigUint {
    (1..=n).map(|x| x.into()).product()
}
```

---

## 十一、规避策略总结

| 反模式类别 | 规避策略 | 推荐工具/模式 |
| :--- | :--- | :--- |
| **所有权** | 显式作用域、避免自引用环 | `Weak` 打破 `Rc` 环 |
| **借用** | 先 collect 再修改、缩短借用范围 | `std::mem::take` 转移 |
| **并发** | 选 Send/Sync 类型、消息传递优先 | `channel`、`Arc<Mutex>` |
| **类型** | 从具体开始，按需泛型 | `impl Trait`、trait 按需 |
| **异步** | 异步锁跨 await、记得 await | `tokio::sync::Mutex` |
| **错误** | 传播错误、提供上下文 | `thiserror`、`anyhow` |
| **性能** | 避免不必要克隆、使用引用 | `Cow`、`Arc<str>` |
| **设计** | 按需求查设计模式 | 模式选取示例 |

---

## 十二、形式化方法链接

### 理论基础

| 概念 | 形式化文档 | 描述 |
| :--- | :--- | :--- |
| **所有权模型** | [ownership_model](../../research_notes/formal_methods/ownership_model.md) | 反模式的形式化定义 |
| **借用检查** | [borrow_checker_proof](../../research_notes/formal_methods/borrow_checker_proof.md) | 借用规则违反的检测 |
| **Send/Sync** | [send_sync_formalization](../../research_notes/formal_methods/send_sync_formalization.md) | 并发反模式的形式化 |
| **反模式理论** | [anti_patterns](../../research_notes/software_design_theory/07_anti_patterns.md) | 设计模式反模式 |
| **类型系统** | [type_system_foundations](../../research_notes/type_theory/type_system_foundations.md) | 类型错误的形式化 |

### 形式化定义

**Def AP1（反模式）**: 违反设计模式不变式或 Rust 安全规则的实现；$\mathit{SafeB}(P) = \mathrm{Inexpr}$ 或违反 ownership/borrow 规则。

**Axiom AP1**: 反模式导致 UB、数据竞争、或逻辑错误。

**定理 AP-T1（反模式检测）**: 编译器错误对应特定的反模式类别，可通过形式化规则映射。

---

## 编译失败测试（compile_fail）

典型反例可通过 `compile_fail` 在 doc-test 或 trybuild 中验证编译失败：

```rust
/// 反例：移动后使用——应编译失败
///
/// ```rust,compile_fail
/// let s = String::from("hello");
/// let s2 = s;
/// println!("{}", s);  // 错误：s 已失效
/// ```
```

**参考**: [testing_cheatsheet](./testing_cheatsheet.md) 编译测试；[c11 宏模块 trybuild](../../../crates/c11_macro_system/) 过程宏编译失败测试。

---

## 速查卡清单（已补全反例 2026-02-12）

- [x] ownership_cheatsheet
- [x] type_system.md
- [x] error_handling_cheatsheet
- [x] generics_cheatsheet
- [x] async_patterns
- [x] control_flow_functions_cheatsheet
- [x] threads_concurrency_cheatsheet
- [x] collections_iterators_cheatsheet
- [x] smart_pointers_cheatsheet
- [x] macros_cheatsheet
- [x] modules_cheatsheet
- [x] testing_cheatsheet
- [x] cargo_cheatsheet
- [x] design_patterns_cheatsheet
- [x] process_management_cheatsheet
- [x] network_programming_cheatsheet
- [x] algorithms_cheatsheet
- [x] wasm_cheatsheet
- [x] strings_formatting_cheatsheet

---

## 十四、完整示例：场景 → 反模式 → 正确写法

### 场景 1: 需要共享可变状态

**反模式**: `Rc<RefCell<T>>` 跨线程。

**正确**: `Arc<Mutex<T>>` 或 `Arc<RwLock<T>>`。

### 场景 2: 缓存全局配置

**反模式**: `lazy_static!` + `Mutex` 可变。

**正确**: `std::sync::OnceLock` 或 `ArcSwap`。

### 场景 3: 构建复杂对象

**反模式**: 构造函数参数过多（>5）。

**正确**: Builder 模式。

### 场景 4: 处理可能失败的操作

**反模式**: `unwrap()` 或 `expect()`  everywhere。

**正确**: `Result` 传播 + 错误转换。

### 场景 5: 频繁字符串拼接

**反模式**: `String` + 操作。

**正确**: `format!` 或 `write!` to `String`。

---

**最后更新**: 2026-02-20
**维护者**: 文档团队
**状态**: ✅ **已完成**
