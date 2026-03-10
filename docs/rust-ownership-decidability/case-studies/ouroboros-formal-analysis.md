# Ouroboros 自引用结构形式化分析

> **主题**: 安全的自引用结构体与所有权系统扩展
>
> **形式化框架**: 借用投影 + Pin保证 + 生命周期参数化
>
> **参考**: [ouroboros](https://docs.rs/ouroboros) 0.18.x, [ouroboros_macro](https://docs.rs/ouroboros_macro)

---

## 目录

- [Ouroboros 自引用结构形式化分析](#ouroboros-自引用结构形式化分析)
  - [目录](#目录)
  - [1. 项目概览](#1-项目概览)
    - [核心解决的问题](#核心解决的问题)
    - [关键特性](#关键特性)
  - [2. 自引用问题背景](#2-自引用问题背景)
    - [2.1 什么是自引用结构体](#21-什么是自引用结构体)
    - [2.2 手动实现的陷阱](#22-手动实现的陷阱)
    - [2.3 Rust所有权系统的限制](#23-rust所有权系统的限制)
  - [3. 宏工作原理](#3-宏工作原理)
    - [3.1 self\_referencing宏生成分析](#31-self_referencing宏生成分析)
    - [3.2 Builder模式实现](#32-builder模式实现)
    - [3.3 代码生成示例](#33-代码生成示例)
  - [4. 借用投影机制](#4-借用投影机制)
    - [4.1 with\_\*方法设计原理](#41-with_方法设计原理)
    - [4.2 闭包API与作用域控制](#42-闭包api与作用域控制)
    - [4.3 内存布局保证](#43-内存布局保证)
  - [5. Pin保证](#5-pin保证)
    - [5.1 !Unpin实现机制](#51-unpin实现机制)
    - [5.2 内存固定原理](#52-内存固定原理)
    - [5.3 自引用有效性证明](#53-自引用有效性证明)
  - [6. 生命周期处理](#6-生命周期处理)
    - [6.1 'this生命周期参数](#61-this生命周期参数)
    - [6.2 协变与逆变问题](#62-协变与逆变问题)
    - [6.3 生命周期约束推导](#63-生命周期约束推导)
  - [7. 高级特性](#7-高级特性)
    - [7.1 or\_shared变体](#71-or_shared变体)
    - [7.2 async/await支持](#72-asyncawait支持)
    - [7.3 递归自引用类型](#73-递归自引用类型)
  - [8. 性能考虑](#8-性能考虑)
    - [8.1 堆分配策略](#81-堆分配策略)
    - [8.2 内存开销分析](#82-内存开销分析)
    - [8.3 零成本抽象验证](#83-零成本抽象验证)
  - [9. 实际应用案例](#9-实际应用案例)
    - [9.1 解析器实现](#91-解析器实现)
    - [9.2 缓存设计](#92-缓存设计)
    - [9.3 树结构](#93-树结构)
  - [10. 与Pin-project对比](#10-与pin-project对比)
    - [10.1 使用场景差异](#101-使用场景差异)
    - [10.2 选型建议](#102-选型建议)
    - [10.3 互操作性](#103-互操作性)
  - [11. 完整代码示例](#11-完整代码示例)
    - [11.1 基本自引用模式](#111-基本自引用模式)
    - [11.2 多字段相互引用](#112-多字段相互引用)
    - [11.3 复杂数据结构](#113-复杂数据结构)
  - [12. 形式化定理汇总](#12-形式化定理汇总)
    - [定理 2.1 (宏生成安全性)](#定理-21-宏生成安全性)
    - [定理 3.1 (投影函数安全性)](#定理-31-投影函数安全性)
    - [定理 4.1 (不可移动不变式)](#定理-41-不可移动不变式)
    - [定理 6.1 (生命周期完备性)](#定理-61-生命周期完备性)
    - [定理 8.1 (零成本抽象)](#定理-81-零成本抽象)
  - [参考文献](#参考文献)

---

## 1. 项目概览

Ouroboros 是一个 Rust 宏库，用于安全地创建**自引用结构体（Self-Referential Structs）**。它通过过程宏自动生成安全的构建器和访问器，解决了 Rust 所有权系统中长期存在的自引用难题。

### 核心解决的问题

| 问题 | Ouroboros 解决方案 |
|------|-------------------|
| 结构体字段引用同一结构体的其他字段 | `#[borrows(...)]` 属性标记依赖关系 |
| 移动结构体导致自引用悬垂 | 生成 `!Unpin` 类型 + `Pin` 保证 |
| 手动实现需要大量 `unsafe` 代码 | 宏自动生成安全的构建器和投影方法 |
| 生命周期参数复杂难以管理 | `'this` 生命周期自动推断和约束 |

### 关键特性

- **零unsafe**: 用户代码无需编写 `unsafe` 块
- **Pin兼容**: 与 Rust 的 `Pin` 系统无缝集成
- **类型安全**: 编译期保证自引用有效性
- **性能优秀**: 无运行时开销的零成本抽象
- **异步支持**: 完整支持 `async/await` 和 futures

---

## 2. 自引用问题背景

### 2.1 什么是自引用结构体

自引用结构体是指其某个字段包含对同一结构体其他字段的引用。这种设计在某些场景下非常自然：

```rust
// 理想化的自引用结构体（Rust不允许直接这样写）
struct Document {
    content: String,
    title: &str,  // 引用 content 中的某个片段
}
```

**典型应用场景**:

1. **解析器**: AST 节点引用原始输入字符串的片段
2. **缓存系统**: 索引结构引用缓存数据
3. **树结构**: 父节点缓存子节点的引用
4. **迭代器**: 返回引用底层集合的元素

### 2.2 手动实现的陷阱

手动实现自引用结构体充满了危险：

```rust
use std::ptr::NonNull;

// 危险的手动实现
struct BadDocument {
    content: String,
    // 使用原始指针绕过借用检查
    title: Option<NonNull<str>>,
}

impl BadDocument {
    fn new(content: String) -> Self {
        let mut doc = Self {
            content,
            title: None,
        };
        // 创建自引用
        doc.title = Some(unsafe {
            NonNull::new_unchecked(&doc.content[0..10] as *const _ as *mut _)
        });
        doc
    }

    fn title(&self) -> &str {
        unsafe { self.title.unwrap().as_ref() }
    }
}

fn main() {
    let doc = BadDocument::new("Hello World Document".to_string());
    let title = doc.title();

    // 致命错误：移动结构体导致悬垂指针
    let moved_doc = doc;  // doc 被移动到新的内存位置
    // title 现在指向已释放的内存！
    println!("{}", title);  // 未定义行为！
}
```

**主要风险**:

| 风险 | 描述 | 后果 |
|------|------|------|
| 悬垂指针 | 结构体移动后，内部指针仍指向旧位置 | 内存安全漏洞 |
| 双重释放 | 不当的 Drop 实现可能导致重复释放内存 | 程序崩溃 |
| 数据竞争 | 多线程环境下缺乏同步机制 | 未定义行为 |
| 生命周期欺骗 | `unsafe` 代码绕过编译器检查 | 逻辑错误 |

### 2.3 Rust所有权系统的限制

Rust 的借用规则明确禁止自引用：

```rust
// 编译错误：生命周期不匹配
struct Document<'a> {
    content: String,
    title: &'a str,  // 这个生命周期无法正确表达"引用自身"
}

impl<'a> Document<'a> {
    fn new() -> Self {
        let content = String::from("text");
        Self {
            content,
            title: &content[0..2],  // 错误：content 将被移动，引用失效
        }
    }  // content 在这里被释放
}
```

**核心矛盾**:

1. **所有权与借用的冲突**: 结构体拥有其字段的所有权，但自引用要求同时借用
2. **移动语义**: Rust 默认允许值被移动，但移动会破坏自引用
3. **生命周期参数化**: 无法为结构体定义引用自身的生命周期参数

---

## 3. 宏工作原理

### 3.1 self_referencing宏生成分析

`#[self_referencing]` 是一个过程宏，它会：

1. **解析结构体定义**: 识别 `#[borrows(...)]` 标记的字段
2. **生成 Builder**: 创建类型安全的构建器模式
3. **生成访问器**: 创建 `with_*` 投影方法
4. **实现 !Unpin**: 确保结构体不能被移动

**输入结构体**:

```rust
use ouroboros::self_referencing;

#[self_referencing]
struct DataWithSlice {
    data: Vec<u8>,
    #[borrows(data)]
    slice: &'this [u8],
}
```

### 3.2 Builder模式实现

宏生成的构建器确保在结构体被固定之前完成所有初始化：

```rust
// 宏生成的代码（简化示意）
impl DataWithSlice {
    pub fn new<F>(data: Vec<u8>, slice_builder: F) -> Pin<Box<Self>>
    where
        F: FnOnce(&Vec<u8>) -> &[u8],
    {
        let mut this = Box::pin(Self {
            data,
            slice: std::ptr::null(),  // 临时值
        });

        // 获取指向 data 的指针
        let data_ptr = &this.data as *const Vec<u8>;

        // 通过闭包计算 slice
        let slice = slice_builder(unsafe { &*data_ptr });

        // 安全地设置自引用字段
        unsafe {
            let this_mut = Pin::get_unchecked_mut(this.as_mut());
            this_mut.slice = slice;
        }

        this
    }
}
```

### 3.3 代码生成示例

完整的宏生成代码包含以下组件：

```rust
// === 自动生成的结构体定义 ===
#[repr(C)]  // 确保字段布局稳定
struct DataWithSlice {
    data: Vec<u8>,
    slice: *const [u8],  // 内部使用原始指针存储
}

// === !Unpin 实现 ===
impl !Unpin for DataWithSlice {}

// === 安全构造函数 ===
impl DataWithSlice {
    pub fn new<F>(
        data: Vec<u8>,
        slice_builder: F
    ) -> Pin<Box<Self>>
    where
        F: FnOnce(&Vec<u8>) -> &[u8],
    {
        // ... 实现细节
    }
}

// === 投影访问器 ===
impl DataWithSlice {
    pub fn with_slice<R, F>(&self, f: F) -> R
    where
        F: FnOnce(&[u8]) -> R,
    {
        f(unsafe { &*self.slice })
    }

    pub fn with_slice_mut<R, F>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        f(unsafe { &mut *(self.slice as *mut [u8]) })
    }
}
```

---

## 4. 借用投影机制

### 4.1 with_*方法设计原理

Ouroboros 使用闭包 API 来安全地访问自引用字段，这是其核心设计模式：

```rust
// 宏生成的 with_slice 方法
impl DataWithSlice {
    /// 安全访问自引用字段 slice
    ///
    /// 设计原理：
    /// 1. 闭包参数的生命周期受限于方法调用
    /// 2. 无法逃逸引用，防止悬垂指针
    /// 3. 返回值 R 不包含对 &self 的引用
    pub fn with_slice<R, F>(&self, f: F) -> R
    where
        F: FnOnce(&[u8]) -> R,
    {
        // 将原始指针转换为引用，仅在闭包执行期间有效
        let slice_ref = unsafe { &*self.slice };
        f(slice_ref)
    }
}
```

**为什么使用闭包 API?**

| 方案 | 问题 | 闭包方案优势 |
|------|------|-------------|
| 直接返回引用 | `fn slice(&self) -> &[u8]` 允许引用逃逸 | 闭包限制生命周期在调用范围内 |
| getter方法 | 调用者可以存储引用 | 无法存储闭包参数 |
| 原始指针访问 | 需要 unsafe | 封装 unsafe 在库内部 |

### 4.2 闭包API与作用域控制

闭包 API 强制实现**借用纪律**：

```rust
let data = DataWithSlice::new(
    vec![1, 2, 3, 4, 5],
    |data| &data[1..4],  // slice = &[2, 3, 4]
);

// 正确的使用方式：在闭包内使用
data.with_slice(|slice| {
    println!("Slice content: {:?}", slice);
    // slice 在这里有效，但不能被返回
});

// 错误的尝试：试图逃逸引用
let stolen: &[u8];
data.with_slice(|slice| {
    stolen = slice;  // 编译错误：生命周期不匹配
});
```

**作用域保证**:

```rust
impl DataWithSlice {
    // 不可变借用投影
    pub fn with_slice<R, F>(&self, f: F) -> R
    where
        F: for<'a> FnOnce(&'a [u8]) -> R,
    {
        let slice_ref: &[u8] = unsafe { &*self.slice };
        f(slice_ref)
    }

    // 可变借用投影
    pub fn with_slice_mut<R, F>(&mut self, f: F) -> R
    where
        F: for<'a> FnOnce(&'a mut [u8]) -> R,
    {
        let slice_ref: &mut [u8] = unsafe { &mut *(self.slice as *mut _) };
        f(slice_ref)
    }
}
```

### 4.3 内存布局保证

使用 `#[repr(C)]` 确保字段布局稳定，这对自引用的安全性至关重要：

```rust
#[repr(C)]
struct DataWithSlice {
    data: Vec<u8>,    // 偏移量 0
    slice: *const [u8], // 偏移量 sizeof(Vec<u8>)
}
```

**内存布局稳定性**:

- `#[repr(C)]` 保证字段按声明顺序排列
- 被引用字段（`data`）在引用字段（`slice`）之前
- 结构体移动时，字段间相对偏移保持不变

---

## 5. Pin保证

### 5.1 !Unpin实现机制

Ouroboros 通过实现 `!Unpin` 来阻止结构体被移动：

```rust
// 宏自动生成
impl !Unpin for DataWithSlice {}
```

**原理**: 当一个类型实现了 `!Unpin`，它就不能被解固定（unpin），从而保证其内存地址稳定。

### 5.2 内存固定原理

`Pin<P>` 是 Rust 提供的内存固定原语：

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

// 宏生成的固定标记
pub struct DataWithSlice {
    data: Vec<u8>,
    slice: *const [u8],
    _pin: PhantomPinned,  // 实现 !Unpin
}
```

**Pin契约**:

```
如果 T: !Unpin，则 Pin<&mut T> 保证：
1. T 的实例不会被移动（除非实现了 Unpin）
2. 指向 T 的指针在 T 销毁前保持有效
3. 可以安全地依赖 T 的内存地址
```

### 5.3 自引用有效性证明

**定理 5.1 (自引用有效性)**: 使用 Ouroboros 创建的自引用结构体，其自引用字段在整个生命周期内始终有效。

**证明**:

1. **构造期安全**:
   - 在 `new()` 中，结构体先被分配到堆上（`Box::pin`）
   - 然后才计算自引用字段的值
   - 自引用被设置后，结构体已经是 `Pin<Box<T>>`

2. **不可移动保证**:
   - `PhantomPinned` 实现使类型 `!Unpin`
   - 用户无法获取 `&mut T` 来移动字段
   - `Box::pin` 保证堆内存地址稳定

3. **访问期安全**:
   - `with_*` 方法通过原始指针临时创建引用
   - 引用的生命周期受限于闭包调用
   - 闭包返回后，引用自动失效

∎

---

## 6. 生命周期处理

### 6.1 'this生命周期参数

Ouroboros 引入特殊的 `'this` 生命周期来表示"结构体的生命周期"：

```rust
#[self_referencing]
struct Document {
    content: String,
    #[borrows(content)]
    // 'this 表示"与整个结构体相同的生命周期"
    title: &'this str,
}
```

**生命周期展开**:

```rust
// 宏实际生成的代码概念
struct Document {
    content: String,
    // 内部使用裸指针，但概念上等价于：
    // title: &'document str where 'document 是结构体生命周期
    title: *const str,
}
```

### 6.2 协变与逆变问题

自引用引入了复杂的生命周期方差问题：

```rust
#[self_referencing]
struct Container<'a> {
    data: &'a str,
    #[borrows(data)]
    // 这里 'this 与 'a 的关系?
    view: &'this str,
}
```

**方差分析**:

| 类型参数 | 方差 | 影响 |
|---------|------|------|
| `'this` | 逆变 | 子类型关系反转 |
| 被引用字段 | 协变 | 正常子类型关系 |
| 自引用字段 | 不变 | 严格生命周期匹配 |

### 6.3 生命周期约束推导

Ouroboros 自动推导生命周期约束：

```rust
#[self_referencing]
struct ComplexDoc<'a, T> {
    owner: String,
    #[borrows(owner)]
    header: &'this str,

    data: Vec<T>,
    #[borrows(data)]
    first: &'this T,

    external: &'a str,  // 外部生命周期
}
```

**推导的约束**:

1. `'this` 不超过结构体生命周期
2. 自引用字段生命周期不超过被引用字段
3. 外部生命周期 `'a` 独立于 `'this`
4. 泛型参数 `T` 的生命周期正确传播

---

## 7. 高级特性

### 7.1 or_shared变体

`or_shared` 允许创建共享的自引用：

```rust
use ouroboros::self_referencing;
use std::sync::Arc;

#[self_referencing]
struct SharedData {
    data: Arc<String>,
    #[borrows(data)]
    #[covariant]  // 协变标记
    slice: &'this str,
}

impl SharedData {
    fn new_shared(arc: Arc<String>) -> Pin<Arc<Self>>> {
        Self::new(arc, |data| &data[..])
    }
}
```

**使用场景**:

- 多线程共享自引用数据
- 减少堆分配（Arc vs Box）
- 需要克隆自引用结构体句柄

### 7.2 async/await支持

Ouroboros 完全支持异步代码：

```rust
use ouroboros::self_referencing;

#[self_referencing]
struct AsyncParser {
    input: String,
    #[borrows(input)]
    current: &'this str,
}

impl AsyncParser {
    async fn parse_next(&self) -> Option<&str> {
        self.with_current(|current| {
            // 在异步上下文中安全访问
            current.split_whitespace().next()
        })
    }
}

// 在 async 函数中使用
async fn process() {
    let parser = AsyncParser::new(
        "hello world async".to_string(),
        |input| input,
    );

    while let Some(word) = parser.parse_next().await {
        println!("{}", word);
    }
}
```

**注意事项**:

1. 自引用结构体可以安全地跨越 await 点
2. `Pin` 保证在异步状态机中仍然有效
3. 不能在 async 块中创建自引用结构体（生命周期限制）

### 7.3 递归自引用类型

支持递归数据结构：

```rust
use ouroboros::self_referencing;

#[self_referencing]
struct TreeNode {
    value: String,
    children: Vec<Box<TreeNode>>,
    #[borrows(value)]
    value_ref: &'this str,
}

impl TreeNode {
    fn new_leaf(value: String) -> Pin<Box<Self>> {
        Self::new(value, Vec::new(), |v| v.as_str())
    }

    fn with_children(
        value: String,
        children: Vec<Box<TreeNode>>,
    ) -> Pin<Box<Self>> {
        Self::new(value, children, |v| v.as_str())
    }
}
```

---

## 8. 性能考虑

### 8.1 堆分配策略

Ouroboros 默认使用 `Box::pin` 进行堆分配：

```rust
pub fn new(...) -> Pin<Box<Self>>
```

**分配策略对比**:

| 策略 | 优点 | 缺点 | 适用场景 |
|------|------|------|---------|
| `Box::pin` (默认) | 简单可靠 | 堆分配开销 | 一般用途 |
| `Arc::pin` | 可共享 | 引用计数开销 | 多线程共享 |
| 栈分配 | 无堆开销 | 复杂且受限 | 极短生命周期 |

### 8.2 内存开销分析

**结构体内存布局**:

```rust
#[self_referencing]
struct Example {
    a: String,      // 24 bytes
    #[borrows(a)]
    b: &'this str,  // 16 bytes (fat pointer)
    c: Vec<u8>,     // 24 bytes
    #[borrows(c)]
    d: &'this [u8], // 16 bytes (fat pointer)
}

// 总大小: 24 + 16 + 24 + 16 = 80 bytes
// 额外开销: PhantomPinned (0 bytes, ZST)
```

**开销来源**:

1. **原始指针存储**: 与引用大小相同（8或16字节）
2. **堆分配**: `Box` 的内存分配开销
3. **无运行时开销**: 投影方法为零成本抽象

### 8.3 零成本抽象验证

使用 `cargo asm` 或 `godbolt.org` 验证：

```rust
// 用户代码
data.with_slice(|s| s.len())

// 编译器优化后的汇编（概念）
// mov rax, [rsi + 32]  // 直接读取 slice 长度字段
// ret
```

**优化保证**:

- 闭包内联消除函数调用开销
- 原始指针解引用优化为直接内存访问
- 无边界检查（已在构造期验证）

---

## 9. 实际应用案例

### 9.1 解析器实现

实现一个高效的零拷贝解析器：

```rust
use ouroboros::self_referencing;

#[self_referencing]
struct ZeroCopyParser {
    input: String,
    #[borrows(input)]
    tokens: Vec<&'this str>,
}

impl ZeroCopyParser {
    fn parse(input: String) -> Pin<Box<Self>> {
        Self::new(input, |input| {
            input.split_whitespace().collect()
        })
    }

    fn token_at(&self, index: usize) -> Option<&str> {
        self.with_tokens(|tokens| {
            tokens.get(index).copied()
        })
    }
}

fn main() {
    let parser = ZeroCopyParser::parse(
        "hello world from ouroboros".to_string()
    );

    assert_eq!(parser.token_at(0), Some("hello"));
    assert_eq!(parser.token_at(3), Some("ouroboros"));
}
```

### 9.2 缓存设计

实现带索引的缓存结构：

```rust
use ouroboros::self_referencing;
use std::collections::HashMap;

#[self_referencing]
struct IndexedCache {
    data: Vec<u8>,
    #[borrows(data)]
    index: HashMap<String, &'this [u8]>,
}

impl IndexedCache {
    fn from_sections(sections: Vec<(String, Vec<u8>)>) -> Pin<Box<Self>> {
        // 合并所有数据
        let mut data = Vec::new();
        let mut offsets = Vec::new();

        for (name, content) in sections {
            let start = data.len();
            data.extend_from_slice(&content);
            offsets.push((name, start, data.len()));
        }

        Self::new(data, |data| {
            let mut index = HashMap::new();
            for (name, start, end) in offsets {
                index.insert(name, &data[start..end]);
            }
            index
        })
    }

    fn get(&self, key: &str) -> Option<&[u8]> {
        self.with_index(|index| {
            index.get(key).copied()
        })
    }
}
```

### 9.3 树结构

实现父子双向引用的树：

```rust
use ouroboros::self_referencing;

#[self_referencing]
struct Node {
    value: String,
    children: Vec<Box<Node>>,
    #[borrows(value)]
    value_ref: &'this str,
}

#[self_referencing]
struct Tree {
    root: Node,
    #[borrows(root)]
    root_ref: &'this Node,
}

impl Tree {
    fn traverse<F>(&self, mut f: F)
    where
        F: FnMut(&str),
    {
        self.with_root_ref(|root| {
            Self::traverse_node(root, &mut f);
        });
    }

    fn traverse_node<F>(node: &Node, f: &mut F)
    where
        F: FnMut(&str),
    {
        node.with_value_ref(|v| f(v));
        node.with_children(|children| {
            for child in children.iter() {
                Self::traverse_node(child, f);
            }
        });
    }
}
```

---

## 10. 与Pin-project对比

### 10.1 使用场景差异

| 特性 | Ouroboros | pin-project |
|------|-----------|-------------|
| **主要用途** | 创建自引用结构体 | 在 Pin 上安全投影字段 |
| **自引用** | 原生支持 | 需手动管理 |
| **unsafe 代码** | 用户无需编写 | 宏生成，用户可能需 unsafe |
| **复杂度** | 高（完全抽象） | 低（仅投影辅助） |
| **适用场景** | 复杂自引用数据 | Future 和流式处理 |

### 10.2 选型建议

**选择 Ouroboros 当**:

- 需要创建复杂的自引用数据结构
- 不想处理 `unsafe` 代码
- 结构体生命周期较长
- 需要递归自引用类型

**选择 pin-project 当**:

- 实现 Futures 和异步流
- 需要在 `Pin<&mut Self>` 上投影字段
- 自引用模式简单且已知
- 与 async/await 深度集成

### 10.3 互操作性

两者可以协同使用：

```rust
use ouroboros::self_referencing;
use pin_project::pin_project;
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

#[self_referencing]
struct DataBuffer {
    buffer: Vec<u8>,
    #[borrows(buffer)]
    current: &'this [u8],
}

#[pin_project]
struct DataProcessor {
    #[pin]
    buffer: Pin<Box<DataBuffer>>,
    position: usize,
}

impl Future for DataProcessor {
    type Output = usize;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        // 使用 pin-project 安全投影
        // 使用 ouroboros 安全访问自引用
        this.buffer.with_current(|current| {
            // 处理数据...
        });
        Poll::Ready(*this.position)
    }
}
```

---

## 11. 完整代码示例

### 11.1 基本自引用模式

```rust
use ouroboros::self_referencing;

// 最简单的自引用：Vec 和它的切片
#[self_referencing]
struct DataWithSlice {
    data: Vec<u8>,
    #[borrows(data)]
    slice: &'this [u8],
}

fn main() {
    let data = DataWithSlice::new(
        vec![1, 2, 3, 4, 5],
        |data| &data[1..4],
    );

    data.with_slice(|slice| {
        assert_eq!(slice, &[2, 3, 4]);
    });
}
```

### 11.2 多字段相互引用

```rust
use ouroboros::self_referencing;
use std::collections::HashMap;

// 多字段相互引用的复杂结构
#[self_referencing]
struct DocumentStore {
    content: String,
    metadata: HashMap<String, String>,

    #[borrows(content)]
    title: &'this str,

    #[borrows(content)]
    body: &'this str,

    #[borrows(metadata)]
    tags: Vec<&'this str>,
}

impl DocumentStore {
    fn parse(content: String, metadata: HashMap<String, String>) -> Pin<Box<Self>> {
        Self::new(
            content,
            metadata,
            |content| {
                // 提取标题（第一行）
                content.lines().next().unwrap_or("")
            },
            |content| {
                // 提取正文（剩余部分）
                content.lines().skip(1).collect::<Vec<_>>().join("\n")
            },
            |metadata| {
                // 从 metadata 提取标签
                metadata
                    .get("tags")
                    .map(|t| t.split(',').collect())
                    .unwrap_or_default()
            },
        )
    }

    fn preview(&self) -> String {
        self.with_title(|title| {
            self.with_body(|body| {
                format!("{}: {}...", title, &body[..body.len().min(50)])
            })
        })
    }
}
```

### 11.3 复杂数据结构

```rust
use ouroboros::self_referencing;
use std::pin::Pin;

// 实现一个带有自引用索引的数据库行缓存
#[self_referencing]
struct RowCache {
    raw_data: Vec<Vec<u8>>,

    #[borrows(raw_data)]
    primary_index: HashMap<u64, &'this [u8]>,

    #[borrows(raw_data)]
    secondary_index: HashMap<String, Vec<&'this [u8]>>,
}

impl RowCache {
    fn from_rows(rows: Vec<(u64, String, Vec<u8>)>) -> Pin<Box<Self>> {
        // 预处理数据
        let mut raw_data: Vec<Vec<u8>> = Vec::new();
        let mut primary_keys: Vec<(u64, usize)> = Vec::new();
        let mut secondary_keys: Vec<(String, usize)> = Vec::new();

        for (pk, sk, data) in rows {
            let idx = raw_data.len();
            raw_data.push(data);
            primary_keys.push((pk, idx));
            secondary_keys.push((sk, idx));
        }

        Self::new(
            raw_data,
            move |raw_data| {
                primary_keys
                    .into_iter()
                    .map(|(pk, idx)| (pk, raw_data[idx].as_slice()))
                    .collect()
            },
            move |raw_data| {
                let mut sec_idx: HashMap<String, Vec<&[u8]>> = HashMap::new();
                for (sk, idx) in secondary_keys {
                    sec_idx.entry(sk).or_default().push(&raw_data[idx]);
                }
                sec_idx
            },
        )
    }

    fn get_by_pk(&self, pk: u64) -> Option<&[u8]> {
        self.with_primary_index(|idx| {
            idx.get(&pk).copied()
        })
    }

    fn get_by_sk(&self, sk: &str) -> Vec<&[u8]> {
        self.with_secondary_index(|idx| {
            idx.get(sk).map(|v| v.clone()).unwrap_or_default()
        })
    }
}

// 使用示例
fn demo() {
    let cache = RowCache::from_rows(vec![
        (1, "alice".to_string(), vec![1, 2, 3]),
        (2, "bob".to_string(), vec![4, 5, 6]),
        (3, "alice".to_string(), vec![7, 8, 9]),
    ]);

    assert_eq!(cache.get_by_pk(1), Some(&[1, 2, 3][..]));
    assert_eq!(cache.get_by_sk("alice").len(), 2);
}
```

---

## 12. 形式化定理汇总

### 定理 2.1 (宏生成安全性)

> **`#[self_referencing]` 宏生成的代码在构造期保证所有自引用字段的有效性。**

**证明要点**:

1. 结构体先被分配到固定内存位置（`Box::pin`）
2. 被引用字段完全初始化后才计算自引用值
3. 自引用设置通过受控的 `unsafe` 块完成，确保指针有效性
4. 结构体标记为 `!Unpin` 防止后续移动

∎

### 定理 3.1 (投影函数安全性)

> **`with_*` 方法提供的闭包 API 保证自引用访问期间不会出现悬垂引用。**

**证明要点**:

1. 闭包参数的生命周期绑定到闭包调用期间
2. 返回值 `R` 的约束确保无法返回内部引用
3. 原始指针仅在闭包执行期间解引用
4. 借用检查器验证闭包体满足生命周期约束

∎

### 定理 4.1 (不可移动不变式)

> **Ouroboros 生成的类型实现 `!Unpin`，确保实例的内存地址在其生命周期内保持不变。**

**证明要点**:

1. `PhantomPinned` 字段使类型自动实现 `!Unpin`
2. `Pin<Box<T>>` 包装阻止解固定操作
3. 不存在返回 `&mut T` 的公共 API
4. Drop 实现保证销毁顺序安全

∎

### 定理 6.1 (生命周期完备性)

> **`'this` 生命周期参数正确表达了自引用字段与结构体实例之间的生命周期依赖关系。**

**证明要点**:

1. `'this` 被约束为不超过结构体生命周期
2. 协变/逆变分析确保子类型关系正确
3. 跨字段引用满足传递性约束
4. 外部生命周期参数独立于自引用生命周期

∎

### 定理 8.1 (零成本抽象)

> **在优化编译下，Ouroboros 的自引用访问不产生运行时开销。**

**证明要点**:

1. 闭包内联消除函数调用开销
2. 原始指针解引用优化为直接内存偏移
3. 借用检查在编译期完成，无运行时检查
4. 内存布局与手动实现的 `unsafe` 版本相同

∎

---

## 参考文献

1. [Ouroboros Documentation](https://docs.rs/ouroboros)
2. [Ouroboros Macro Documentation](https://docs.rs/ouroboros_macro)
3. [The Rust Programming Language - Pinning](https://doc.rust-lang.org/std/pin/index.html)
4. [Rust RFC 2349 - Pin](https://rust-lang.github.io/rfcs/2349-pin.html)
5. [Self-Referential Structs in Rust](https://morestina.net/blog/1868/self-referential-structs-in-rust)
6. [Pin-Project Documentation](https://docs.rs/pin-project)

---

*文档版本: 2.0.0*
*定理数量: 5个*
*最后更新: 2026-03-10*
