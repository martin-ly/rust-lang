# Rust 高级主题导航

本目录包含 Rust 编程语言的高级主题，适合已经掌握 Rust 基础并希望深入理解语言内部机制和高级用法的开发者。

---

## 目录结构

```
08-advanced-topics/
├── README.md                      # 本文件 - 导航与概览
├── 08-01-const-generics.md        # 常量泛型
├── 08-02-async-rust.md           # 异步Rust深度解析
├── 08-03-ffi-patterns.md         # FFI模式与C互操作
├── 08-04-proc-macros.md          # 过程宏开发
├── 08-05-unsafe-patterns.md      # Unsafe Rust模式
├── 08-06-zero-cost-abstractions.md # 零成本抽象
└── 08-07-custom-allocators.md    # 自定义分配器
```

---

## 学习路径建议

### 初级路径
如果你刚开始接触 Rust 高级特性：

1. **08-01-const-generics.md** - 理解编译时计算能力
2. **08-02-async-rust.md** - 掌握异步编程的核心概念
3. **08-06-zero-cost-abstractions.md** - 学习如何写出高效的抽象代码

### 进阶路径
如果你需要与外部系统交互或开发库：

1. **08-03-ffi-patterns.md** - 学习如何安全地与 C 代码交互
2. **08-04-proc-macros.md** - 掌握声明宏和过程宏的开发
3. **08-05-unsafe-patterns.md** - 深入理解 Unsafe Rust 的安全边界

### 专家路径
如果你正在优化性能或开发系统级代码：

1. **08-05-unsafe-patterns.md** -  Unsafe Rust 的完整指南
2. **08-07-custom-allocators.md** - 自定义内存分配策略
3. **08-06-zero-cost-abstractions.md** - 深入了解编译器优化

---

## 各主题概述

### 08-01 Const Generics（常量泛型）

常量泛型允许你在类型参数中使用常量值，实现编译时多态。

**核心概念：**
- `const N: usize` 语法
- 常量泛型表达式
- 编译时数组大小检查

**应用场景：**
- 固定大小数组抽象
- 类型状态机
- 编译时配置

**示例预览：**
```rust
struct Vector<T, const N: usize> {
    data: [T; N],
}

impl<T, const N: usize> Vector<T, N> {
    fn size(&self) -> usize { N }
}
```

---

### 08-02 Async Rust（异步Rust）

深度解析 Rust 的异步编程模型，包括 Future trait、Pin、异步运行时和流处理。

**核心概念：**
- Future trait 与状态机
- Pin 与自引用类型
- async/await 语法糖
- 异步运行时架构
- Stream trait 与背压

**应用场景：**
- 高并发网络服务
- 实时数据处理
- 非阻塞 I/O

**示例预览：**
```rust
async fn fetch_data(url: &str) -> Result<Data, Error> {
    let response = client.get(url).await?;
    let data = response.json::<Data>().await?;
    Ok(data)
}
```

---

### 08-03 FFI Patterns（FFI模式）

学习如何安全地与 C 代码和其他语言交互，包括内存布局、ABI 兼容性和绑定生成。

**核心概念：**
- `extern "C"` 调用约定
- FFI 边界的安全性
- 内存布局控制 (`#[repr(C)]`)
- 不透明指针与所有权
- bindgen 和 cbindgen 工具

**应用场景：**
- 调用 C/C++ 库
- 嵌入式系统开发
- 跨语言插件系统
- 系统 API 调用

**示例预览：**
```rust
#[repr(C)]
pub struct MyStruct {
    pub field1: i32,
    pub field2: *mut c_char,
}

#[no_mangle]
pub extern "C" fn my_library_init() -> *mut MyContext {
    Box::into_raw(Box::new(MyContext::new()))
}
```

---

### 08-04 Proc Macros（过程宏）

全面掌握 Rust 的宏系统，包括声明宏（macro_rules!）和三种过程宏。

**核心概念：**
- TokenStream 处理
- 派生宏（Derive macros）
- 属性宏（Attribute macros）
- 函数式宏（Function-like macros）
- syn 和 quote crate

**应用场景：**
- 代码生成
- DSL 开发
- 序列化/反序列化
- 测试框架

**示例预览：**
```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    // 生成代码...
    quote! {
        // 生成的实现
    }.into()
}
```

---

### 05 Unsafe Patterns（Unsafe模式）

深入理解 Unsafe Rust，学习如何在不安全代码中维护安全不变量。

**核心概念：**
- 原始指针操作
- unsafe trait 与 unsafe fn
- 未定义行为（UB）
- 内存模型与别名规则
- Miri 检测工具

**应用场景：**
- 性能关键路径
- 底层系统编程
- FFI 边界
- 数据结构实现

**示例预览：**
```rust
pub unsafe fn slice_from_raw_parts<'a, T>(
    data: *const T,
    len: usize,
) -> &'a [T] {
    // SAFETY: 调用者必须保证 data 和 len 有效
    std::slice::from_raw_parts(data, len)
}
```

---

### 08-06 Zero-Cost Abstractions（零成本抽象）

学习 Rust 如何实现零成本抽象，以及如何利用这些特性编写高效代码。

**核心概念：**
- 零成本抽象原则
- 迭代器优化
- 泛型单态化
- 内联与 LTO
- SIMD 向量化

**应用场景：**
- 高性能计算
- 游戏引擎
- 嵌入式系统
- 实时系统

**示例预览：**
```rust
// 迭代器链在优化后与手写循环性能相同
let sum: i32 = (0..1000)
    .map(|x| x * 2)
    .filter(|x| x % 3 == 0)
    .sum();
```

---

### 08-07 Custom Allocators（自定义分配器）

学习 Rust 的分配器 API，以及如何为特定场景实现自定义内存分配器。

**核心概念：**
- GlobalAlloc trait
- Allocator trait（ nightly ）
- 内存池分配器
- 栈分配器
- 内存对齐

**应用场景：**
- 实时系统（避免堆分配延迟）
- 游戏引擎
- 嵌入式系统
- 高性能服务器

**示例预览：**
```rust
pub struct PoolAllocator {
    pools: [Vec<*mut u8>; 8],
}

unsafe impl GlobalAlloc for PoolAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // 从池中分配...
    }
    
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // 归还到池中...
    }
}
```

---

## 前置知识

在学习本目录内容之前，建议掌握：

1. **Rust 基础语法**
   - 所有权系统
   - 借用与生命周期
   - trait 系统
   - 泛型编程

2. **标准库熟悉度**
   - 集合类型
   - 错误处理
   - I/O 操作
   - 并发原语

3. **构建工具**
   - Cargo 包管理
   - 编译配置
   - 测试框架

---

## 最佳实践

### 代码组织

```rust
// 模块组织示例
mod ffi {
    // FFI 相关代码隔离
    pub mod bindings;
    pub mod types;
    pub mod utils;
}

mod unsafe_utils {
    // 不安全的工具函数集中管理
    #![allow(unsafe_code)]
    
    /// SAFETY: 文档说明安全前提
    pub unsafe fn raw_ptr_add<T>(ptr: *const T, offset: usize) -> *const T {
        ptr.add(offset)
    }
}
```

### 安全检查清单

在使用高级特性时，请检查：

- [ ] **Unsafe 代码**
  - 是否有完整的安全文档
  - 是否最小化了 unsafe 块范围
  - 是否使用了 Miri 检查

- [ ] **FFI 边界**
  - C 接口是否明确了所有权
  - 指针有效性是否得到验证
  - 异常安全性是否考虑

- [ ] **性能关键代码**
  - 是否测量了性能
  - 是否检查了汇编输出
  - 是否考虑了缓存效应

- [ ] **宏代码**
  - 是否处理了所有边缘情况
  - 错误信息是否清晰
  - 是否避免了名称污染

---

## 工具与资源

### 开发工具

| 工具 | 用途 | 安装命令 |
|------|------|----------|
| bindgen | C 头文件绑定生成 | `cargo install bindgen-cli` |
| cbindgen | 生成 C 头文件 | `cargo install cbindgen` |
| cargo-expand | 宏展开查看 | `cargo install cargo-expand` |
| cargo-asm | 汇编代码查看 | `cargo install cargo-asm` |
| Miri | 未定义行为检测 | `rustup component add miri` |
| valgrind | 内存检测 | 系统包管理器安装 |

### 性能分析

```bash
# 使用 perf 进行性能分析
cargo build --release
perf record ./target/release/myapp
perf report

# 使用 cargo-flamegraph
cargo install flamegraph
cargo flamegraph

# 使用 heaptrack 分析内存
cargo build --release
heaptrack ./target/release/myapp
```

### 学习资源

**官方文档：**
- [The Rust Reference - Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [The Embedded Rust Book](https://docs.rust-embedded.org/book/)

**书籍：**
- 《Programming Rust》（Jim Blandy 等）
- 《Rust for Rustaceans》（Jon Gjengset）
- 《Rust Atomics and Locks》（Mara Bos）

**博客与文章：**
- [Rust Lang Blog](https://blog.rust-lang.org/)
- [This Week in Rust](https://this-week-in-rust.org/)
- [Rust Forge](https://forge.rust-lang.org/)

---

## 常见问题

### Q: 什么时候应该使用 Unsafe Rust？

**A:** 仅在以下情况下使用：
1. 与 C 代码交互（FFI）
2. 实现基础数据结构（如 Vec、HashMap）
3. 性能关键路径需要原始指针操作
4. 与硬件直接交互

**永远不要**为了"方便"或"绕过编译器检查"而使用 unsafe。

### Q: 异步 Rust 应该选择哪个运行时？

**A:** 
- **Tokio**: 生态系统最完善，推荐用于大多数项目
- **async-std**: API 更接近标准库，适合特定场景
- **smol**: 轻量级，适合嵌入式或学习
- **自定义**: 仅在特殊需求下考虑

### Q: 如何调试宏生成的代码？

**A:**
```bash
# 查看宏展开
cargo expand

# 查看特定模块的展开
cargo expand path::to::module

# 保存到文件
cargo expand > expanded.rs
```

### Q: FFI 中如何处理 panic？

**A:** 始终使用 `catch_unwind` 捕获 panic，防止跨 FFI 边界传播：

```rust
#[no_mangle]
pub extern "C" fn safe_ffi_function() -> i32 {
    match std::panic::catch_unwind(|| {
        // 可能 panic 的 Rust 代码
    }) {
        Ok(result) => result,
        Err(_) => {
            // 记录错误，返回错误码
            -1
        }
    }
}
```

---

## 贡献与反馈

如果发现文档中的错误或有改进建议，欢迎提交 Issue 或 Pull Request。

### 文档规范

- 所有代码示例必须经过编译测试
- Unsafe 代码必须有完整的安全文档
- 性能声明需要有基准测试支持
- 保持中英文术语对照

---

## 版本信息

- **Rust 版本**: 1.75+
- **文档版本**: 1.0
- **最后更新**: 2026-03-04

---

## 许可证

本文档遵循与 Rust 项目相同的许可证：
- MIT License
- Apache License 2.0

---

> **注意**：本目录中的代码示例仅供学习参考，生产环境使用前请进行充分测试和代码审查。
