# Rust 2024 Edition `Future` in Prelude 影响分析

## 概述

Rust 2024 Edition 将 `std::future::Future` trait 添加到标准库 prelude 中。这意味着在 Edition 2024 下，`Future` trait 无需显式导入即可直接使用。

## 变化详情

### 之前（Rust 2021 及之前）

```rust
use std::future::Future;

async fn compute() -> i32 {
    42
}

fn box_future() -> Box<dyn Future<Output = i32>> {
    Box::new(compute())
}
```

### 之后（Rust 2024 Edition）

```rust
// 无需显式导入 Future trait
async fn compute() -> i32 {
    42
}

fn box_future() -> Box<dyn Future<Output = i32>> {
    Box::new(compute())
}
```

## 影响分析

### 正面影响

1. **代码更简洁**：异步代码中减少冗余的 `use std::future::Future;`
2. **学习曲线降低**：新手无需了解 prelude 与 `Future` 的关系
3. **与 async/await 对称**：`async` 和 `await` 已经是关键字，`Future` 自然应可见

### 潜在冲突

#### 冲突 1：自定义 `Future` trait

如果项目中定义了与标准库同名的 `Future` trait：

```rust
// 项目自定义的 Future trait
pub trait Future {
    fn execute(&self);
}

// Rust 2024：可能与 std::future::Future 冲突
impl Future for MyTask {
    fn execute(&self) {}
}
```

**解决方案**：

```rust
// 使用全限定路径或重命名
use std::future::Future as StdFuture;

pub trait Future {
    fn execute(&self);
}

impl Future for MyTask {
    fn execute(&self) {}
}

impl StdFuture for MyTask {
    type Output = ();
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(())
    }
}
```

#### 冲突 2：第三方库中的 `Future` 类型

某些旧版库可能导出自己的 `Future` 类型：

```rust
use some_legacy_lib::Future; // 可能与 prelude 的 Future 冲突
```

**解决方案**：

```rust
// 显式指定要使用的 Future
use std::future::Future as StdFuture;
use some_legacy_lib::Future as LegacyFuture;
```

#### 冲突 3：宏展开中的名称冲突

某些宏可能生成 `Future` 相关的代码，在 prelude 自动导入后可能产生歧义。

**解决方案**：在宏中使用全限定路径 `::std::future::Future`。

## 迁移建议

### 对于应用开发者

1. **移除冗余导入**：

```rust
// Rust 2021
use std::future::Future;

// Rust 2024：可以删除这行
```

1. **检查自定义 trait 名称**：如果定义了 `Future` trait，考虑重命名或使用全限定路径

### 对于库开发者

1. **保持兼容性**：如果库支持多 Edition，继续使用显式导入
2. **避免定义 `Future` trait**：除非必要，否则不要定义与标准库冲突的 trait 名称
3. **文档更新**：在文档中说明库对 Rust 版本的要求

### 迁移检查清单

- [ ] 搜索代码中所有 `use std::future::Future;`，评估是否可以删除
- [ ] 检查项目中是否有自定义的 `Future` trait
- [ ] 检查依赖库中是否有 `Future` 相关的名称冲突
- [ ] 运行 `cargo check` 和 `cargo test` 确认无编译错误
- [ ] 更新团队编码规范，说明 prelude 的变化

## 技术细节

### Prelude 包含的内容

Rust 2024 Edition 的 prelude 新增了以下与异步相关的类型：

- `std::future::Future`

这使得以下代码无需任何导入即可编译：

```rust
fn spawn_task<T>(task: T) -> Box<dyn Future<Output = T::Output>>
where
    T: Future,
{
    Box::new(task)
}
```

### 与 `async/await` 的关系

`Future` trait 是 `async/await` 的底层基础。将其加入 prelude 是 Rust 异步生态系统成熟的重要标志：

- `async fn` 隐式返回实现 `Future` 的类型
- `.await` 操作依赖 `Future::poll` 方法
- 异步运行时（Tokio、async-std 等）围绕 `Future` trait 构建

## 版本兼容性

| Rust 版本 | Edition | `Future` 在 prelude 中？ |
|-----------|---------|------------------------|
| < 1.85    | 2021    | 否                     |
| >= 1.85   | 2021    | 否                     |
| >= 1.85   | 2024    | 是                     |

## 参考资源

- [Rust Edition Guide: Future in Prelude](https://doc.rust-lang.org/edition-guide/rust-2024/future-in-prelude.html)
- [std::prelude 文档](https://doc.rust-lang.org/std/prelude/)
