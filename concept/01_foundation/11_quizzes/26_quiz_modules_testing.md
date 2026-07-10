> **内容分级**: [综述级]

# 测验：模块系统与测试（L1 试点扩展）
>
> **EN**: Modules
> **Summary**: Quiz Modules Testing. Core Rust concept.
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: N/A
---

> **来源**: · [自测题库](../../00_meta/04_navigation/self_assessment.md) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
> [The Rust Programming Language — Ch7 Managing Growing Projects](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) ·
> [The Rust Programming Language — Ch11 Testing](https://doc.rust-lang.org/book/ch11-00-testing.html)
>
> **前置概念**:
> [Modules and Paths](../07_modules_and_items/11_modules_and_paths.md) ·
> [Testing Basics](../10_testing_basics/16_testing_basics.md)

---

> **Bloom 层级**: L2-L3
> **定位**: L1 嵌入式互动测验——验证模块系统（package/crate/module、可见性、路径）与测试（单元测试、集成测试、文档测试）核心概念的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

---

## 认知路径

> **认知路径**: 本节从 "测验" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 测验 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 测验 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与测验的适用边界。
5. **迁移应用**: 将 测验 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 测验 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 测验 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 测验 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: 测验 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 测验 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 测验 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "测验 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 测验 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 测验 规则被违反的直接信号。

> **反命题 3**: "其他语言对 测验 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 测验 具有语言特有的形态。

---

> **反向推理 1**: 如果程序在 测验 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 测验 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 一、模块系统

### Q1. 以下代码能否编译？解释 `mod`、`use` 和 `pub` 的关系

```rust
// src/main.rs
mod front_of_house {
    pub mod hosting {
        pub fn add_to_waitlist() {}
    }
}

fn main() {
    front_of_house::hosting::add_to_waitlist();
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译。

**解析**：

| 关键字 | 作用 |
|:---|:---|
| `mod` | 声明一个模块（Module），Rust 根据模块位置查找对应文件 |
| `pub` | 使项对外部可见；默认所有项都是私有的 |
| `use` | 将路径导入当前作用域，创建快捷方式 |

**模块（Module）查找规则**：

```rust,ignore
mod front_of_house; // 查找 src/front_of_house.rs 或 src/front_of_house/mod.rs
```

**可见性层级**：

| 修饰符 | 可见范围 |
|:---|:---|
| （默认） | 当前模块（Module）及其子模块 |
| `pub` | 任何地方 |
| `pub(crate)` | 当前 crate 内 |
| `pub(super)` | 父模块（Module） |
| `pub(in path)` | 指定路径内 |

**知识点**：Rust 的模块（Module）系统是"基于文件系统的显式树"，与 Python/JavaScript 的隐式模块不同。[→ 模块系统详解](../07_modules_and_items/11_modules_and_paths.md)

</details>

---

### Q2. 以下代码能否编译？`super` 和 `self` 的作用是什么？

```rust
mod outer {
    pub fn foo() {}

    mod inner {
        pub fn bar() {
            super::foo();
            self::baz();
        }

        fn baz() {}
    }
}

fn main() {}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译。

**解析**：

| 关键字 | 含义 | 示例 |
|:---|:---|:---|
| `self` | 当前模块（Module） | `self::baz()` = `inner::baz()` |
| `super` | 父模块（Module） | `super::foo()` = `outer::foo()` |
| `crate` | crate 根 | `crate::outer::foo()` |

**路径类型**：

```rust,ignore
// 绝对路径（推荐）
crate::outer::inner::bar();

// 相对路径
outer::inner::bar();
super::foo();  // 从 inner 模块引用 outer
```

**注意**：`self` 通常可省略，`self::baz()` 等价于 `baz()`。但在 `use` 语句中有特殊用途：

```rust,ignore
use self::inner::bar;     // 显式引用当前模块的 inner
use super::foo;           // 引用父模块的 foo
use crate::utils::helper; // 引用 crate 根的 utils
```

**知识点**：`super` 常用于测试模块（Module）访问被测代码的私有项（测试通常放在 `super` 模块中）。[→ 模块系统详解](../07_modules_and_items/11_modules_and_paths.md)

</details>

---

### Q3. 以下代码能否编译？解释 `use` 语句的多种写法

```rust
mod shapes {
    pub mod circle {
        pub fn area(r: f64) -> f64 { std::f64::consts::PI * r * r }
    }
    pub mod square {
        pub fn area(s: f64) -> f64 { s * s }
    }
}

use shapes::circle;
use shapes::square::area as square_area;

fn main() {
    println!("{}", circle::area(2.0));
    println!("{}", square_area(3.0));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出：

```
12.566370614359172
9
```

**解析**：

| `use` 写法 | 效果 |
|:---|:---|
| `use shapes::circle;` | 导入 `circle` 模块（Module），使用 `circle::area(...)` |
| `use shapes::square::area as square_area;` | 导入 `area` 函数并重命名为 `square_area` |
| `use shapes::{circle, square};` | 同时导入多个项（嵌套路径） |
| `use shapes::*;` | 通配导入（不推荐，除 prelude 外） |

**嵌套路径和 glob**：

```rust
use std::io::{self, Write, Read}; // self = std::io 本身
use std::collections::*;          // 导入所有公共项
```

**重导出（Re-export）**：

```rust,ignore
pub use shapes::circle; // 外部用户可通过 crate::circle 访问
```

**知识点**：`use` 只是创建别名，不复制代码。`pub use` 是构建 crate 公共 API 的常用技巧。[→ 模块（Module）系统详解](../07_modules_and_items/11_modules_and_paths.md)

</details>

---

## 二、单元测试与集成测试

### Q4. 以下测试代码的输出是什么？`#[cfg(test)]` 的作用是什么？

```rust
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }

    #[test]
    #[should_panic(expected = "attempt to add with overflow")]
    fn test_overflow() {
        let _ = i32::MAX + 1;
    }
}

fn main() {}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`cargo test` 输出：

```
running 2 tests
test tests::test_add ... ok
test tests::test_overflow ... ok
```

**解析**：

| 属性 | 作用 |
|:---|:---|
| `#[cfg(test)]` | 条件编译——只在测试模式下编译此模块（Module） |
| `#[test]` | 标记函数为测试函数 |
| `#[should_panic]` | 预期测试会 panic；若未 panic 则测试失败 |
| `use super::*;` | 导入父模块的所有公共项，使被测函数可用 |

**测试类型对比**：

| 类型 | 位置 | 访问范围 | 用途 |
|:---|:---|:---|:---|
| 单元测试 | `src/` 内 `#[cfg(test)]` mod | `pub` 项 | 测试单个函数/模块（Module） |
| 集成测试 | `tests/` 目录 | 仅 `pub` API | 测试 crate 的公共接口 |
| 文档测试 | `///` 中的代码块 | `pub` 项 | 验证文档示例 |

**常用断言宏（Macro）**：

```rust,ignore
assert!(condition);
assert_eq!(left, right);
assert_ne!(left, right);
assert!(result.is_ok(), "Expected Ok, got {:?}", result);
```

**知识点**：`#[cfg(test)]` 确保测试代码不会编译进最终产物。集成测试放在 `tests/` 目录下，每个文件是一个独立的二进制。[→ 测试详解](../10_testing_basics/16_testing_basics.md)

</details>

---

### Q5. 以下代码能否编译？集成测试如何访问被测 crate？

```rust,ignore
// tests/integration_test.rs
use my_project::add;

#[test]
fn test_add_integration() {
    assert_eq!(add(2, 3), 5);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译（假设 `my_project` 的 `lib.rs` 中 `pub fn add` 已定义）。

**解析**：

**集成测试的关键规则**：

1. 集成测试放在项目根目录的 `tests/` 文件夹下
2. 每个 `.rs` 文件编译为独立的测试二进制
3. 必须通过 crate 名（`my_project`）引用（Reference）被测库的 `pub` API

**项目结构**：

```
my_project/
├── Cargo.toml
├── src/
│   └── lib.rs          # pub fn add(...)
└── tests/
    ├── integration_test.rs  # use my_project::add;
    └── common/
        └── mod.rs        # 共享测试辅助代码
```

**共享辅助代码**：

`tests/common/mod.rs` 不会被视为测试文件（因为 `common` 不是 `.rs` 测试文件），但可被其他测试文件引用（Reference）：

```rust,ignore
// tests/integration_test.rs
mod common;
use common::setup;
```

**知识点**：集成测试验证 crate 的公共 API 契约。它们不能访问 `pub(crate)` 或私有项，这强制开发者从用户视角验证设计。[→ 测试详解](../10_testing_basics/16_testing_basics.md)

</details>

---

### Q6. 以下代码的输出是什么？解释 `Result` 类型的测试断言

```rust
fn may_fail(input: i32) -> Result<i32, &'static str> {
    if input > 0 {
        Ok(input * 2)
    } else {
        Err("Input must be positive")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ok() -> Result<(), &'static str> {
        let result = may_fail(5)?;
        assert_eq!(result, 10);
        Ok(())
    }

    #[test]
    fn test_err() {
        let result = may_fail(-1);
        assert!(result.is_err());
    }
}

fn main() {}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：两个测试都通过。

**解析**：

**返回 `Result` 的测试**：

```rust
#[test]
fn test_ok() -> Result<(), &'static str> {
    let result = may_fail(5)?; // 若 Err，测试自动失败
    assert_eq!(result, 10);
    Ok(()) // 必须返回 Ok(()) 表示成功
}
```

| 测试返回类型 | 成功 | 失败 |
|:---|:---|:---|
| `()` | 正常返回 | panic |
| `Result<(), E>` | `Ok(())` | `Err(_)` 或 panic |
| `Option<()>` | `Some(())` | `None` |

**优点**：测试中使用 `?` 传播错误，避免嵌套 `match`。

**断言 `Result` 的方法**：

```rust,ignore
assert!(result.is_ok());
assert!(result.is_err());
assert_eq!(result.unwrap(), expected);
assert_eq!(result.unwrap_err(), expected_err);
```

**知识点**：返回 `Result` 的测试函数使错误处理（Error Handling）测试更简洁，是 Rust 测试的惯用模式。[→ 测试详解](../10_testing_basics/16_testing_basics.md)

</details>

---

## 三、工作区与 crate 结构

### Q7. 以下项目结构中，`crate`、`package` 和 `module` 的关系是什么？

```
my_workspace/
├── Cargo.toml          # [workspace] 定义
├── src/
│   └── main.rs         # 二进制 crate
├── lib.rs              # 库 crate
└── tests/
    └── integration.rs
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 概念 | 说明 | 本例 |
|:---|:---|:---|
| **Package** | Cargo 的构建/发布单元；含一个 `Cargo.toml` | `my_workspace/` |
| **Crate** | 编译单元；可以是二进制（bin）或库（lib） | `main.rs` → bin crate；`lib.rs` → lib crate |
| **Module** | 代码组织单元；命名空间边界 | `mod` 定义的每个模块 |

**一个 Package 可包含多个 Crate**：

```toml
# Cargo.toml
[package]
name = "my_app"
version = "1.0.0"

[[bin]]
name = "cli"
path = "src/main.rs"

[[bin]]
name = "server"
path = "src/server.rs"

[lib]
name = "my_lib"
path = "src/lib.rs"
```

**常见布局**：

```
src/
├── lib.rs          # 库 crate（可被其他 crate 依赖）
├── main.rs         # 二进制 crate（依赖 lib.rs）
└── bin/
    ├── tool1.rs    # 额外二进制 crate
    └── tool2.rs
```

**知识点**：理解 package/crate/module 的层级关系是管理 Rust 项目结构的基础。[→ 模块系统详解](../07_modules_and_items/11_modules_and_paths.md)

</details>

---

### Q8. 以下代码能否编译？`pub(crate)` 和 `pub(super)` 的区别

```rust
mod outer {
    pub(crate) fn crate_visible() {}
    pub(super) fn parent_visible() {}

    mod inner {
        pub fn deep() {
            crate::outer::crate_visible();
            super::parent_visible();
        }
    }
}

fn main() {
    outer::crate_visible();
    outer::parent_visible();
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`parent_visible` is private

**解析**：

| 可见性 | 范围 | `main` 中可见？ |
|:---|:---|:---:|
| `pub(crate)` | 当前 crate 的任何地方 | ✅ |
| `pub(super)` | 仅父模块（`outer` 的父是 crate 根） | ❌（但 `outer` 内可见） |

**修正**：`main` 中只能访问 `crate_visible`：

```rust,ignore
fn main() {
    outer::crate_visible();    // ✅ pub(crate)
    // outer::parent_visible(); // ❌ pub(super) 仅 outer 的父模块可见
}
```

**使用场景**：

```rust
mod database {
    pub(crate) fn connect() {}     // 内部 API，crate 内可用
    pub(super) fn internal_helper() {} // 仅 database 的父模块可用
}
```

**知识点**：限制可见性是封装的核心。Rust 鼓励使用最严格的可见性（默认私有 → `pub(super)` → `pub(crate)` → `pub`）。[→ 模块系统详解](../07_modules_and_items/11_modules_and_paths.md)

</details>

---

## 四、综合应用

### Q9. 以下代码的输出是什么？解释 `assert_ne!` 和自定义错误消息

```rust
fn generate_id() -> u64 {
    42
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ids_are_unique() {
        let id1 = generate_id();
        let id2 = generate_id();
        assert_ne!(
            id1, id2,
            "IDs should be unique, but both were {}",
            id1
        );
    }
}

fn main() {}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 测试失败。

**输出**：

```
assertion `left != right` failed: IDs should be unique, but both were 42
```

**解析**：`generate_id()` 总是返回 42，因此两个 ID 相等，`assert_ne!` 失败。

**自定义错误消息**：所有断言宏（Macro）都支持格式化字符串：

```rust,ignore
assert!(condition, "message: {}", value);
assert_eq!(left, right, "expected {}, got {}", expected, actual);
assert_ne!(left, right, "should not be equal to {}", forbidden);
```

**修复方案**：使用随机或递增 ID：

```rust
use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

fn generate_id() -> u64 {
    COUNTER.fetch_add(1, Ordering::SeqCst)
}
```

**知识点**：自定义断言消息极大提升了测试失败时的调试效率。`assert_ne!` 在验证唯一性、非退化场景时特别有用。[→ 测试详解](../10_testing_basics/16_testing_basics.md)

</details>

---

### Q10. 以下代码能否编译？解释 `#[ignore]` 和 `#[should_panic]` 的适用场景

```rust
#[cfg(test)]
mod tests {
    #[test]
    #[ignore = "not yet implemented"]
    fn test_future_feature() {
        assert_eq!(2 + 2, 5);
    }

    #[test]
    #[should_panic]
    fn test_divide_by_zero() {
        let _ = 1 / 0;
    }

    #[test]
    fn test_normal() {
        assert_eq!(2 + 2, 4);
    }
}

fn main() {}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译。`cargo test` 默认运行 2 个测试（`test_normal` 和 `test_divide_by_zero`），忽略 `test_future_feature`。

**运行被忽略的测试**：

```bash
cargo test -- --ignored
cargo test -- --include-ignored  # 运行所有测试，包括忽略的
```

**属性对比**：

| 属性 | 作用 | 适用场景 |
|:---|:---|:---|
| `#[ignore]` | 跳过此测试 | 已知失败的测试、需要外部资源的测试、未完成的测试 |
| `#[should_panic]` | 预期 panic | 验证错误处理（Error Handling）路径、边界条件 |
| `#[should_panic(expected = "...")]` | 预期特定 panic 消息 | 验证正确的错误类型 |

**测试筛选**：

```bash
cargo test test_normal       # 运行名称匹配的测试
cargo test -- --nocapture    # 显示 println! 输出
cargo test -- --test-threads=1  # 单线程运行测试
```

**知识点**：`#[ignore]` 是管理"已知问题"测试的标准方式。`should_panic` 测试确保代码在错误条件下确实失败，而非静默继续。[→ 测试详解](../10_testing_basics/16_testing_basics.md)

</details>

---

## 五、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 模块与测试已内化 | 在项目中实践 Workspace + 集成测试 + CI 集成 |
| 7–9/10 | ✅ 核心概念掌握 | 为本工作区的 crates/ 编写集成测试 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Modules](../07_modules_and_items/11_modules_and_paths.md) · [Testing](../10_testing_basics/16_testing_basics.md) |
| 0–3/10 | 📚 建议重新开始 | 从 [Modules](../07_modules_and_items/11_modules_and_paths.md) 逐节阅读，拆分小项目练习 |

---

> **对应练习**: 建议为本工作区 `crates/` 下的任意 crate 编写集成测试

---

> **权威来源**: [The Rust Programming Language — Ch7](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) · [The Rust Programming Language — Ch11](https://doc.rust-lang.org/book/ch11-00-testing.html) · [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：模块系统与测试（L1 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：模块系统与测试（L1 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：模块系统与测试（L1 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：模块系统与测试（L1 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
