> **内容分级**: [基础级]

# Use Declarations（使用声明）
>
> **EN**: Use Declarations
> **Summary**: Use declarations: how Rust brings paths into scope, including `use`, `pub use`, nested imports, globs, re-exports, and visibility interplay.
> **受众**: [初学者]
> **Bloom 层级**: L1-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: F×App — 掌握模块（Module）路径的引入与重导出机制
> **定位**: 系统讲解 `use` 声明的语法、作用域规则、重导出与 glob 导入，帮助学习者建立清晰的模块（Module）命名空间心智模型。
> **前置概念**: [Modules and Paths](11_modules_and_paths.md) · [Items](39_items.md) · [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Preludes](35_preludes.md) · [API Naming Conventions](../../02_intermediate/05_modules_and_visibility/22_api_naming_conventions.md)
>
> **来源**: [The Rust Programming Language — Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) · [Rust Reference — Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html)

---

> **对应 Crate**: [`c03_control_fn`](../../crates/c03_control_fn)
> **对应练习**: [`exercises/src/modules/`](../../exercises/src/modules)
> **权威来源**: [Rust Reference — Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) · [TRPL — Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（Rust Reference、TRPL）

## 认知路径

> **认知路径**: 本节从“为什么需要 `use`”出发，依次建立路径引入、重导出、嵌套导入与 glob 导入的完整图景。

1. **问题识别**: 当模块层级较深时，如何简化路径书写？
2. **概念建立**: 掌握 `use`、`pub use`、嵌套导入、`use path::*` 的语法与语义。
3. **机制推理**: 通过 ⟹ 定理链将 `use` 声明、作用域与可见性规则串联起来。
4. **边界辨析**: 借助反命题/反例理解导入私有项、名称冲突、glob 遮蔽等问题。
5. **迁移应用**: 将 `use` 声明与 Prelude、API 命名规范等后置概念链接。

---

> **过渡**: 从 `use` 声明的直观描述转向其形式化定义，需要先把“简化路径”的直觉转化为作用域绑定的精确规则。
> **过渡**: 在建立 `use` 声明的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。
> **过渡**: 最后，将 `use` 声明与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 1]: `use path::Item;` 将路径绑定到当前作用域的短名 ⟹ 不创建新项，只创建别名，不影响原始可见性。
>
> **定理 2** [Tier 1]: `pub use path::Item;` 重导出内部路径 ⟹ 外部用户可通过当前模块访问该路径，构成 API 表面。
>
> **定理 3** [Tier 1]: Glob 导入 `use path::*;` 导入目标模块所有公开项 ⟹ 可能降低可读性并在名称冲突时引发编译错误。

---

> **反向推理 1** [Tier 1]: 若编译器报错 `unresolved import` 或 `private import` ⟸ 应检查路径是否正确、目标项是否 `pub`、以及 `use` 所在模块的可见性。
>
> **反向推理 2** [Tier 1]: 若公共 API 表面与内部模块结构不一致 ⟸ 考虑使用 `pub use` 进行重导出，隐藏实现细节。

---

## 📑 目录

- [Use Declarations（使用声明）](#use-declarations使用声明)
  - [认知路径](#认知路径)
  - [📑 目录](#-目录)
  - [一、核心命题](#一核心命题)
  - [二、`use` 基本语法](#二use-基本语法)
  - [三、路径形式](#三路径形式)
  - [四、`pub use` 重导出](#四pub-use-重导出)
  - [五、嵌套导入与 Glob](#五嵌套导入与-glob)
  - [六、反例与边界测试](#六反例与边界测试)
    - [6.1 导入私有项](#61-导入私有项)
    - [6.2 名称冲突](#62-名称冲突)
    - [6.3 Glob 导入遮蔽标准库](#63-glob-导入遮蔽标准库)
  - [七、权威来源索引](#七权威来源索引)

---

## 一、核心命题

> **命题 1**: `use` 声明将某个路径绑定到当前作用域的短名，**不创建新项**，只创建别名。
>
> **命题 2**: `pub use` 可以把内部路径重导出为当前模块的公共 API。
>
> **命题 3**: Glob 导入 `use path::*` 导入所有公开项，但可能降低可读性并导致名称冲突。
>
> **命题 4**: `use` 可以解构枚举（Enum）变体、结构体（Struct）字段路径，以及嵌套模块。

---

## 二、`use` 基本语法

> (Source: [Rust Reference — Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html))

```rust
mod kitchen {
    pub fn cook() {}
}

use kitchen::cook; // 将 kitchen::cook 引入当前作用域

fn main() {
    cook();
}
```

**绑定到不同名字**:

```rust
use kitchen::cook as prepare;
```

---

## 三、路径形式

| 形式 | 说明 | 示例 |
|:---|:---|:---|
| 绝对路径 | `crate::`、`self::`、`super::` | `use crate::module::Item;` |
| 相对路径 | 从当前模块开始 | `use self::sub::Item;` |
| `super` | 父模块 | `use super::ParentItem;` |
| `crate` | 当前 crate 根 | `use crate::utils::helper;` |

```rust
mod outer {
    pub const VAL: i32 = 1;

    mod inner {
        pub fn print() {
            println!("{}", super::VAL); // 使用 super 访问父模块
        }
    }
}
```

---

## 四、`pub use` 重导出

> (Source: [TRPL — Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html))

```rust
mod backend {
    pub struct User;
}

mod api {
    pub use crate::backend::User; // 重导出
}

fn main() {
    let _u = api::User; // 看起来 User 属于 api 模块
}
```

> **关键洞察**: `pub use` 是 Rust API 设计中常用的"门面模式（Facade）"工具，可将复杂内部结构隐藏，对外呈现简洁接口。

---

## 五、嵌套导入与 Glob

```rust
// 嵌套导入
use std::collections::{HashMap, HashSet, BTreeMap};

// 嵌套 + 重命名
use std::io::{self, Write as IoWrite};

// Glob（谨慎使用）
use std::fmt::*;
```

> **使用建议**:
>
> - 优先使用具名导入，明确依赖。
> - glob 导入适合 prelude 模式或测试模块中的 `super::*`。
> - 避免在库代码顶部使用 `use crate::*`，这会隐藏依赖关系。

---

## 六、反例与边界测试

### 6.1 导入私有项

```rust,compile_fail
mod inner {
    fn secret() {}
}

use inner::secret; // ❌ 函数 `secret` 是私有的
```

**修正**: 将 `secret` 标记为 `pub`。

### 6.2 名称冲突

```rust,compile_fail
mod a { pub fn foo() {} }
mod b { pub fn foo() {} }

use a::foo;
use b::foo; // ❌ `foo` 引入冲突

fn main() {
    foo();
}
```

**修正**: 使用别名 `use b::foo as b_foo;`。

### 6.3 Glob 导入遮蔽标准库

```rust,compile_fail
use std::io::*;

fn read() {} // 如果某个 trait/类型也叫 read，可能产生歧义
```

**修正**: 显式导入所需项。

---

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | ✅ 一级 | 模块与 use 的入门讲解 |
| [Rust Reference — Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) | ✅ 一级 | 完整语法规范 |
