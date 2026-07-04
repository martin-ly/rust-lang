# 可见性与隐私（Visibility and Privacy）

> **EN**: Visibility and Privacy
> **Summary**: Rust 模块（Module）系统中 item 的可见性规则：`pub`、`pub(crate)`、`pub(super)`、`pub(in path)` 以及重导出的影响。
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Modules and Paths](../01_foundation/11_modules_and_paths.md) · [Names, Scopes and Resolution](../04_formal/40_names_and_resolution.md)
> **后置概念**: [API Naming Conventions](../02_intermediate/22_api_naming_conventions.md) · [Cargo SemVer Checks](../07_future/46_cargo_semver_checks_preview.md) · [Safety Boundaries](../05_comparative/04_safety_boundaries.md)
> **定理链**: Module Hierarchy → Visibility Rule → Public API Surface
> **主要来源**: [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) · [TRPL — Modules](https://doc.rust-lang.org/book/ch07-03-paths-for-referring-to-an-item-in-the-module-tree.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Oxide: The Essence of Rust](https://arxiv.org/abs/1903.00982) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)

---

---

## 认知路径

> **认知路径**: 本节从 "可见性与隐私（Visibility and Privacy）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 可见性与隐私（Visibility and Privacy） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 可见性与隐私（Visibility and Privacy） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与可见性与隐私（Visibility and Privacy）的适用边界。
5. **迁移应用**: 将 可见性与隐私（Visibility and Privacy） 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "可见性与隐私（Visibility and Privacy） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 可见性与隐私（Visibility and Privacy） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 可见性与隐私（Visibility and Privacy） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 可见性与隐私（Visibility and Privacy） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 可见性与隐私（Visibility and Privacy） 具有语言特有的形态。

## 一、可见性的核心问题

**可见性（visibility）** 与 **隐私（privacy）** 回答同一个问题：*“这个 item 在当前位置能否被使用？”*

Rust 的名称解析基于全局的命名空间层次结构。每个层级都可以视为某个 item。声明或定义一个新模块（Module），相当于在定义位置向层次结构中插入一棵新树。

---

## 二、默认规则

默认情况下，所有 item 都是**私有（private）**的，但有两个例外：

1. `pub` trait 的关联项默认是 public。
2. `pub` enum 的变体默认是 public。

当 item 被声明为 `pub` 时，它对外部世界可见。

```rust
struct Foo;                    // 私有
pub struct Bar { field: i32 }  // 公开结构体，但字段默认私有
pub enum State {               // 公开枚举，变体默认公开
    PubliclyAccessibleState,
    PubliclyAccessibleState2,
}
```

---

## 三、访问规则

### 1. Public item

如果 item 是 public 的，那么只要从模块（Module） `m` 可以访问该 item 的所有祖先模块，就可以从 `m` 外部访问它。也可以通过重导出（re-export）命名该 item。

### 2. Private item

如果 item 是 private 的，它可以被当前模块（Module）及其后代模块访问。

---

## 四、可见性修饰符

| 修饰符 | 含义 |
|:---|:---|
| `pub` | 全局公开 |
| `pub(crate)` | 当前 crate 内可见 |
| `pub(super)` | 父模块可见，等价于 `pub(in super)` |
| `pub(in path)` | 在指定祖先模块路径内可见 |
| `pub(self)` | 仅当前模块可见，等价于 private |

### 示例

```rust
pub mod outer_mod {
    pub mod inner_mod {
        pub(in crate::outer_mod) fn outer_mod_visible_fn() {}
        pub(crate) fn crate_visible_fn() {}
        pub(super) fn super_mod_visible_fn() {}
        pub(self) fn inner_mod_visible_fn() {}
    }
}
```

> **Edition 差异**: 2018 Edition 起，`pub(in path)` 的路径必须以 `crate`、`self` 或 `super` 开头。

---

## 五、重导出与可见性

`pub use` 可以公开地重导出 item，使外部 crate 通过新的路径访问原本私有的模块链中的 item。

```rust
pub use self::implementation::api;

mod implementation {
    pub mod api {
        pub fn f() {}
    }
}
```

- 外部 crate 通过 `implementation::api::f` 访问会收到隐私错误。
- 但通过 `api::f` 访问是允许的。

重导出相当于把“隐私链”短路到重导出点，而不是按命名空间层次正常传递。

---

## 六、实践建议

1. **最小公开表面**: 只把必要的 item 设为 `pub`，隐藏实现细节。
2. **使用 `pub(crate)` 管理内部 API**: 比 `pub` 更严格，同时允许 crate 内测试访问。
3. **重导出塑造 API**: 通过 `pub use` 把内部模块的公共接口提升到 crate 根，形成清晰的公共 API。
4. **可见性影响 semver**: 改变 public item 的签名或移除 public item 通常是破坏性变更。

---

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Modules and Paths](../01_foundation/11_modules_and_paths.md) | 可见性基于模块层次结构 |
| [Names, Scopes and Resolution](../04_formal/40_names_and_resolution.md) | 名称解析遵守可见性规则 |
| [API Naming Conventions](../02_intermediate/22_api_naming_conventions.md) | 可见性决定公共 API 边界 |
| [Cargo SemVer Checks](../07_future/46_cargo_semver_checks_preview.md) | 可见性变化影响语义化版本 |
