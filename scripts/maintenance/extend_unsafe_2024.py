#!/usr/bin/env python3
"""Extend concept/03_advanced/03_unsafe.md with 2024 Edition Unsafe/FFI content."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FILE = ROOT / "concept" / "03_advanced" / "03_unsafe.md"

text = FILE.read_text(encoding="utf-8")

# 1. Update TOC heading and add new subsections
old_toc = """  - [九、`unsafe_op_in_unsafe_fn`：权限分离模型（2024 Edition）](#九unsafe_op_in_unsafe_fn权限分离模型2024-edition)
    - [9.1 问题：权限的混淆](#91-问题权限的混淆)
    - [9.2 2024 Edition 的权限分离](#92-2024-edition-的权限分离)
    - [9.3 形式化模型：权限的模块化](#93-形式化模型权限的模块化)
    - [9.4 与 `unsafe extern` + `safe` 的关系](#94-与-unsafe-extern--safe-的关系)"""

new_toc = """  - [九、Unsafe/FFI 2024：权限分离与显式契约](#九unsafeffi-2024权限分离与显式契约)
    - [9.1 问题：权限的混淆](#91-问题权限的混淆)
    - [9.2 2024 Edition 的权限分离](#92-2024-edition-的权限分离)
    - [9.3 形式化模型：权限的模块化](#93-形式化模型权限的模块化)
    - [9.4 与 `unsafe extern` + `safe` 的关系](#94-与-unsafe-extern--safe-的关系)
    - [9.5 `unsafe extern` blocks：FFI 边界的显式 unsafe（Rust 2024）](#95-unsafe-extern-blocksffi-边界的显式-unsaferust-2024)
    - [9.6 `#[unsafe(...)]` 属性：链接级 unsafe 契约（Rust 2024）](#96-unsafe-属性链接级-unsafe-契约rust-2024)"""

assert old_toc in text, "TOC block not found"
text = text.replace(old_toc, new_toc)

# 2. Update section heading and stabilization note
old_heading = """## 九、`unsafe_op_in_unsafe_fn`：权限分离模型（2024 Edition）

> **稳定版本**: Rust 2024 Edition（默认行为） · **1.95 完全稳定**
> **形式化意义**: **调用者权限（unsafe fn 声明）与实现者权限（unsafe {} 块）的显式分离**"""

new_heading = """## 九、Unsafe/FFI 2024：权限分离与显式契约

> **稳定版本**: Rust 2024 Edition（默认行为） · **Rust 1.85.0 随 Edition 2024 稳定**
> **覆盖范围**: `unsafe_op_in_unsafe_fn`、`unsafe extern` blocks、`#[unsafe(...)]` 属性
> **形式化意义**: **调用者权限（unsafe fn / unsafe extern 声明）与实现者权限（unsafe {} 块）的显式分离**"""

assert old_heading in text, "Section heading not found"
text = text.replace(old_heading, new_heading)

# 3. Insert new subsections after 9.4
old_94_end = """三者共同构成 Rust **unsafe 权限的模块化体系**：从"块级"向"函数级/操作级"细化。

> **来源: [Rust 2024 Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)** `unsafe_op_in_unsafe_fn` clarifies the separation between caller and implementer unsafe obligations.
> **来源: [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)** `unsafe_op_in_unsafe_fn` lint.

---

## 相关概念链接"""

new_94_end = """三者共同构成 Rust **unsafe 权限的模块化体系**：从"块级"向"函数级/操作级"细化。

> **来源: [Rust 2024 Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)** `unsafe_op_in_unsafe_fn` clarifies the separation between caller and implementer unsafe obligations.
> **来源: [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)** `unsafe_op_in_unsafe_fn` lint.

### 9.5 `unsafe extern` blocks：FFI 边界的显式 unsafe（Rust 2024）

> **稳定版本**: Rust 1.82.0+ 可用 · **Rust 2024 Edition 强制要求**
> **RFC**: [RFC 3484 — Unsafe Extern Blocks](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html)
> **官方文档**: [Rust Edition Guide — Unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) · [Rust Reference — External blocks](https://doc.rust-lang.org/reference/items/external-blocks.html)

#### 9.5.1 问题：谁为 FFI 签名负责？

在 Rust 2021 及更早版本中，`extern` 块内的所有函数和静态量都隐式是 `unsafe` 的，但 `extern` 块本身**不必**写 `unsafe`：

```rust
// Rust 2021 及更早：extern 块本身没有 unsafe 标记
extern "C" {
    pub fn sqrt(x: f64) -> f64;        // 调用需要 unsafe {}
    pub fn strlen(p: *const c_char) -> usize; // 调用需要 unsafe {}
}
```

这里存在责任模糊：如果 `extern` 块内的签名写错了，调用时发生 UB，责任在**写 extern 块的人**还是**调用者**？
Rust 2024 的答案是：**写 extern 块的人负责保证签名正确**，因此 extern 块本身必须显式标记为 `unsafe`。

#### 9.5.2 语法与语义

```rust
// Rust 2024：extern 块必须 unsafe
unsafe extern "C" {
    // sqrt 签名简单、调用安全：可标记为 safe，调用时无需 unsafe {}
    pub safe fn sqrt(x: f64) -> f64;

    // strlen 需要合法指针：保持 unsafe，调用者需写 unsafe {}
    pub unsafe fn strlen(p: *const c_char) -> usize;

    // 默认未标注 safe/unsafe 的项，保守视为 unsafe
    pub fn free(p: *mut c_void);

    pub safe static TAU: f64;
}
```

| 写法 | 调用是否需要 `unsafe {}` | 适用场景 |
|:---|:---:|:---|
| `pub safe fn` / `pub safe static` | ❌ 不需要 | 签名已知正确、调用无额外前提 |
| `pub unsafe fn` / `pub unsafe static` | ✅ 需要 | 调用有额外安全前提（如有效指针） |
| 未标注 `safe`/`unsafe` | ✅ 需要（默认 unsafe） | 迁移中或保守处理 |

> **关键洞察**: `unsafe extern` 块表示"我作为作者保证块内所有签名正确"; `safe` 修饰表示"我还保证该项单独调用不会导致 UB"。

#### 9.5.3 版本迁移示例

```rust
// 2021 edition
extern "C" {
    pub fn sqrt(x: f64) -> f64;
}

// 2024 edition
unsafe extern "C" {
    pub safe fn sqrt(x: f64) -> f64;
}
```

迁移工具 `cargo fix --edition` 会自动将 `extern` 块改写为 `unsafe extern`，但不会自动推断哪些项可标 `safe`；开发者需根据 FFI 契约手动标注。

#### 9.5.4 边界与反模式

- `safe` 和 `unsafe` 关键字**仅允许出现在 `unsafe extern` 块内**；旧版 `extern` 块不能标注单个项。
- 在 2024 edition 中，`extern { ... }`（没有 `unsafe`）会编译错误：`extern blocks must be unsafe`。
- `unsafe extern` 在所有 edition 中都会触发 `unsafe_code` lint（若启用 `deny(unsafe_code)` 会被拒绝）。

### 9.6 `#[unsafe(...)]` 属性：链接级 unsafe 契约（Rust 2024）

> **稳定版本**: Rust 1.82.0+ 可用 · **Rust 2024 Edition 强制要求**
> **RFC**: [RFC 3325 — Unsafe Attributes](https://rust-lang.github.io/rfcs/3325-unsafe-attributes.html)
> **官方文档**: [Rust Edition Guide — Unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html)

#### 9.6.1 哪些属性是 unsafe 的？

Rust 2024 要求以下三个影响链接和符号的属性必须包裹在 `#[unsafe(...)]` 中：

| 属性 | 作用 | 安全要求 |
|:---|:---|:---|
| `no_mangle` | 关闭名称修饰，使用函数原名作为符号 | 必须保证全局符号不冲突 |
| `export_name = "..."` | 显式指定导出符号名 | 必须保证符号名唯一且合法 |
| `link_section = "..."` | 将项放入指定 ELF/Mach-O section | 必须保证 section 使用合法 |

这些属性影响链接器级别的全局命名空间，错误使用可能导致 UB（例如两个函数同名导致链接时冲突）。

#### 9.6.2 语法变化

```rust
// Rust 2021 及更早
#[no_mangle]
pub fn entry_point() {}

#[export_name = "my_custom_symbol"]
pub static FLAG: u32 = 1;

// Rust 2024
#[unsafe(no_mangle)]
pub fn entry_point() {}

#[unsafe(export_name = "my_custom_symbol")]
pub static FLAG: u32 = 1;
```

#### 9.6.3 为什么需要 unsafe 包装？

```rust
// 以下代码在旧版中只包含 safe 代码，但会崩溃（符号名冲突）
#[export_name = "malloc"]
fn foo() -> usize { 1 }

fn main() {
    println!("Hello, world!");
}
```

通过 `#[unsafe(export_name = "...")]`，编译器明确提示："此属性有编译器无法验证的安全要求，需要人工保证"。

#### 9.6.4 迁移与 lint

- 在 Rust 2024 中，`#[no_mangle]` / `#[export_name = ...]` / `#[link_section = ...]` 不加 `unsafe(...)` 会报错。
- 在 Rust 2021/2018/2015 中，Rust 1.82+ 已支持 `#[unsafe(...)]]` 写法，旧写法会触发 `unsafe_attr_outside_unsafe` lint（当前 allow-by-default，未来可能收紧）。
- `cargo fix --edition` 可自动将旧写法迁移为 `#[unsafe(...)]`。

> **来源**: [Rust 2024 Edition Guide — Unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) · [Unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html) · [RFC 3484](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html) · [RFC 3325](https://rust-lang.github.io/rfcs/3325-unsafe-attributes.html)

---

## 相关概念链接"""

assert old_94_end in text, "End of section 9.4 not found"
text = text.replace(old_94_end, new_94_end)

# 4. Update provenance/source line at the top of the document
old_source = """> **主要来源**: [TRPL: Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) · [Rust Reference: Unsafe Rust](https://doc.rust-lang.org/reference/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html) · [Rust Edition Guide 2024 — unsafe_op_in_unsafe_fn](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-op-in-unsafe-fn.html) · [Rust Edition Guide 2024 — unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html)"""

new_source = """> **主要来源**: [TRPL: Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) · [Rust Reference: Unsafe Rust](https://doc.rust-lang.org/reference/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html) · [RFC 3325](https://rust-lang.github.io/rfcs/3325-unsafe-attributes.html) · [RFC 3484](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html) · [Rust Edition Guide 2024 — unsafe_op_in_unsafe_fn](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-op-in-unsafe-fn.html) · [Rust Edition Guide 2024 — unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) · [Rust Edition Guide 2024 — unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html)"""

if old_source in text:
    text = text.replace(old_source, new_source)
else:
    print("Warning: top source line not found; skipping")

# 5. Update changelog
old_changelog = """**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成权威定义、unsafe 操作矩阵、UB 分类、Safety Contract 规范、思维导图、示例反例
- v1.1 (2026-05-13): 重构增强——定理一致性矩阵扩展至10行（⟹推理链）、反命题决策树×4、认知路径六步递进、章节过渡段落、层次一致性标注
- v1.3 (2026-05-13): Phase BC 形式化深化——新增§2.2b Unsafe Code Guidelines 完整 UB 分类（内存访问/类型系统/并发/其他四大类 15 子类 + UB 检测不可判定性定理）；新增§7.2b Miri 检测算法原理（核心解释循环、与 LLVM 优化假设关系、MIRIFLAGS 完整选项速查）
- v1.2 (2026-05-13): 深度重构——新增 §5.5 Stacked Borrows 操作语义、§5.6 Tree Borrows 演进；增强 §7.2 Miri 检测边界（覆盖范围表格+MIRIFLAGS使用）；补充层次一致性标注（L1/L4映射）与章节过渡段落"""

new_changelog = """**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成权威定义、unsafe 操作矩阵、UB 分类、Safety Contract 规范、思维导图、示例反例
- v1.1 (2026-05-13): 重构增强——定理一致性矩阵扩展至10行（⟹推理链）、反命题决策树×4、认知路径六步递进、章节过渡段落、层次一致性标注
- v1.3 (2026-05-13): Phase BC 形式化深化——新增§2.2b Unsafe Code Guidelines 完整 UB 分类（内存访问/类型系统/并发/其他四大类 15 子类 + UB 检测不可判定性定理）；新增§7.2b Miri 检测算法原理（核心解释循环、与 LLVM 优化假设关系、MIRIFLAGS 完整选项速查）
- v1.2 (2026-05-13): 深度重构——新增 §5.5 Stacked Borrows 操作语义、§5.6 Tree Borrows 演进；增强 §7.2 Miri 检测边界（覆盖范围表格+MIRIFLAGS使用）；补充层次一致性标注（L1/L4映射）与章节过渡段落
- v2.0 (2026-06-23): 全面对齐 Rust 2024 Edition Unsafe/FFI 变更——重写第九章，补充 `unsafe extern` blocks（RFC 3484）与 `#[unsafe(...)]` 属性（RFC 3325），更新稳定版本信息为 Rust 1.85.0"""

if old_changelog in text:
    text = text.replace(old_changelog, new_changelog)
else:
    print("Warning: changelog block not found; skipping")

FILE.write_text(text, encoding="utf-8")
print(f"Updated {FILE.relative_to(ROOT)}")
