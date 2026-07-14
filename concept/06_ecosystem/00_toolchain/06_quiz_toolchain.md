> **内容分级**: [综述级]
> **代码状态**: ✅ 含可编译示例

# 测验：Rust 工具链（L6 试点扩展）
>
> **EN**: Toolchain
> **Summary**: Toolchain — An interactive quiz checking the Rust toolchain: Cargo dependencies, Clippy, Miri, rustfmt, and documentation.
> **受众**: [进阶]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: N/A
---

> **来源**: [Cargo Book](https://doc.rust-lang.org/cargo/index.html) · [rustup](https://rust-lang.github.io/rustup/) · [工具链](01_toolchain.md) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Clippy Documentation](https://doc.rust-lang.org/clippy/) ·
> [Miri Documentation](https://github.com/rust-lang/miri) ·
> [Rustfmt Documentation](https://github.com/rust-lang/rustfmt)
>
> **前置概念**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> [Toolchain](01_toolchain.md) ·
> Cargo Workspaces

---

> **Bloom 层级**: L3-L4
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题（能否编译 / 输出分析，本测验特色）+ 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`） 的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: L6 嵌入式互动测验——验证 Rust 工具链核心概念（Cargo 依赖管理、Clippy lint、Miri UB 检测、rustfmt、文档生成）的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、Cargo 依赖管理

本节将「Cargo 依赖管理」分解为若干主题： Q1. 以下 `Cargo.toml` 片段中，`^`、`~`、`=`…、Q2. 以下命令的作用是什么？与Q3. 以下 `Cargo.toml` 配置的作用是什么？。

### Q1. 🟢 以下 `Cargo.toml` 片段中，`^`、`~`、`=` 版本约束的含义是什么？

```toml
[dependencies]
serde = "^1.0"
tokio = "~1.35"
regex = "=1.10.2"
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 约束 | 含义 | 允许范围 | 示例 |
|:---|:---|:---|:---|
| `^1.0` | 兼容更新 | `>=1.0.0, <2.0.0` | 1.0.0, 1.5.0, 1.99.9 ✅；2.0.0 ❌ |
| `~1.35` | 近似更新 | `>=1.35.0, <1.36.0` | 1.35.0, 1.35.99 ✅；1.36.0 ❌ |
| `=1.10.2` | 精确锁定 | 仅 1.10.2 | 1.10.2 ✅；其他 ❌ |

**默认行为**：`serde = "1.0"` 等价于 `serde = "^1.0"`

**SemVer 与 Cargo 的关系**：

- Cargo 假设所有 crate 遵守 SemVer（语义化版本）
- `cargo update` 应用兼容更新（PATCH 和 MINOR），不应用 MAJOR 更新
- `cargo.lock` 锁定实际解析的版本，确保可复现构建

**知识点**：版本约束直接影响供应链安全。过于宽泛（`^1`）可能引入破坏变更，过于严格（`=x.y.z`）可能错过安全补丁。[→ Cargo 工具链详解](01_toolchain.md)

</details>

---

### Q2. 🟢 以下命令的作用是什么？

```bash
cargo build --release
cargo check
cargo clippy -- -D warnings
cargo test --all-targets
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 命令 | 作用 | 关键区别 |
|:---|:---|:---|
| `cargo build --release` | 发布模式编译，启用优化 | 编译慢，运行快；`target/release/` |
| `cargo check` | 仅类型检查，不生成机器码 | 比 `build` 快 3-5 倍；适合快速验证 |
| `cargo clippy -- -D warnings` | 运行 Clippy linter，并将警告提升为错误 | `-D warnings` 使 CI 在 lint 失败时中断 |
| `cargo test --all-targets` | 运行所有测试目标（lib、bin、tests、examples） | 默认只运行 lib 和 tests |

**编译模式对比**：

| 模式 | 优化 | 断言 | debug 信息 | 适用场景 |
|:---|:---:|:---:|:---:|:---|
| debug（默认） | ❌ | ✅ | 完整 | 开发、调试 |
| release | ✅ | ❌（默认） | 有限 | 生产部署 |

**注意**：`cargo check` 不运行代码生成和链接，因此无法检测链接错误。

**知识点**：`cargo check` 是日常开发最高效的命令。Clippy 是 Rust 的"高级 linter"，可捕获逻辑错误而不仅是语法错误。[→ 工具链详解](01_toolchain.md)

</details>

---

### Q3. 🟡 以下 `Cargo.toml` 配置的作用是什么？

```toml
[workspace]
members = ["crates/*"]
resolver = "3"

[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.35", default-features = false }
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

**Workspace（工作区）**：管理多个相关 crate 的集合，统一依赖版本和编译配置。

| 配置项 | 作用 |
|:---|:---|
| `members = ["crates/*"]` | 工作区包含 `crates/` 目录下的所有 crate |
| `resolver = "3"` | 使用 Cargo 的第 3 版依赖解析器（Edition 2024 默认） |
| `[workspace.dependencies]` | 集中定义依赖版本，子 crate 通过 `workspace = true` 引用（Reference） |

**子 crate 引用（Reference）方式**：

```toml
# crates/my_app/Cargo.toml
[dependencies]
serde = { workspace = true }
tokio = { workspace = true, features = ["rt-multi-thread"] }
```

**resolver = "3" 的改进**：

- 更积极的特性统一（feature unification）
- 更好的 dev-dependency 处理
- 与 Edition 2024 对齐

**知识点**：Workspace 是大型 Rust 项目的标准组织方式。集中依赖管理避免了版本漂移（version drift）。→ Cargo Workspace 详解

</details>

---

## 二、Clippy 与代码质量

「Clippy 与代码质量」部分包含 Q4. 以下代码中，Clippy 会发出什么警告？如何修复？ 与  Q5. 以下代码在 Miri 下运行会发生什么？ 两条主线，本节依次说明。

### Q4. 🟡 以下代码中，Clippy 会发出什么警告？如何修复？

```rust
fn main() {
    let v = vec![1, 2, 3];
    if v.len() == 0 {
        println!("Empty");
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：Clippy 警告：`len_zero`（或 `comparison_to_empty`）

**建议修复**：

```rust
fn main() {
    let v = vec![1, 2, 3];
    if v.is_empty() {
        println!("Empty");
    }
}
```

**Clippy lint 类别**：

| 类别 | 前缀 | 说明 |
|:---|:---|:---|
| Correctness | `correctness` | 可能正确的 bug |
| Suspicious | `suspicious` | 可疑代码，可能隐藏 bug |
| Complexity | `complexity` | 过于复杂的代码 |
| Performance | `performance` | 性能低效 |
| Style | `style` | 风格问题 |
| Pedantic | `pedantic` | 严格检查（默认关闭） |
| Nursery | `nursery` | 新 lint，可能不稳定 |
| Restrictions | `restriction` | 限制特定模式（默认关闭） |

**启用/禁用 lint**：

```rust
#![allow(clippy::len_zero)]      // 禁用特定 lint
#![warn(clippy::pedantic)]        // 启用 pedantic 类别
#![deny(clippy::correctness)]     // 将 correctness 提升为错误
```

**知识点**：Clippy 拥有 600+ lint，是 Rust 代码质量的第一道防线。`cargo clippy --fix` 可自动修复部分警告。[→ Clippy 详解](01_toolchain.md)

</details>

---

### Q5. 🟡 以下代码在 Miri 下运行会发生什么？

```rust
fn main() {
    let mut x = 0u32;
    let ptr1 = &mut x as *mut u32;
    let ptr2 = &mut x as *mut u32;

    unsafe {
        *ptr1 = 1;
        *ptr2 = 2;
    }
    println!("{x}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ Miri 报告 **Undefined Behavior**。

**Miri 错误信息**（Tree Borrows）：

```
error: Undefined Behavior: attempting to write to ... but tag ... does not have write permission
```

**解析**：

- `let ptr1 = &mut x as *mut u32`：创建独占引用（Reference） `&mut x`，再转换为原始指针（Raw Pointer）
- `let ptr2 = &mut x as *mut u32`：再次创建独占引用（Reference） `&mut x`，**第一个引用失效**
- 在 Tree Borrows 模型中，`ptr1` 的写权限在 `ptr2` 创建时被撤销

**修复方案**——使用 `addr_of_mut!`（不创建中间引用（Reference））：

```rust
use std::ptr::addr_of_mut;

fn main() {
    let mut x = 0u32;
    let ptr1 = addr_of_mut!(x);
    let ptr2 = addr_of_mut!(x);

    unsafe {
        *ptr1 = 1;
        *ptr2 = 2;
    }
    println!("{x}");
}
```

**Miri 的作用**：

- 检测**未定义行为**（UB），而非一般性 bug
- 实现 Rust 的内存模型（Stacked Borrows / Tree Borrows）
- 比 Valgrind/ASan 更精确地检测 Rust 特有的别名违规

**知识点**：Miri 是 Rust 内存安全（Memory Safety）的终极验证工具。`&mut T as *mut T` 的转换模式在 Miri 下经常暴露别名问题，应优先使用 `addr_of_mut!`。[→ Miri 详解](../../03_advanced/02_unsafe/01_unsafe.md)

</details>

---

## 三、编译配置与目标平台

本组测验聚焦 `.cargo/config.toml` 的配置语义：registry 源替换（`[source]` 段的重定向规则）、默认 target 与 linker 覆盖（交叉编译场景的常用配置）、rustflags 注入（`target-cpu=native` 等优化的正确注入位置）。这类配置是工具链测验中错误率最高的部分，因为配置文件位置（项目级 vs 用户级）与优先级规则容易被忽略——作答时务必先确认配置生效范围。

### Q6. 🟡 以下 `.cargo/config.toml` 配置的作用是什么？

```toml
[build]
rustflags = ["-C", "target-cpu=native"]

[target.x86_64-pc-windows-msvc]
linker = "rust-lld.exe"

[registries.crates-io]
protocol = "sparse"
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 配置段 | 作用 |
|:---|:---|
| `[build] rustflags` | 传递给 rustc 的额外标志；`target-cpu=native` 启用本地 CPU 的所有特性（如 AVX-512） |
| `[target.x86_64-pc-windows-msvc] linker` | 使用 `rust-lld`（LLVM 链接器）替代 MSVC 的 `link.exe`；链接速度更快 |
| `[registries.crates-io] protocol = "sparse"` | 使用稀疏索引协议下载 crate 元数据；显著减少初始下载时间和带宽 |

**其他常用配置**：

```toml
[env]
RUST_LOG = "debug"

[profile.release]
lto = true          # 链接时优化
opt-level = 3       # 最高优化级别
strip = true        # 移除 debug 符号
```

**知识点**：`.cargo/config.toml` 是项目级构建配置，`.cargo/config.toml`（无点）是用户级全局配置。合理配置可显著改善编译性能和产物体积。[→ Cargo 工具链详解](01_toolchain.md)

</details>

---

## 四、文档与发布

本节从 Q7. 以下 `cargo doc` 命令的作用是什么？ 与  Q8. 以下命令序列的作用是什么？发布 crate 到 crates.… 两个层面剖析「文档与发布」。

### Q7. 🟢 以下 `cargo doc` 命令的作用是什么？

```bash
cargo doc --open
cargo doc --no-deps
cargo doc --document-private-items
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 命令 | 作用 |
|:---|:---|
| `cargo doc --open` | 生成文档并在浏览器中打开 |
| `cargo doc --no-deps` | 仅生成本 crate 的文档，不生成依赖的文档 |
| `cargo doc --document-private-items` | 同时生成 `pub(crate)` 和私有项的文档 |

**文档测试（Doc Tests）**：

```rust,ignore
// doctest 语法示意（`my_crate::add` 需实际 crate 上下文）
/// 返回两数之和
///
/// # Examples
///
/// ```
/// assert_eq!(my_crate::add(2, 3), 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

`cargo test --doc` 会编译并运行文档中的代码示例。

**常用 doc 属性**：

```rust,ignore
/// # Panics
/// # Errors
/// # Safety（unsafe 函数必须）
/// # Examples
/// [`ModuleName`](crate::module::ModuleName) — 内部链接
```

**知识点**：文档测试是 Rust 独特的质量保证机制——确保文档中的示例代码始终可编译、可通过。[→ 工具链详解](01_toolchain.md)

</details>

---

### Q8. 🟡 以下命令序列的作用是什么？发布 crate 到 crates.io 的正确流程是什么？

```bash
cargo login
cargo publish --dry-run
cargo publish
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 命令 | 作用 |
|:---|:---|
| `cargo login` | 使用 crates.io API token 认证（token 从 crates.io/settings/tokens 获取） |
| `cargo publish --dry-run` | 模拟发布过程，验证打包和依赖，但不实际上传 |
| `cargo publish` | 实际发布到 crates.io（永久且不可撤销！） |

**发布前检查清单**：

1. ✅ `Cargo.toml` 中 `name`、`version`、`description`、`license`、`repository` 已填写
2. ✅ `cargo test` 全部通过
3. ✅ `cargo clippy` 无警告（或已评估）
4. ✅ `cargo publish --dry-run` 通过
5. ✅ `cargo doc` 生成正确
6. ✅ 版本号遵循 SemVer（MAJOR.MINOR.PATCH）

**重要限制**：

- 已发布的版本**不可删除或修改**（防止供应链攻击）
- 最多 10 个 crate 所有者
- yank（撤回）不会阻止已锁定版本的下载

**知识点**：crates.io 是 Rust 生态的中心枢纽。谨慎的版本管理和发布流程是维护 crate 信誉的基础。[→ 生态安全实践](../07_security_and_cryptography/01_security_practices.md)

</details>

---

## 五、综合应用

本节从 Q9. 以下 `Cargo.toml` 中的 `[profile]`… 与  Q10. 以下命令如何帮助诊断编译问题？ 两个层面剖析「综合应用」。

### Q9. 🟡 以下 `Cargo.toml` 中的 `[profile]` 配置如何影响编译产物？

```toml
[profile.dev]
opt-level = 1
incremental = true

[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 配置 | 影响 |
|:---|:---|
| `opt-level = 1`（dev） | 基本优化，平衡编译速度和运行时（Runtime）性能 |
| `incremental = true` | 增量编译，只重新编译变更部分 |
| `opt-level = 3`（release） | 激进优化（内联、循环展开、向量化） |
| `lto = "fat"` | 全程序链接时优化，跨 crate 内联 |
| `codegen-units = 1` | 单代码生成单元，允许最大优化，但编译串行化 |
| `panic = "abort"` | panic 时直接 abort，不展开栈；减小二进制体积 |

**优化级别对比**：

| `opt-level` | 说明 | 典型场景 |
|:---:|:---|:---|
| 0 | 无优化 | 调试 |
| 1 | 基本优化 | 快速开发迭代 |
| 2 | 默认发布优化 | 一般发布 |
| 3 | 激进优化 | 性能关键 |
| "s" | 体积优化 | 嵌入式/WASM |
| "z" | 极致体积优化 | 极端资源受限 |

**知识点**：`codegen-units = 1 + lto = "fat"` 是追求极致性能的标准组合，但编译时间可能增加 2-5 倍。[→ Cargo 工具链详解](01_toolchain.md)

</details>

---

### Q10. 🟡 以下命令如何帮助诊断编译问题？

```bash
RUST_BACKTRACE=1 cargo run
 cargo tree --duplicate
 cargo audit
 cargo outdated
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 命令 | 用途 |
|:---|:---|
| `RUST_BACKTRACE=1 cargo run` | panic 时打印栈跟踪，帮助定位崩溃点；`=full` 显示更详细信息 |
| `cargo tree --duplicate` | 检测依赖树中的重复 crate（可能导致编译错误或类型不匹配） |
| `cargo audit` | 检查依赖中的已知安全漏洞（基于 RustSec Advisory DB） |
| `cargo outdated` | 显示哪些依赖有更新的兼容版本可用（需安装 `cargo-outdated`） |

**诊断工具链全景**：

| 问题类型 | 工具 |
|:---|:---|
| 编译错误 | `rustc --explain E0XXX`、`cargo check` |
| 性能瓶颈 | `cargo flamegraph`、`perf` |
| 内存泄漏 | `valgrind`、` Miri `（检测 UB） |
| 二进制体积 | `cargo bloat`、`twiggy` |
| 安全漏洞 | `cargo audit`、`cargo deny` |
| 许可证合规 | `cargo deny`、`cargo-license` |

**知识点**：Rust 的工具链生态非常完善。掌握诊断工具是高效开发和维护 Rust 项目的核心能力。[→ 工具链详解](01_toolchain.md)

</details>

---

## 六、规范题型补充：单选 · 多选 · 判断

> 本节按四级题型规范补充单选、多选与判断题，知识点与 [Toolchain](01_toolchain.md) 权威页一致；
> 干扰项针对常见误解设计。

### Q11. 🟢【单选】`cargo build --release` 与默认 `cargo build` 的区别是？

- A. 仅输出目录不同（`target/release` vs `target/debug`）
- B. release 启用优化，默认关闭 `debug_assertions` 与整数溢出检查
- C. release 编译速度更快
- D. debug 产物体积更小

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：release profile 默认 `opt-level=3`、`debug-assertions=off`、`overflow-checks=off`，产物快但编译慢、调试信息少。A 只是表象（目录确实不同，但不是本质）；C 恰好相反（优化显著拉长编译时间）；D 也相反（debug 产物带调试符号通常更大）。溢出行为差异尤其重要：debug 下溢出 panic，release 下环绕——两类构建行为不同是经典 bug 来源。

</details>

---

### Q12. 🟡【单选】`rustup` 的核心职责是？

- A. Rust 的包管理器，负责下载依赖 crate
- B. 管理 Rust 工具链本身：stable/beta/nightly 版本、组件（clippy/rustfmt）与交叉编译 target 的安装与切换
- C. 代码格式化工具
- D. 把 crate 发布到 crates.io

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：分工要记清：**rustup 管工具链，cargo 管项目**。A、D 是 cargo 的职责；C 是 rustfmt（可作为 rustup 组件安装）。`rustup toolchain install nightly`、`rustup target add wasm32-unknown-unknown`、`rustup component add clippy` 都是日常命令；`rust-toolchain.toml` 则把工具链选择钉死在项目级。

</details>

---

### Q13. 🟡【多选】关于 Cargo 依赖解析与锁定，下列说法正确的有？（选出所有正确项）

- A. `serde = "1.0"` 默认等价于 `^1.0`，允许 1.x 内的兼容更新
- B. `Cargo.lock` 锁定确切版本；二进制（应用）项目应将其提交到版本控制
- C. 依赖图中同一 crate 的多个不兼容版本（如 1.x 与 2.x）可以共存
- D. `cargo update` 会无视 `Cargo.toml` 的版本约束随意升级

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：默认 `^` 约束允许"不破坏兼容"的升级（A）；lock 文件保证团队与 CI 构建可复现，应用提交、库传统上不提交（B）；Cargo 允许同一 crate 的多个 semver 不兼容版本并存并分别编译（C，`cargo tree -d` 可查重复）。D 错：`cargo update` 严格在 `Cargo.toml` 约束**之内**选择最新兼容版本，越界升级需先改清单。

</details>

---

### Q14. 🟢【判断】Clippy 是 Rust 的官方 lint 工具，在编译器默认警告之外提供代码风格、性能与正确性方面的数百条检查建议。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：Clippy 作为 rustup 组件分发（`rustup component add clippy`），lint 分为 correctness（默认 deny）、suspicious、style、complexity、perf、pedantic、nursery 等类别。工程实践：`cargo clippy -- -D warnings` 把所有警告升级为错误纳入 CI——本仓库的质量门 3 正是这一实践。

</details>

---

### Q15. 🟡【判断】`cargo vet` 用于供应链审计：记录并共享对第三方依赖的安全审查结论；本仓库质量门中的 `cargo vet --locked` 即属此类实践。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：`cargo vet`（Mozilla 发起）的思路是"依赖审查可共享"：项目维护 `supply-chain/` 下的审计记录（本仓库即有 `supply-chain/audits.toml`），声明每个依赖"被谁、按什么标准审过"，可导入 Mozilla/Firefox 等公开审计，避免全社区重复审查同一 crate。它与 `cargo audit`（查已知漏洞数据库）互补：一个管"有没有已知 CVE"，一个管"代码是否被可信方审过"。

</details>

---

## 七、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 工具链已内化 | 探索 `cargo-make`、`cargo-xtask`、`cargo-bloat` 等高级工具 |
| 7–9/10 | ✅ 核心概念掌握 | 在 CI 中集成 `cargo clippy -- -D warnings` + `cargo audit` |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Toolchain](01_toolchain.md)，实践 Workspace 配置 |
| 0–3/10 | 📚 建议重新开始 | 从 [Cargo Book](https://doc.rust-lang.org/cargo/index.html) 官方文档开始 |

---

> **对应练习**: 无直接对应练习，建议通过修改本工作区 `.cargo/config.toml` 和 `Cargo.toml` 实践

---

> **权威来源**: [The Cargo Book](https://doc.rust-lang.org/cargo/index.html) · [Clippy Lints](https://rust-lang.github.io/rust-clippy//master/index.html) · [Miri Book](https://rustc-dev-guide.rust-lang.org/miri.html)

## 嵌入式测验（Embedded Quiz）

理解「嵌入式测验（Embedded Quiz）」需要把握测验 1：本文件是 测验：Rust 工具链（L6 试点扩展） 的专项测…、测验 2：在 测验：Rust 工具链（L6 试点扩展） 的测验中，若遇…与测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层），本节依次展开。

### 测验 1：🟢 本文件是 测验：Rust 工具链（L6 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：Rust 工具链（L6 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：🟢 在 测验：Rust 工具链（L6 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：Rust 工具链（L6 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：🟢 专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>

## ⚠️ 反例与陷阱

工具链测验常以类型推断为考点，最直接的陷阱是标注与实际值不符。

### 反例：类型标注与字面量不匹配（rustc 1.97.0，--edition 2024 实测）

```rust,compile_fail,E0308
fn main() {
    let x: i32 = "hello"; // ❌ 类型不匹配
    let _ = x;
}
```

**实测错误**：`error[E0308]: mismatched types -- expected`i32`, found`&str``。

### ✅ 修正：让字面量类型与标注一致（或改标注为 `&str`）

```rust
fn main() {
    let x: i32 = 42; // ✅ 字面量类型与标注一致
    let _ = x;
}
```
