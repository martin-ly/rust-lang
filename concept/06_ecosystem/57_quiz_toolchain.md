> **内容分级**: [综述级]

# 测验：Rust 工具链（L6 试点扩展）
>
> **EN**: Toolchain
> **Summary**: ```toml [dependencies] serde = "^1.0" tokio = "~1.35" regex = "=1.10.2"``` <details> <summary>💡 点击展开答案与解析</summary> **答案**： | 约束 | 含义 | 允许范围 | 示例 | |:---|:---|:---|:---| | `^1.0` | 兼容更新 | `>=1.0.0, <2.0.0` | 1.0.0, 1.5.0, 1.99.9 ✅；2.0.0 ❌ | | `~1.35` | 近似更新 | `>=1.35.0, <1.36.0` | 1.35.0, 1.35.99 ✅

> **受众**: [进阶]
> **内容分级**: [综述级]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**:
> [The Cargo Book](https://doc.rust-lang.org/cargo/) ·
> [Clippy Documentation](https://doc.rust-lang.org/clippy/) ·
> [Miri Documentation](https://github.com/rust-lang/miri) ·
> [Rustfmt Documentation](https://github.com/rust-lang/rustfmt)
>
> **前置概念**:
> [Toolchain](./01_toolchain.md) ·
> Cargo Workspaces

---

> **Bloom 层级**: 应用 → 分析
> **定位**: L6 嵌入式互动测验——验证 Rust 工具链核心概念（Cargo 依赖管理、Clippy lint、Miri UB 检测、rustfmt、文档生成）的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、Cargo 依赖管理

### Q1. 以下 `Cargo.toml` 片段中，`^`、`~`、`=` 版本约束的含义是什么？

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

**知识点**：版本约束直接影响供应链安全。过于宽泛（`^1`）可能引入破坏变更，过于严格（`=x.y.z`）可能错过安全补丁。[→ Cargo 工具链详解](./01_toolchain.md)

</details>

---

### Q2. 以下命令的作用是什么？

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

**知识点**：`cargo check` 是日常开发最高效的命令。Clippy 是 Rust 的"高级 linter"，可捕获逻辑错误而不仅是语法错误。[→ 工具链详解](./01_toolchain.md)

</details>

---

### Q3. 以下 `Cargo.toml` 配置的作用是什么？

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
| `[workspace.dependencies]` | 集中定义依赖版本，子 crate 通过 `workspace = true` 引用 |

**子 crate 引用方式**：

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

### Q4. 以下代码中，Clippy 会发出什么警告？如何修复？

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

**知识点**：Clippy 拥有 600+ lint，是 Rust 代码质量的第一道防线。`cargo clippy --fix` 可自动修复部分警告。[→ Clippy 详解](./01_toolchain.md)

</details>

---

### Q5. 以下代码在 Miri 下运行会发生什么？

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

- `let ptr1 = &mut x as *mut u32`：创建独占引用 `&mut x`，再转换为原始指针
- `let ptr2 = &mut x as *mut u32`：再次创建独占引用 `&mut x`，**第一个引用失效**
- 在 Tree Borrows 模型中，`ptr1` 的写权限在 `ptr2` 创建时被撤销

**修复方案**——使用 `addr_of_mut!`（不创建中间引用）：

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

**知识点**：Miri 是 Rust 内存安全的终极验证工具。`&mut T as *mut T` 的转换模式在 Miri 下经常暴露别名问题，应优先使用 `addr_of_mut!`。[→ Miri 详解](../03_advanced/03_unsafe.md)

</details>

---

## 三、编译配置与目标平台

### Q6. 以下 `.cargo/config.toml` 配置的作用是什么？

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

**知识点**：`.cargo/config.toml` 是项目级构建配置，`.cargo/config.toml`（无点）是用户级全局配置。合理配置可显著改善编译性能和产物体积。[→ Cargo 工具链详解](./01_toolchain.md)

</details>

---

## 四、文档与发布

### Q7. 以下 `cargo doc` 命令的作用是什么？

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

```rust
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

```rust
/// # Panics
/// # Errors
/// # Safety（unsafe 函数必须）
/// # Examples
/// [`ModuleName`](crate::module::ModuleName) — 内部链接
```

**知识点**：文档测试是 Rust 独特的质量保证机制——确保文档中的示例代码始终可编译、可通过。[→ 工具链详解](./01_toolchain.md)

</details>

---

### Q8. 以下命令序列的作用是什么？发布 crate 到 crates.io 的正确流程是什么？

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

**知识点**：crates.io 是 Rust 生态的中心枢纽。谨慎的版本管理和发布流程是维护 crate 信誉的基础。[→ 生态安全实践](./19_security_practices.md)

</details>

---

## 五、综合应用

### Q9. 以下 `Cargo.toml` 中的 `[profile]` 配置如何影响编译产物？

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
| `opt-level = 1`（dev） | 基本优化，平衡编译速度和运行时性能 |
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

**知识点**：`codegen-units = 1 + lto = "fat"` 是追求极致性能的标准组合，但编译时间可能增加 2-5 倍。[→ Cargo 工具链详解](./01_toolchain.md)

</details>

---

### Q10. 以下命令如何帮助诊断编译问题？

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

**知识点**：Rust 的工具链生态非常完善。掌握诊断工具是高效开发和维护 Rust 项目的核心能力。[→ 工具链详解](./01_toolchain.md)

</details>

---

## 六、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 工具链已内化 | 探索 `cargo-make`、`cargo-xtask`、`cargo-bloat` 等高级工具 |
| 7–9/10 | ✅ 核心概念掌握 | 在 CI 中集成 `cargo clippy -- -D warnings` + `cargo audit` |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Toolchain](./01_toolchain.md)，实践 Workspace 配置 |
| 0–3/10 | 📚 建议重新开始 | 从 [Cargo Book](https://doc.rust-lang.org/cargo/) 官方文档开始 |

---

> **对应练习**: 无直接对应练习，建议通过修改本工作区 `.cargo/config.toml` 和 `Cargo.toml` 实践

---

> **权威来源**: [The Cargo Book](https://doc.rust-lang.org/cargo/) · [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html) · [Miri Book](https://rustc-dev-guide.rust-lang.org/miri.html)
