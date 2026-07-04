> **内容分级**: [综述级]
> **本节关键术语**: Custom Subcommand · `cargo-<name>` · `cargo metadata` · `--message-format=json` · Cargo Plugin · `cargo-expand` · `cargo-audit` · `cargo-semver-checks` — [完整对照表](../00_meta/01_terminology/terminology_glossary.md)
>
# Cargo 子命令与插件生态

> **EN**: Cargo Subcommands and Plugins
> **Summary**: Explains how Cargo's custom subcommand system works, how tools integrate via `cargo metadata` and JSON messages, and surveys common plugins in the ecosystem.
> **受众**: [中级 → 高级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把“如何扩展 Cargo”讲清楚：从自定义子命令约定到常用插件选型，覆盖 Cargo 的工具集成接口。
> **前置概念**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **后置概念**: [Cargo Security CVEs](72_cargo_security_cves.md) · [DevOps and CI/CD](28_devops_and_ci_cd.md)

---

> **来源**: [Cargo — External Tools](https://doc.rust-lang.org/cargo/reference/external-tools.html) · [Cargo — Commands](https://doc.rust-lang.org/cargo/commands/cargo.html) · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — cargo metadata](https://doc.rust-lang.org/cargo/commands/cargo-metadata.html) ·
> [Cargo Book — Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html)


---

> **过渡**: 从 Cargo 子命令与插件生态 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Cargo 子命令与插件生态 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Cargo 子命令与插件生态 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。


---

> **定理 1** [Tier 2]: Cargo 子命令与插件生态 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Cargo 子命令与插件生态 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Cargo 子命令与插件生态 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。


## 📑 目录

- [Cargo 子命令与插件生态](#cargo-子命令与插件生态)
  - [📑 目录](#-目录)
  - [一、Cargo 的可扩展性设计](#一cargo-的可扩展性设计)
  - [二、自定义子命令](#二自定义子命令)
    - [命名约定](#命名约定)
    - [安装方式](#安装方式)
    - [别名](#别名)
  - [三、`cargo metadata` 与 JSON 消息](#三cargo-metadata-与-json-消息)
    - [`cargo metadata`](#cargo-metadata)
    - [`--message-format=json`](#--message-formatjson)
  - [四、常用插件速览](#四常用插件速览)
  - [五、编写自定义子命令的最佳实践](#五编写自定义子命令的最佳实践)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：自定义 Cargo 子命令的可执行文件命名规则是什么？](#测验-1自定义-cargo-子命令的可执行文件命名规则是什么)
    - [测验 2：`cargo metadata` 的输出格式是什么？](#测验-2cargo-metadata-的输出格式是什么)
    - [测验 3：`--message-format=json` 适合哪些工具集成场景？](#测验-3--message-formatjson-适合哪些工具集成场景)
    - [测验 4：为什么官方建议自定义子命令使用 CLI 而不是链接 `cargo` crate？](#测验-4为什么官方建议自定义子命令使用-cli-而不是链接-cargo-crate)
  - [权威来源索引](#权威来源索引)

---

## 一、Cargo 的可扩展性设计

Cargo 通过以下机制与第三方工具集成：

- **自定义子命令**: 任何名为 `cargo-<name>` 的可执行文件都可作为 `cargo <name>` 调用；
- **`cargo metadata`**: 以稳定 JSON 格式输出项目结构与依赖信息；
- **`--message-format=json`**: 在构建过程中输出编译消息、产物、build script 结果等；
- **环境变量**: 如 `CARGO`、`CARGO_MANIFEST_DIR` 等，供子命令感知当前 Cargo 上下文。

> [来源: Cargo Book — External Tools](https://doc.rust-lang.org/cargo/reference/external-tools.html)

---

## 二、自定义子命令

### 命名约定

创建一个名为 `cargo-hello` 的可执行文件并放到 `PATH` 中：

```bash
cargo hello
# 等价于执行 cargo-hello hello [args...]
```

Cargo 调用时会传入：

- 第一个参数：子命令可执行文件本身路径；
- 第二个参数：子命令名 `hello`；
- 后续参数：用户输入的其他参数。

### 安装方式

```bash
# 从 crates.io 安装
cargo install cargo-hello

# 安装后通常位于 ~/.cargo/bin
```

### 别名

在 `.cargo/config.toml` 中定义别名：

```toml
[alias]
b = "build"
t = "test"
fmt-check = "fmt -- --check"
```

---

## 三、`cargo metadata` 与 JSON 消息

### `cargo metadata`

```bash
cargo metadata --format-version 1 --no-deps
```

输出包括：

- package 名称、版本、路径；
- 依赖图；
- target 信息；
- features；
- workspace 成员。

Rust 生态中常用 `cargo_metadata` crate 解析该输出。

### `--message-format=json`

```bash
cargo build --message-format=json
```

JSON 消息类型：

| `reason` | 说明 |
|:---|:---|
| `compiler-message` | 编译器错误或警告 |
| `compiler-artifact` | 编译产物信息 |
| `build-script-executed` | build script 输出 |
| `build-finished` | 构建结束标记 |

> **关键洞察**: `--message-format=json` 是 IDE、代码分析工具和 CI 集成 Cargo 的主要接口。
>
> [来源: Cargo Book — External Tools — JSON messages](https://doc.rust-lang.org/cargo/reference/external-tools.html#json-messages)

---

## 四、常用插件速览

| 插件 | 用途 | 典型命令 |
|:---|:---|:---|
| **cargo-expand** | 展开宏（Macro），查看宏展开后的代码 | `cargo expand` |
| **cargo-watch** | 文件变更时自动运行命令 | `cargo watch -x check` |
| **cargo-tarpaulin** | 代码覆盖率 | `cargo tarpaulin` |
| **cargo-audit** | 检查依赖漏洞 | `cargo audit` |
| **cargo-deny** | 许可证/安全/依赖策略审查 | `cargo deny check` |
| **cargo-semver-checks** | 检测 SemVer 违规 | `cargo semver-checks` |
| **cargo-tree** | 查看依赖树（已内置） | `cargo tree` |
| **cargo-outdated** | 查找过时依赖 | `cargo outdated` |
| **cargo-udeps** | 查找未使用的依赖 | `cargo udeps` |
| **cargo-fuzz** | 模糊测试 | `cargo fuzz run target` |

> **注意**: 第三方插件的质量和维护状态各不相同，生产环境使用前需评估。

---

## 五、编写自定义子命令的最佳实践

1. **优先使用 CLI 而非 Cargo 库**: `cargo` crate 作为库的 API 不稳定；
2. **使用 `cargo metadata` 获取项目信息**: 格式稳定且版本化；
3. **读取 `CARGO` 环境变量**: 需要回调查看 Cargo 时使用同一二进制；
4. **处理 `--help`**: `cargo help <name>` 会传入 `--help`；
5. **提供清晰的错误信息**: 与 Cargo 风格保持一致。

```rust,ignore
fn main() {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    // 使用 cargo metadata 获取信息...
}
```

---

## 嵌入式测验

### 测验 1：自定义 Cargo 子命令的可执行文件命名规则是什么？

<details>
<summary>✅ 答案与解析</summary>

必须命名为 `cargo-<name>`，并放在 `PATH` 中。调用时使用 `cargo <name>`，Cargo 会自动找到并执行对应文件。

</details>

---

### 测验 2：`cargo metadata` 的输出格式是什么？

<details>
<summary>✅ 答案与解析</summary>

稳定版本化的 JSON。调用时应显式指定 `--format-version`，以规避未来格式变更风险。

</details>

---

### 测验 3：`--message-format=json` 适合哪些工具集成场景？

<details>
<summary>✅ 答案与解析</summary>

适合 IDE 显示编译错误、CI 解析构建结果、外部工具监控构建产物和 build script 输出等。

</details>

---

### 测验 4：为什么官方建议自定义子命令使用 CLI 而不是链接 `cargo` crate？

<details>
<summary>✅ 答案与解析</summary>

因为 `cargo` crate 的 API 不稳定，且链接的 Cargo 库版本可能与用户安装的 Cargo 二进制版本不一致。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Cargo Book — External Tools](https://doc.rust-lang.org/cargo/reference/external-tools.html) | ✅ 一级 | Cargo 外部工具官方文档 |
| [Cargo Book — cargo metadata](https://doc.rust-lang.org/cargo/commands/cargo-metadata.html) | ✅ 一级 | cargo metadata 官方文档 |
| [Cargo Book — Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) | ✅ 一级 | Cargo 环境变量官方文档 |

---

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.96.1 / Cargo 外部工具文档

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Cargo Book external tools 文档
