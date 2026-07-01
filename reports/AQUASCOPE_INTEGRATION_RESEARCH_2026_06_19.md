# Aquascope 可视化集成调研报告

> **报告日期**: 2026-06-19
> **调研目标**: 评估将 Brown University Cognitive Engineering Lab 的 Aquascope 所有权/借用可视化工具集成到本项目的可行性、成本与路径
> **对应权威来源**:
>
> [Aquascope GitHub](https://github.com/cognitive-engineering-lab/aquascope) ·
> [Brown University Interactive Book](https://rust-book.cs.brown.edu/) ·
> OOPSLA 2023 paper *A Grounded Conceptual Model for Ownership Types in Rust*

---

## 1. Aquascope 是什么

Aquascope 是 Brown University Cognitive Engineering Lab 开发的 Rust 程序交互式可视化工具。它能同时展示：

- **编译时视角**：借用检查器如何看待所有权、借用、生命周期
- **运行时视角**：程序实际执行时的内存状态变化

典型输出是一张分步骤的图表，每一步显示：

- 变量名与所有权限（读/写/拥有）
- 堆/栈中的值与指针
- 哪一行代码导致权限变化

Brown University 的交互式 Rust Book 在第 4 章（Ownership）大量使用 Aquascope 图表，其教学效果在 OOPSLA 2023/2024 论文中得到验证。

---

## 2. 当前版本与安装要求（2026-06-19）

Aquascope 在 GitHub 上已发布 **v0.4.0**（2026-05-04），但官方 README 与文档中仍主要引用 **v0.3.4 / v0.3.7**。集成到 mdBook 需要以下组件：

| 组件 | 版本/要求 | 说明 |
|:---|:---|:---|
| `mdbook-aquascope` | 0.3.7 / 0.4.0 | mdBook 预处理器 |
| `aquascope_front` | 对应 tag | 通过 git 安装，提供 `cargo-aquascope` |
| Rust nightly | v0.3.4: `nightly-2023-08-25`；v0.3.7: `nightly-2024-12-15`；v0.4.0: `nightly-2026-05-01` | 必须固定到发布说明指定的 nightly |
| rustup components | `rust-src`, `rustc-dev`, `llvm-tools-preview`, `miri` | 需要 miri 解释器 |
| 前置步骤 | `cargo +<nightly> miri setup` | 初始化 miri |

官方推荐安装命令（以 v0.3.7 为例）：

```bash
cargo install mdbook-aquascope --locked --version 0.3.7
rustup toolchain install nightly-2024-12-15 -c rust-src -c rustc-dev -c llvm-tools-preview -c miri
cargo +nightly-2024-12-15 install aquascope_front \
  --git https://github.com/cognitive-engineering-lab/aquascope \
  --tag v0.3.7 --locked
cargo +nightly-2024-12-15 miri setup
```
### 2.1 关键发现：官方指定的 nightly 已不可用

2026-06-19 实际执行时发现：

```text
$ rustup toolchain install nightly-2024-12-15
error: no release found for 'nightly-2024-12-15'
```
同样，`nightly-2023-08-25`（v0.3.4 所需）也已从 rustup 发布通道中移除。这意味着 **Aquascope 的“固定 nightly”安装路径在当前 rustup 环境下已断裂**。可能原因：

1. rustup 仅保留最近几个月的 nightly manifest，旧 nightly 会被清理。
2. 官方文档未及时更新可用工具链。
3. 需要本地构建/缓存对应 nightly 的 rustc-dev 组件，而当前环境没有。

因此，集成 POC 必须验证 **v0.4.0 是否能在当前 nightly（2026-06-17）上编译**，或寻找仍保留在 rustup 中的、Aquascope 可接受的 nightly 版本。

### 2.2 当前尝试

已启动在现有 nightly（`rustc 1.98.0-nightly (c1b22f44c 2026-06-17)`）上安装 `mdbook-aquascope v0.4.0`：

```bash
cargo install mdbook-aquascope --version 0.4.0 --force
```
**结果**：✅ 编译并安装成功（36.7s）。这说明 `mdbook-aquascope v0.4.0` 的预处理器本身可以在当前 nightly 上运行，不需要固定到旧 nightly。

接下来继续验证 `aquascope_front`（即 `cargo-aquascope`）是否也能在当前 nightly 上安装并运行。

**第一次尝试结果**：❌ 失败。`rustc_utils v0.15.2-nightly-2026-05-01` 找不到 rustc 内部 crate（`rustc_middle`、`rustc_mir_dataflow` 等），提示缺少 `rust-src`、`rustc-dev`、`llvm-tools-preview` 组件。这些组件在当前 nightly 上均可安装，已执行：

```bash
rustup component add rust-src rustc-dev llvm-tools-preview miri --toolchain nightly
```
**第二次尝试结果**：❌ 仍失败。安装 `rustc-dev` 后，`rustc_utils` 与 `miri` 内部 API 与当前 nightly（2026-06-17）不兼容：

- `rustc_utils` 中 `Unnormalized<TyCtxt<'_>, Ty<'_>>` 与 `Ty<'_>` 类型不匹配
- `miri` 中 `mir::RetagKind` 类型不存在

这些错误表明 Aquascope 的 rustc 内部依赖与当前 nightly 的编译器 ABI 已经脱节。

### 2.3 v0.4.0 所需 nightly 同样不可用

v0.4.0 的 `rust-toolchain.toml` 指定：

```toml
[toolchain]
channel = "nightly-2026-05-01"
components = ["rust-src", "rustc-dev", "llvm-tools-preview", "miri"]
```
但实际安装时报错：

```text
$ rustup toolchain install nightly-2026-05-01 -c rust-src -c rustc-dev -c llvm-tools-preview -c miri
error: no release found for 'nightly-2026-05-01'
```
截至 2026-06-19，Aquascope `main` 分支仍未更新该工具链锁定（仍为 `nightly-2026-05-01`）。

### 2.4 POC 结论

| 组件 | 在当前 nightly 上 | 在指定 nightly 上 | 结论 |
|:---|:---:|:---:|:---|
| `mdbook-aquascope v0.4.0` | ✅ 可安装 | 不需要固定 | 预处理器可用 |
| `aquascope_front v0.4.0` | ❌ API 不兼容 | `nightly-2026-05-01` 不可用 | **核心可视化引擎不可用** |
| 完整 mdBook 集成 | ❌ | ❌ | **当前不可行** |

**核心问题**：Aquascope 依赖 rustc 内部 API 与 miri，必须锁定到精确 nightly；但该 nightly 已从 rustup 发布通道移除，且上游 `main` 未更新到新 nightly。因此，**本地生成 Aquascope 可视化（mdBook 预处理器、静态截图、外部调用）均无法在当前环境下完成**。

> ⚠️ Aquascope 明确标注为 **research software**，接口尚未完全稳定，可能遇到 bug。

---

## 3. 集成方式

### 3.1 mdBook 预处理器（推荐路径）

在 `book.toml` 中启用：

```toml
[preprocessor.aquascope]
```
然后在 Markdown 中使用特殊代码块：

````markdown
```aquascope,interpreter
#fn main() {
let mut s = String::from("hello ");`[]`
s.push_str("world");`[]`
#}
```
````
其中 `\`[]\`` 标记解释器应展示状态的步骤。

### 3.2 静态截图/嵌入（当前不可行）

理论上可：

- 使用 Aquascope 生成 SVG/PNG 图表
- 作为静态图片嵌入 `concept/` 文档
- 维护成本低，但失去交互性

**但当前因 `aquascope_front` 无法安装，本地无法生成 Aquascope 图表，故此方案暂时不可行。**

### 3.3 链接到 Brown Book

最轻量的方案：在相关文档中直接链接到 Brown University Interactive Book 的对应 Aquascope 示例。已在 `concept/01_foundation/01_ownership.md` 和 `02_borrowing.md` 中部分实施。

---

## 4. 本项目集成可行性评估

### 4.1 优势

- **教学价值高**：对所有权、借用、生命周期等核心难点有直观解释
- **来源权威**：基于 Brown University 研究，OOPSLA 2023/2024 论文支撑
- **与本项目定位契合**：项目强调 L1-L4 分层概念，Aquascope 正好覆盖 L1-L2

### 4.2 障碍与风险

| 风险 | 严重程度 | 说明 |
|:---|:---:|:---|
| 工具链不可用 | **高** | 官方指定的 `nightly-2024-12-15` 已从 rustup 移除；v0.3.4 的 `nightly-2023-08-25` 同样不可用 |
| 工具链锁定 | 中 | 即使找到可用 nightly，也需与项目当前 `nightly 1.98.0 (2026-06-17)` 不同 |
| 安装复杂 | 中 | 需要 miri、llvm-tools、rustc-dev，CI/Contributor 环境负担大 |
| mdBook 兼容性 | 中 | 项目使用 mdbook v0.4.52，mdbook-aquascope 0.3.7 需要测试兼容性 |
| 文档元数据干扰 | 低-中 | `concept/` 文件顶部有大量 `>` 元数据块，mdBook 能渲染但 Aquascope 解析可能受影响 |
| 研究软件不稳定 | 中 | 接口可能变化，需要持续维护 |
| 中文文档 | 低 | Aquascope 输出为代码可视化，语言无关；但周边说明需本地化 |

### 4.3 工作量估算

| 阶段 | 工作量 | 内容 |
|:---|---:|:---|
| 调研与 POC | 0.5-1 天 | 安装工具链，在最小 mdBook 中跑通 Aquascope |
| 适配 `concept/` | 1-2 天 | 选择 5-10 个核心示例，转换为 Aquascope 代码块 |
| CI 集成 | 0.5-1 天 | 在 GitHub Actions 中安装 nightly + miri |
| 文档更新 | 0.5 天 | 更新 `book.toml`、添加贡献者说明 |

---

## 5. 推荐集成路径

### 方案 A：全量 mdBook 预处理器集成（阻塞）

需要 Aquascope 上游将工具链更新到 rustup 中仍可用的 nightly，且 `rustc_utils` / `miri` 内部 API 与新 nightly 兼容。当前不满足前提。

### 方案 B：静态截图嵌入（阻塞）

需要 `cargo-aquascope` 可运行。当前因工具链/API 不匹配无法生成图表。

### 方案 C：仅链接引用（推荐，已部分实施）

保持现状，在 `concept/` 中通过外部链接指向 Brown University Interactive Book 的 Aquascope 可视化。零维护成本、零工具链依赖，且能立即利用上游最新的可视化内容。建议在本轮补课冲刺中继续深化此方案。

---

## 6. 与本项目现有内容的对接建议

建议在以下文档优先嵌入 Aquascope：

| 文档 | 建议可视化内容 |
|:---|:---|
| `concept/01_foundation/01_ownership.md` | `String::from` 后所有权转移、`clone` 与移动语义 |
| `concept/01_foundation/02_borrowing.md` | Brown Book 的 5 种 Fixing Ownership Errors 案例 |
| `concept/01_foundation/03_lifetimes.md` | 引用生命周期与函数返回引用错误 |
| `concept/02_intermediate/04_error_handling.md` | `?` 传播与所有权交互（可选） |

---

## 7. 决策建议

- **短期（本轮补课冲刺内）**：采用 **方案 C 链接引用**，在 `concept/01_foundation/` 所有权/借用/生命周期文档中增加指向 Brown Book Aquascope 示例的链接。这是当前唯一可行的 Aquascope 相关教学增强。
- **中期（2-4 周）**：观望 Aquascope 上游是否更新 `rust-toolchain.toml` 到 rustup 可用的新 nightly；若更新，再尝试 **方案 A POC**。
- **长期**：若 Aquascope 工具链锁定问题持续，考虑用 Mermaid/自定义 SVG 实现轻量级所有权可视化替代方案，避免依赖 rustc 内部 API。

---

## 8. 参考文献

- Crichton, W., Gray, G., & Krishnamurthi, S. (2023). *A Grounded Conceptual Model for Ownership Types in Rust*. Proc. ACM Program. Lang., OOPSLA2. DOI: [10.1145/3622841](https://doi.org/10.1145/3622841)
- Crichton, W., & Krishnamurthi, S. (2024). *Profiling Programming Language Learning*. Proc. ACM Program. Lang., OOPSLA2. (Distinguished Paper.)
- Aquascope GitHub: <https://github.com/cognitive-engineering-lab/aquascope>
- Brown University Interactive Book: <https://rust-book.cs.brown.edu/>
