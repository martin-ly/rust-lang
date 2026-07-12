# 测验：版本演进、Edition 机制与前沿特性（L7）

> **EN**: Version Evolution, Editions and Preview Features Quiz
> **Summary**: L7 standalone quiz on Rust's release train, edition mechanism, stabilized features in 1.90–1.97, and the status semantics of nightly preview features tracked for 1.98+.
> **受众**: [进阶]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` L7 前沿层独立测验。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**: [Rust Editions](../00_version_tracking/02_editions.md) · [Rust 发布流程](../00_version_tracking/03_rust_release_process.md) · [Rust 1.96 稳定特性](../00_version_tracking/rust_1_96_stabilized.md) · [Rust 1.97.0 稳定特性](../00_version_tracking/rust_1_97_stabilized.md) · [Rust 1.98+ 前沿特性预览](../00_version_tracking/rust_1_98_preview.md) · [Rust Blog — Announcing Rust 1.97.0](https://blog.rust-lang.org/2026/07/09/Rust-1.97.0/)（P2 生态官方发布信息，curl 200 实测 2026-07-13）
>
> **前置概念**:
> [Rust 版本跟踪](../00_version_tracking/01_rust_version_tracking.md) ·
> [Rust Editions](../00_version_tracking/02_editions.md) ·
> [Rust 发布流程](../00_version_tracking/03_rust_release_process.md) ·
> [Rust 1.97.0 稳定特性](../00_version_tracking/rust_1_97_stabilized.md) ·
> [Rust 工具链](../../06_ecosystem/00_toolchain/01_toolchain.md)

---

> **Bloom 层级**: L2-L3
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题 + 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`）的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: 验证学习者对 Rust 版本治理机制（发布火车、Edition）、1.90–1.97 稳定特性谱系与前沿特性状态语义的掌握。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、发布火车与 Edition 机制

本节考查版本治理基础：Q1 发布火车周期，Q2 Edition 机制四条陈述的辨析。

### Q1. 🟢【单选】Rust 的"发布火车"（release train）模型中，新 stable 版本的发布周期是？

- A. 每两周
- B. 每六周
- C. 每六个月
- D. 每年一次

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：Rust 使用三个频道（Nightly / Beta / Stable）构成发布火车模型，Beta 与 Stable 均为**六周一次**：每六周从 Nightly 切出 `beta` 分支作为下一个稳定版候选，六周后 Beta 提升为 Stable。(Source: [Rust 发布流程](../00_version_tracking/03_rust_release_process.md))

**常见误解**：六个月的节奏容易与 Edition（约 2–3 年一次）或某些 Linux 发行版混淆；两周是部分 crate 生态项目的节奏，不是语言本身的发布周期。

</details>

---

### Q2. 🟢 以下关于 Edition 机制的四条陈述，哪一条与 [Rust Editions](../00_version_tracking/02_editions.md) 的定义一致？

| 选项 | 陈述 |
|:---|:---|
| A | 设置 `edition = "2024"` 后，所有依赖必须同步升级到 2024 edition |
| B | 每个 crate 可独立选择 edition，同一编译单元内可混用不同 edition 的依赖 |
| C | `rust-version` 与 `edition` 是同一字段的两个名字 |
| D | 一个 `rustc` 版本只能编译一个 edition 的代码 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B 正确。

**解析**：Edition 是 Rust 在保持向后兼容前提下引入非兼容语法/语义变更的机制。关键原则：每个 crate **独立**选择 edition，依赖的 edition 不影响当前 crate 的编译（A 错）；`edition` 控制语法/语义版本，`rust-version` 声明最低编译器版本，是不同维度的约束（C 错）；同一 `rustc` 版本可编译多个 edition（D 错）。迁移使用 `cargo fix --edition`。

</details>

---

### Q3. 🟡【单选】下列 Edition 与其稳定版本的对应，哪一项正确？

- A. Edition 2018 — Rust 1.0
- B. Edition 2021 — Rust 1.31
- C. Edition 2024 — Rust 1.85
- D. Edition 2015 — Rust 1.56

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

**解析**：对应关系为 2015 → 1.0（初始版本）、2018 → 1.31（模块系统简化、`dyn Trait` 显式化）、2021 → 1.56（prelude 新增 `TryFrom`/`TryInto`、数组 `IntoIterator`）、**2024 → 1.85**（`if let` 临时作用域收窄、`gen` 关键字保留、异步闭包、never type fallback）。

</details>

---

## 二、1.90–1.97 稳定特性谱系

本节考查 1.90–1.97 稳定特性谱系：Q4 辨析 `rust-version` 与 `edition` 字段，Q5 识别 1.95–1.96 的稳定特性。

### Q4. 🟡 以下 `Cargo.toml` 片段中，哪个字段声明的是"最低编译器版本"而非"语法版本"？

```toml
[package]
name = "demo"
version = "0.1.0"
edition = "2024"
rust-version = "1.94"
```

| 选项 | 判断 |
|:---|:---|
| A | `edition` 声明最低编译器版本 |
| B | `rust-version` 声明最低编译器版本 |
| C | 两个字段语义完全相同 |
| D | `version` 字段控制语法版本 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：`rust-version = "1.94"` 声明该 crate 要求的**最低 rustc 版本**（MSRV），工具链低于此版本时 Cargo 拒绝构建；`edition = "2024"` 选择**语法/语义版本**，决定 `gen` 关键字保留、`if let` 作用域等语言行为。两者是不同维度的约束，混用是常见配置错误。(Source: [Rust Editions](../00_version_tracking/02_editions.md) 反命题 3)

</details>

---

### Q5. 🟡【多选】下列哪些特性是在 Rust 1.95–1.96 中稳定的？（选出所有正确项）

- A. `cfg_select!` 宏（1.95，编译期 cfg 条件选择）
- B. `assert_matches!` / `debug_assert_matches!`（1.96）
- C. `core::range` 的 `Copy` 范围类型（1.96，RFC 3550）
- D. `async fn` in trait（RPITIT）

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：1.95 稳定了 `cfg_select!` 宏、`if let` guards on match arms、路径段关键字重命名导入与 PowerPC 内联汇编；1.96 稳定了 `assert_matches!`/`debug_assert_matches!`（未进 prelude，需显式导入）、`expr` 元变量用于 `cfg`、以及 `core::range::Range<T>` 等实现 `Copy` + `IntoIterator` 的新范围类型（RFC 3550）。D 错：RPITIT（`impl Trait` in trait return position）稳定于 **1.75.0**（2023-12-28），远早于 1.95——[rust_1_90_stabilized](../00_version_tracking/rust_1_90_stabilized.md) 的版本勘误表专门澄清了这一点。

</details>

---

### Q6. 🟡【判断】Rust 1.93 稳定的 `String::into_raw_parts` / `Vec::into_raw_parts` 将容器拆分为原始指针、长度与容量三元组，便于与 FFI 或 Wasm 线性内存零拷贝交互。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：1.93 的「`String` / `Vec` 原始部分拆分」：`let (ptr, len, cap) = v.into_raw_parts();` 便于与外部运行时交互。同版本还稳定了 `MaybeUninit` 增强 API（`assume_init_ref`、`write_copy_of_slice` 等）与 `VecDeque::pop_front_if` / `pop_back_if` 条件弹出。(Source: [Rust 1.93 稳定特性](../00_version_tracking/rust_1_93_stabilized.md))

</details>

---

### Q7. 🔴【单选】关于 Rust 1.97.0（2026-07-09 stable）的变更，下列哪一项**不属于**该版本？

- A. `must_use` lint 扩展至 `Result<T, !>` 与 `ControlFlow<!, T>`
- B. Cargo 新增 `build.warnings` 配置与 `resolver.lockfile-path`
- C. rustdoc 的 `--emit` 与 `--remap-path-prefix` 稳定化
- D. `generic_const_exprs` 完整稳定，允许 const 参数任意运算

<details>
<summary>✅ 答案与解析</summary>

**答案：D**

**解析**：1.97 的变更集中在语言（`must_use` 对 uninhabited 错误类型的处理、`dead_code_pub_in_binary` lint、import 中 `self` 的放宽、新 target feature）、Cargo（`build.warnings`、`resolver.lockfile-path`、`-m` 简写）、Rustdoc（`--emit`、`--remap-path-prefix` 稳定化）等。D 错：`generic_const_exprs` 截至 1.97 仍是 nightly 特性——stable 边界仍是 min_const_generics（const 参数参与的运算式会被编译期拒绝），详见 [Const Generics](../../02_intermediate/01_generics/02_const_generics.md) §三与§七反例。

</details>

---

### Q8. 🔴 某库作者在 1.97 stable 上写下如下代码，编译器拒绝。按稳定边界，根因是什么？

```rust,ignore
fn double_size<const N: usize>() -> [u8; N * 2] {
    [0; N * 2]
}
```

| 选项 | 判断 |
|:---|:---|
| A | 语法错误，`N * 2` 应写为 `N.mul(2)` |
| B | const 参数参与运算属于 `generic_const_exprs`，stable 仅支持 min_const_generics 的独立参数形态 |
| C | `u8` 不允许作为数组元素类型 |
| D | 应改用 `Vec<u8>`，数组不支持 const 泛型 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：stable 的 const generics（min_const_generics，1.51 起）只允许 const 参数以**独立**形态出现在数组长度等位置（如 `[T; N]`）；`N * 2` 这类 const 参数参与的运算式属于 `generic_const_exprs` 特性门，截至 1.97 未稳定。工程绕行：要求调用方直接传入已算好的 const，或用 where 子句的相等约束（[Const Generics](../../02_intermediate/01_generics/02_const_generics.md) §七 反例 1）。A/C/D 均为干扰项。

</details>

---

## 三、前沿特性状态语义

本节考查前沿特性状态语义：Q9 预研页与 1.98+ 预览的状态含义，Q10 Beta 频道的合入规则。

### Q9. 🔴【多选】关于 `03_preview_features/` 预研页与 1.98+ 预览的状态语义，下列说法正确的有？（选出所有正确项）

- A. 标记 🧪 Nightly 实验性的特性可直接用于生产 stable 工具链
- B. 预研页标注的"预计稳定时间"高度不确定，以官方发布为准
- C. `~const` 等 nightly 实验语法是过渡方案，不代表最终语言方向
- D. 预研页跟踪 nightly 版本并随 RFC / MCP 进展更新状态

<details>
<summary>✅ 答案与解析</summary>

**答案：B、C、D**

**解析**：预研页统一标注 `#[experimental]` / `#[nightly_only]` 与"特性集高度不确定，稳定时间和具体内容以官方发布为准"（B、D 正确）；A 错：nightly 实验特性需要 feature gate，不能用于 stable 生产构建；C 正确：以 const trait impl 预研页为例，`~const` 语法已被明确视为过渡方案，未来可能被 `eff`/`with` 统一效果语法取代，但 `const` 作为效果语义持续演进。

</details>

---

### Q10. 🟡【判断】Beta 频道每六周从 Nightly 切出后，仍接受新特性的合入，因此 Beta 与 Nightly 的特性集完全相同。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：按发布流程，Beta 分支是"下一稳定版的预览"，切出后**仅接受关键修复**，不再合入新特性；Nightly 则继续接收面向下下个周期的新特性。因此 Beta 特性集是 Nightly 在切分支时刻的快照子集，六周后提升为 Stable。(Source: [Rust 发布流程](../00_version_tracking/03_rust_release_process.md))

</details>

---

## 四、认证工具链与版本下沉

本节考查认证工具链与版本下沉：Q11 Ferrocene 的定位（2026-07-12 更正后），Q12 版本跟踪关系，Q13 1.91–1.92 变更归属。

### Q11. 🟢【单选】按本知识库 2026-07-12 更正后的定位，Ferrocene 是？

- A. Rust 的 nightly 实验特性，待上游稳定
- B. Ferrous Systems 交付、TÜV SÜD 鉴定的下游认证工具链发行版（ISO 26262 ASIL D / IEC 61508 SIL 3 / IEC 62304 Class C）
- C. rustc 的一个 codegen 后端
- D. Rust Foundation 的官方稳定版别名

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：[Ferrocene 权威页](../03_preview_features/12_ferrocene_preview.md) 的定位声明明确：Ferrocene 不是待稳定语言特性，而是对上游 rustc 特定版本执行完整鉴定（qualification）流程后发布的**下游认证工具链发行版**，附监管机构可审查的证据包；页面保留在 `03_preview_features/` 仅为路径稳定。认证工具链生态对比见 [认证工具链与认证包清单](../../04_formal/04_model_checking/10_certified_toolchains_and_packages.md)。

</details>

---

### Q12. 🟡【判断】Ferrocene 26.02.0 跟踪上游 rustc 1.92 而非最新 stable，这种"认证延迟"是工具链缺陷。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：按 Ferrocene 权威页 §2.3，认证延迟是**设计使然**：鉴定流程（qualification）需要针对特定上游版本产出完整证据包，认证版必然滞后上游 stable；Ferrocene 采用季度发行节奏（26.02.0 于 2026-02 发布，含上游 1.91–1.92 变更）。安全关键项目选型时应把"认证版本滞后"作为既定约束纳入规划，而非视为缺陷。

</details>

---

### Q13. 🟡【多选】下列哪些变更属于 Rust 1.91–1.92 版本线？（选出所有正确项）

- A. 借用检查器优化：改进算法与缓存机制，编译时间减少 10–20%（1.91）
- B. `MaybeUninit` 内部内存布局与有效性约束文档化（1.92）
- C. `generic_const_exprs` 完整稳定（1.92）
- D. 增强的 const 上下文及其对生命周期的影响（1.91）

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、D**

**解析**：[Rust 1.91 稳定特性](../00_version_tracking/rust_1_91_stabilized.md) 记录借用检查器优化（编译时间 -10–20%、借用冲突检测加速）与增强的 const 上下文；[Rust 1.92 稳定特性](../00_version_tracking/rust_1_92_stabilized.md) 记录 `MaybeUninit` 布局/有效性约束文档化与联合体原始引用。C 错：`generic_const_exprs` 截至 1.97 仍为 nightly 特性（参见 Q7）。

</details>

---

### Q14. 🔴 某汽车软件团队评估工具链，提出如下论证。按权威页口径，哪条成立？

```text
方案：直接在上游最新 stable（1.97）上开发 ASIL D 控制器软件，
      理由是"版本越新缺陷越少"。
```

| 选项 | 评审意见 |
|:---|:---|
| A | 正确，最新 stable 总是安全关键项目的首选 |
| B | 不成立：ASIL D 要求工具鉴定（tool qualification），应选 Ferrocene 等经 TÜV SÜD 鉴定的工具链，并接受其认证版本滞后上游的既定约束 |
| C | 不成立，应改用 nightly 以获取最全的安全特性 |
| D | 成立，只要开启所有 clippy lint 即等价于工具鉴定 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：ISO 26262 ASIL D 对开发工具要求工具鉴定；上游 stable rustc 本身未经鉴定，而 Ferrocene 编译器经 TÜV SÜD 鉴定至 ASIL D / SIL 3 / Class C（[Ferrocene 权威页](../03_preview_features/12_ferrocene_preview.md) §1.1）。C 错：nightly 特性不能用于认证构建；D 错：lint 是开发期辅助，与监管认可的工具鉴定证据包完全不等价。汽车软件标准化路径另见 [AUTOSAR 与 Rust](../../06_ecosystem/11_domain_applications/22_autosar_and_rust.md)。

</details>

---

### Q15. 🔴【多选】关于版本跟踪体系（`00_version_tracking/`）的治理口径，下列说法正确的有？（选出所有正确项）

- A. 每版稳定特性有独立 `rust_1_XX_stabilized.md` 页，预览特性有 `rust_1_XX_preview.md` 页
- B. 版本页是中心化管理对象：Rust 新版本发布时由专人/流程统一更新
- C. 稳定页与预览页可互相复制正文，只要标题不同
- D. 版本勘误（如 RPITIT 实际稳定于 1.75 而非更晚版本）应记录在版本页中

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、D**

**解析**：版本跟踪目录按"稳定页 + 预览页"成对组织（A），AGENTS.md §7 将"版本页中心化管理"列为长期治理机制、随 Rust 新版本发布触发（B）；D 正确——[rust_1_90_stabilized](../00_version_tracking/rust_1_90_stabilized.md) 的版本勘误表专门澄清 RPITIT 稳定于 1.75。C 错：违反 canonical 规则——稳定/预览页各有定位，禁止互相复制正文，交叉内容应以链接表达。

</details>

---

> **变更记录**: 2026-07-12 新建（W3-b：L7 独立 quiz 补缺，10 题：单选 3 / 代码阅读 3 / 多选 2 / 判断 2；难度 🟢2 / 🟡5 / 🔴3）；2026-07-13 扩展至 15 题（+5 题「认证工具链与版本下沉」：Ferrocene 定位/认证延迟/1.91–1.92 谱系/ASIL D 选型/版本跟踪治理；难度 🟢3 / 🟡7 / 🔴5）。
