# 季度国际来源抽样审计报告 — 2026 Q3

**审计季度**：2026 Q3
**审计日期**：2026-08-04
**审计人**：Kimi Code CLI
**项目**：`e:/_src/rust-lang`
**当前官方稳定版本**：[Rust 1.97.0](https://blog.rust-lang.org/2026/07/09/Rust-1.97.0/)（2026-07-09），补丁 [1.97.1](https://blog.rust-lang.org/2026/07/16/Announcing-Rust-1.97.1/)（2026-07-16）
**项目声明 MSRV**：`1.97.0+ (Edition 2024)`
**审计范围**：`concept/` 中 6 个核心页，覆盖 L1–L4
**约束声明**：本次审计为只读研究；未修改任何 `concept/` 文件。

---

## 1. 抽样页清单与理由

| # | 文件路径 | 层级 | 主要国际来源 | 抽样理由 |
|---|---|---|---|---|
| 1 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L1 | [TRPL Ch4](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | 所有权是 Rust 最核心、最基础的 L1 概念，漂移风险高 |
| 2 | [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L1 | [TRPL Ch4.2](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) | 借用规则是所有权系统的直接延伸，涉及 NLL、TB 等前沿模型 |
| 3 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | L1 | [TRPL Ch10.3](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)、[Rust Reference: Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html) | 生命周期是 L1 中最接近形式化的概念，Reference 更新频繁 |
| 4 | [`concept/02_intermediate/00_traits/01_traits.md`](concept/02_intermediate/00_traits/01_traits.md) | L2 | [TRPL Ch10.2](https://doc.rust-lang.org/book/ch10-02-traits.html)、[Rust Reference: Traits](https://doc.rust-lang.org/reference/items/traits.html) | Trait 系统涉及对象安全/dyn 兼容性等近期术语变更 |
| 5 | [`concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md`](concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md) | L3 | [TRPL Ch16](https://doc.rust-lang.org/book/ch16-00-concurrency.html)、[Rustonomicon — Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html)、[Rust Reference — Special Types and Traits](https://doc.rust-lang.org/reference/special-types-and-traits.html) | 并发安全契约是类型系统与并发的交叉点，auto trait 规则近期无大变化但需对齐 Rustonomicon |
| 6 | [`concept/03_advanced/01_async/08_pin_unpin.md`](concept/03_advanced/01_async/08_pin_unpin.md) | L3/L4 | [std::pin](https://doc.rust-lang.org/std/pin/index.html)、[RFC 2349](https://rust-lang.github.io/rfcs/2349-pin.html)、[Tracking Issue #55766](https://github.com/rust-lang/rust/issues/55766) | Pin 是 async/await 与 unsafe 的交叉核心，std 文档已大幅更新 |

---

## 2. 对比维度

| 维度 | 检查问题 | 通过标准 |
|---|---|---|
| **定义漂移** | 本页定义是否与国际来源一致？ | 无矛盾；项目特定扩展需显式标注 |
| **边界完整性** | 例外、前置条件、UB 触发器是否列全？ | 不少于国际来源覆盖 |
| **版本对齐** | `Rust 版本` 标注是否与当前 stable 一致？ | ≤ 当前稳定补丁版本 |
| **锚点/链接有效性** | 外部链接是否 HTTP 200 且锚点正确？ | 无死链、无错误 RFC 引用 |
| **代码块新鲜度** | 示例是否可在声明 edition 下编译？ | 由 `check_concept_code_blocks.py` 验证 |
| **术语一致性** | 是否使用国际来源最新术语？ | 与 Reference/Nomicon 最新版一致 |

---

## 3. 逐主题对比矩阵与对称差

### 3.1 所有权（Ownership）

| 维度 | 本库 | 国际来源 | 对称差 / 结论 |
|---|---|---|---|
| **权威定义** | 三视角：类型系统（Wikipedia）、TRPL 规则集、RustBelt/COR 仿射逻辑 | TRPL：所有权是编译器检查的内存管理规则集，零运行时开销 | 本库额外提供形式化视角；TRPL 更朴素 |
| **核心规则** | 唯一所有者、作用域绑定、move、Copy 例外 | TRPL：每个值有单一所有者；值在 owner 离开作用域时 drop | 一致 |
| **形式化基础** | 线性/仿射逻辑、区域类型、分离逻辑 | TRPL 不展开 | 本库扩展 |
| **版本标注** | `1.97.0+ (Edition 2024)` | TRPL 示例已使用 `edition2024` | 一致 |
| **边界/反例** | 含 `mem::forget`、`ManuallyDrop`、循环引用泄漏等 | TRPL 第 15 章单独讲引用循环可泄漏 | 一致；本库在所有权页提前给出形式化限定 |
| **项目特定内容** | 定理“Safe Rust 无内存泄漏（模循环引用）” | TRPL 不承诺无泄漏 | 属于本库形式化模型，建议保留但加脚注说明 |

**主要对称差**：

- 本库已覆盖但国际来源未强调：RustBelt/COR、仿射逻辑、跨语言对比矩阵、`ManuallyDrop` 例外。
- 国际来源已更新但本库基本覆盖：TRPL 第 4 章现在把所有权、借用、切片、内存布局放在同一章；本库通过 canonical 分工将切片等主题分到其他页，符合项目约定。

---

### 3.2 借用（Borrowing）

| 维度 | 本库 | 国际来源 | 对称差 / 结论 |
|---|---|---|---|
| **核心规则** | AXM：共享只读 XOR 独占可变；引用有效；NLL | TRPL：相同规则；NLL（scope 到 last use） | 一致 |
| **内存模型** | Stacked Borrows → Tree Borrows、two-phase borrows | TRPL 不提 TB/SB | 本库领先 |
| **再借用（reborrow）** | 详细解释 | TRPL 通过示例隐含 | 本库更系统 |
| **`let chains`** | 作为借用章节独立小节存在 | RFC 2497 是独立语言特性，不在 TRPL 借用章 | 范围可能溢出 |
| **版本标注** | `1.97.0+` | 一致 | 一致 |

**主要对称差**：

- 本库已覆盖但国际来源未强调：Tree Borrows、two-phase borrows、内存模型演进。
- 国际来源已更新：TRPL 明确“引用的作用域到 **last use** 结束”，本库也已覆盖。
- 缺口/建议：`let chains` 与借用规则关联较弱，建议评估是否迁移到 [`concept/01_foundation/04_control_flow/03_let_chains.md`](concept/01_foundation/04_control_flow/03_let_chains.md) 或改为摘要链接。

---

### 3.3 生命周期（Lifetimes）

| 维度 | 本库 | 国际来源 | 对称差 / 结论 |
|---|---|---|---|
| **权威定义** | 编译期标注、泛型的一种、区域类型 | TRPL：确保引用有效；每个引用有 lifetime | 一致 |
| **Elision 规则** | 三条规则、trait object 默认边界、`'_` preferred | [Reference lifetime-elision](https://doc.rust-lang.org/reference/lifetime-elision.html)：三条规则、`'_` preferred、default object lifetime bounds | 基本一致；Reference 更完整 |
| **高级形式化** | HRTB、variance、NLL、Polonius、Tofte-Talpin | TRPL 仅基础；Reference 未深入 | 本库领先 |
| **1.98 预览** | `&mut` unsized coercion lifetime 缩短、trait object 默认推断收紧 | 1.98 beta / RFC 3498 / RFC 3501 | 本库有 preview，需显式标注来源 |
| **链接健康** | 存在指向 `https://doc.rust-lang.org/reference/lifetimes.html` 的引用 | 该 URL 已 404；当前规范页为 `lifetime-elision.html` | **死链，需修复** |

**主要对称差**：

- 本库已覆盖但国际来源未强调：Tofte-Talpin 区域推断、Polonius、NLL 算法演进。
- 国际来源已更新：Reference 的 default trait object lifetime bounds 规则；本库已部分覆盖，可再对齐。
- 缺口：一处死链（见 findings F5）。

---

### 3.4 Trait 系统

| 维度 | 本库 | 国际来源 | 对称差 / 结论 |
|---|---|---|---|
| **术语** | 使用 **“对象安全 (Object Safety)”** | [Rust Reference](https://doc.rust-lang.org/reference/items/traits.html) 已改为 **“dyn 兼容性 (dyn compatibility)”** | **术语滞后** |
| **dyn compat 规则** | 基于 RFC 255：无 `Self: Sized`、无泛型方法、仅特定 receiver 等 | Reference 新增：关联常量禁止、`AsyncFn*` 不兼容、Pin receiver 允许、supertrait 必须 dyn compatible | **规则滞后** |
| **supertrait item shadowing** | 已提及 RFC 3624 | RFC 3624 已合并 | 已覆盖 |
| **RPITIT/AFIT/GATs/const trait** | 有专门章节 | TRPL 基础；Reference 未深入 | 本库领先 |
| **版本标注** | `1.97.0+` | 一致 | 一致 |

**主要对称差**：

- 国际来源已更新但本库滞后：**术语从 object safety 改为 dyn compatibility**，且判定规则已扩展。
- 本库已覆盖但国际来源未强调：RPITIT/AFIT、const trait、negative impls、fundamental attribute 的形式化分析。

---

### 3.5 Send/Sync

| 维度 | 本库 | 国际来源 | 对称差 / 结论 |
|---|---|---|---|
| **契约** | `T: Send` / `T: Sync ⟺ &T: Send` | Rustonomicon 相同定义 | 一致 |
| **auto trait 推导** | 结构化推导、PhantomData 投毒 | Reference auto traits 规则；Rustonomicon 示例 | 一致 |
| **手动 unsafe impl** | `Carton<T>` 模式、`where Box<T>: Send/Sync` | Rustonomicon 中 `Carton<T>` 示例 | 本库 Q3 已对齐更新 |
| **`MutexGuard`** | 矩阵中说明 `!Send` | Rustonomicon 也强调 | 一致 |
| **版本标注** | `1.97.0+` | 一致 | 一致 |

**主要对称差**：

- 基本一致。本库已吸收 Rustonomicon `Carton<T>` 模式，建议继续保留并强化与 Rustonomicon 锚点的链接。

---

### 3.6 Pin/Unpin

| 维度 | 本库 | 国际来源 | 对称差 / 结论 |
|---|---|---|---|
| **核心契约** | Pin 是“承诺不移动”；Unpin 是默认安全网 | [std::pin](https://doc.rust-lang.org/std/pin/index.html) 一致 | 一致 |
| **API** | `Pin<&mut T>`、`Box::pin`、`pin!` | std::pin 文档：`pin!`、`Box::into_pin`、投影规则 | 一致 |
| **结构 pinning** | 有章节 | std::pin 文档详细 | 基本一致 |
| **Drop guarantee** | 有提及 | std::pin 文档详细 | 可补充 |
| **RFC 引用** | 正文中出现 **“RFC 2592 — Pin”** | Pin 的 RFC 是 **2349**；2592 是 futures | **引用错误** |
| **链接健康** | `Rustonomicon — Pin` 链接 `https://doc.rust-lang.org/nomicon/pin.html` | 该 URL 返回 **404** | **死链** |
| **版本标注** | `1.97.1+` | 一致 | 一致 |

**主要对称差**：

- 本库覆盖良好，但存在 **RFC 引用错误** 和 **死链**。
- 国际来源 std::pin 文档包含更丰富的边界示例（intrusive doubly-linked list、`Deref`/`DerefMut` 不移动要求），本库可选补充。

---

## 4. 审计发现汇总

| # | 文件路径 | 维度 | 发现 | 严重度 | 行动项 |
|---:|---|---|---|:---:|---|
| F1 | [`concept/02_intermediate/00_traits/01_traits.md`](concept/02_intermediate/00_traits/01_traits.md) | 术语漂移 | 仍使用 **“对象安全 / Object Safety”**；Rust Reference 已改为 **“dyn 兼容性 / dyn compatibility”** | P1 | 全页更新术语，保留“曾用名 object safety”注释，链接指向 Reference `#dyn-compatibility` |
| F2 | [`concept/02_intermediate/00_traits/01_traits.md`](concept/02_intermediate/00_traits/01_traits.md) | 边界完整性 | 未覆盖 Reference 中的新 dyn compatibility 规则：关联常量禁止、`AsyncFn*` 不兼容、Pin receiver 允许、supertrait 必须 dyn compatible | P1 | 补充 dyn compatibility 判定矩阵，引用 [Reference Traits](https://doc.rust-lang.org/reference/items/traits.html) |
| F3 | [`concept/03_advanced/01_async/08_pin_unpin.md`](concept/03_advanced/01_async/08_pin_unpin.md) | 引用错误 | 正文出现 **“RFC 2592 — Pin”**；Pin 的 RFC 是 **2349** | P1 | 将 2592 改为 2349；如需引用 futures RFC 2592 应单独标注 |
| F4 | [`concept/03_advanced/01_async/08_pin_unpin.md`](concept/03_advanced/01_async/08_pin_unpin.md) | 死链 | `https://doc.rust-lang.org/nomicon/pin.html` 返回 404 | P1 | 替换为 [std::pin](https://doc.rust-lang.org/std/pin/index.html) 或删除该来源 |
| F5 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | 死链 | 引用 `https://doc.rust-lang.org/reference/lifetimes.html` 返回 404 | P1 | 替换为 `https://doc.rust-lang.org/reference/lifetime-elision.html` 或对应 Reference 锚点 |
| F6 | [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 范围/去重 | `let chains`（RFC 2497）作为借用章节的独立小节，与该页核心主题关联较弱 | P2 | 评估迁移到 `concept/01_foundation/04_control_flow/03_let_chains.md` 或改为摘要/链接 |
| F7 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 表述强度 | “Safe Rust 无内存泄漏（模循环引用）”是项目形式化定理；TRPL 明确引用循环可导致泄漏 | P2 | 保留定理，但增加脚注说明这是基于本库形式化模型的结论，非 TRPL 原话 |
| F8 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | 来源标注 | Rust 1.98.0 兼容性注意（lifetime capture / trait object default）应显式引用 RFC 3498、RFC 3501 或 1.98 beta release notes | P2 | 在兼容性注意中添加 RFC/发布说明来源链接 |
| F9 | [`concept/03_advanced/01_async/08_pin_unpin.md`](concept/03_advanced/01_async/08_pin_unpin.md) | 示例/边界 | 缺少 std::pin 文档中 intrusive doubly-linked list 示例和 `Deref`/`DerefMut` 不移动要求 | P2 | 可选补充，增强边界教学 |
| F10 | [`concept/02_intermediate/00_traits/01_traits.md`](concept/02_intermediate/00_traits/01_traits.md) | 链接健康 | Reference object-safety 锚点可能已改为 `#dyn-compatibility` | P2 | 运行 `kb_auditor --link-check` 确认并更新 |

---

## 5. 后续修复/补充建议（按优先级）

### P1 — 必须在下次合并前修复

1. **更新 Trait 系统术语**：将 [`concept/02_intermediate/00_traits/01_traits.md`](concept/02_intermediate/00_traits/01_traits.md) 中的“对象安全 / Object Safety”统一改为“dyn 兼容性 / dyn compatibility”，并在首次出现时注明旧称。
2. **补充 dyn compatibility 判定规则**：新增矩阵或列表，覆盖关联常量、`AsyncFn*`、Pin receiver、supertrait dyn compatibility 等 Reference 最新规则。
3. **修正 Pin RFC 引用**：将 [`08_pin_unpin.md`](concept/03_advanced/01_async/08_pin_unpin.md) 中的 `RFC 2592 — Pin` 改为 `RFC 2349`。
4. **修复死链**：
   - Pin 页 Rustonomicon 链接 → 替换为 [std::pin](https://doc.rust-lang.org/std/pin/index.html)。
   - Lifetimes 页 `reference/lifetimes.html` → 替换为 [Reference lifetime-elision](https://doc.rust-lang.org/reference/lifetime-elision.html)。

### P2 — 建议在本季度内补充

1. **所有权页定理脚注**：为“Safe Rust 无内存泄漏”增加形式化来源与 TRPL 差异说明。
2. **借用页 `let chains` 范围评估**：按 AGENTS.md canonical 规则，判断该节是否应独立成页或改为链接。
3. **生命周期页 1.98 来源链接**：显式关联 [RFC 3498](https://rust-lang.github.io/rfcs/3498-lifetime-capture-rules-2024.html)（lifetime capture rules 2024）与 [RFC 3501](https://rust-lang.github.io/rfcs/3501-edition-2024.html)（edition 2024）。
4. **Pin 页边界示例增强**：可选引入 std::pin 文档中的 intrusive list 与 `Deref` 不移动要求。
5. **全量链接巡检**：运行 `python scripts/kb_auditor.py --link-check`，确认所有外部锚点 200。

---

## 6. 签核前建议运行的命令

```bash
python scripts/kb_auditor.py --link-check
python scripts/check_canonical_uniqueness.py --strict
python scripts/check_concept_authority_coverage.py --strict --include-crates
python scripts/check_cross_domain_coverage.py --strict
python scripts/check_concept_code_blocks.py --strict
```

---

## 7. 总体结论

- **无重大语义漂移**：6 个抽样页的核心定义、规则与 TRPL / Reference / Rustonomicon / std 文档保持一致。
- **主要问题集中在术语与链接**：
  - Rust Reference 已将 **object safety** 改为 **dyn compatibility**，本库 Trait 页术语滞后。
  - 存在 1 处 RFC 引用错误（Pin 页）和 2 处死链（Pin 页 Rustonomicon、Lifetimes 页 Reference）。
- **形式化与前沿内容领先国际基础文档**：RustBelt、Tree Borrows、Tofte-Talpin、Polonius、RPITIT/AFIT 等内容在本库中有系统覆盖，而 TRPL/Reference 仅作基础介绍，这符合本库 L4 定位。

**总体审计结论**：□ 无漂移 / ☑ 轻微漂移，已列出修复清单 / □ 重大漂移需后续 sprint
