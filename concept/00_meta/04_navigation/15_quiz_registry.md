# 测验体系注册表（Quiz Registry）

**EN**: Quiz Registry — Human-readable index of all assessment assets in the knowledge base.

> **Summary**: Unified index of the 22 standalone quizzes, per-page embedded quizzes, exercises test suites, Brown inventories, and the rustlings mapping, with question counts, type composition, difficulty distribution, and backlink status.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L0（元信息 / 导航）
> **权威来源**: 本文件为 `concept/` 权威页。
>
> **机器可读副本**: [`../quiz_registry.yaml`](../quiz_registry.yaml)（`scripts/check_quiz_system.py` 校验一致性）
> **题型规范**: quiz 保持 `.md` 格式，按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`） 组织
> （代码阅读题 +【单选】【多选】【判断】，`<details>` 折叠答案），不引入 TOML 插件。
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **回链状态**: ✅ 对应 concept 权威页已回链 quiz（22/22，W3-b 批量补链完成）
> **来源**: [mdBook 官方文档](https://rust-lang.github.io/mdBook/)（P0 官方：本知识库测验体系的托管框架，curl 200 实测 2026-07-13）

---

## 一、独立 quiz（22 个 / 324 题）

> 每个 quiz 保留原有代码阅读题（特色），2026-07-12 起按四级题型规范增补单选/多选/判断题并逐题标注难度。
> 「元测验」列为文件末尾关于测验本身使用方式的嵌入式理解题，不计入题数。
> W3-b（2026-07-12）新增 L0/L7 各 1 个、L6 子领域 3 个独立 quiz（各 10 题），并批量完成 concept→quiz 回链；
> 2026-07-13 上述 5 个 quiz 各扩展至 15 题（10+5），并新增 L6 领域应用 quiz（15 题）。

### L0 元层（`concept/00_meta/05_quizzes/`）

| Quiz | 主题 | 题数 | 题型构成 | 难度分布（🟢/🟡/🔴） | 回链 |
|:---|:---|:---:|:---|:---:|:---:|
| [01_quiz_meta_framework](../05_quizzes/01_quiz_meta_framework.md) | 元层框架与知识体系架构 | 15 | 代码阅读/单选/多选/判断 | 3/7/5 | ✅ |

### L1 基础层（`concept/01_foundation/11_quizzes/`）

| Quiz | 主题 | 题数 | 题型构成 | 难度分布（🟢/🟡/🔴） | 回链 |
|:---|:---|:---:|:---|:---:|:---:|
| [24_quiz_type_system](../../01_foundation/11_quizzes/01_quiz_type_system.md) | 类型系统 | 15+3 | 代码阅读/单选/多选/判断 | 6/9/0 | ✅ |
| [25_quiz_error_handling](../../01_foundation/11_quizzes/02_quiz_error_handling.md) | 错误处理 | 15+3 | 代码阅读/单选/多选/判断 | 3/11/1 | ✅ |
| [26_quiz_modules_testing](../../01_foundation/11_quizzes/03_quiz_modules_testing.md) | 模块系统与测试 | 15+3 | 代码阅读/单选/多选/判断 | 4/10/1 | ✅ |
| [27_quiz_closures_iterators](../../01_foundation/11_quizzes/04_quiz_closures_iterators.md) | 闭包与迭代器 | 15+3 | 代码阅读/单选/多选/判断 | 3/11/1 | ✅ |
| [29_quiz_pl_foundations](../../01_foundation/11_quizzes/05_quiz_pl_foundations.md) | 通用 PL 基座 | 11 | 单选/多选/判断 | 2/6/3 | ✅ |
| [33_quiz_ownership_borrowing](../../01_foundation/11_quizzes/06_quiz_ownership_borrowing.md) | 所有权、借用与生命周期 | 15+3 | 代码阅读/单选/多选/判断 | 4/9/2 | ✅ |

### L2 进阶层（`concept/02_intermediate/`）

| Quiz | 主题 | 题数 | 题型构成 | 难度分布（🟢/🟡/🔴） | 回链 |
|:---|:---|:---:|:---|:---:|:---:|
| [04_quiz_traits_and_generics](../../02_intermediate/01_generics/04_quiz_traits_and_generics.md) | Trait 与泛型 | 15+3 | 代码阅读/单选/多选/判断 | 5/7/3 | ✅ |
| [05_quiz_memory_management](../../02_intermediate/02_memory_management/05_quiz_memory_management.md) | 内存管理与智能指针 | 15+3 | 代码阅读/单选/多选/判断 | 3/9/3 | ✅ |
| [30_quiz_cpp_rust_foundations](../../02_intermediate/08_quizzes/30_quiz_cpp_rust_foundations.md) | C/C++ → Rust 基础对比 | 13 | 单选/多选/判断 | 3/7/3 | ✅ |

### L3 高级层（`concept/03_advanced/`）

| Quiz | 主题 | 题数 | 题型构成 | 难度分布（🟢/🟡/🔴） | 回链 |
|:---|:---|:---:|:---|:---:|:---:|
| [08_quiz_concurrency_async](../../03_advanced/00_concurrency/09_quiz_concurrency_async.md) | 并发与异步 | 15+3 | 代码阅读/单选/多选/判断 | 2/8/5 | ✅ |
| [10_quiz_semantic_models](../../03_advanced/00_concurrency/10_quiz_semantic_models.md) | 语义模型与跨语言对比 | 15+3 | 代码阅读/单选/多选/判断 | 3/10/2 | ✅ |
| [05_quiz_unsafe](../../03_advanced/02_unsafe/05_quiz_unsafe.md) | Unsafe Rust | 15+3 | 代码阅读/单选/多选/判断 | 3/4/8 | ✅ |
| [10_quiz_macros](../../03_advanced/03_proc_macros/10_quiz_macros.md) | 宏系统 | 15+3 | 代码阅读/单选/多选/判断 | 4/7/4 | ✅ |

### L4–L6（形式化 / 对比 / 生态）

| Quiz | 主题 | 题数 | 题型构成 | 难度分布（🟢/🟡/🔴） | 回链 |
|:---|:---|:---:|:---|:---:|:---:|
| [06_quiz_formal_methods](../../04_formal/04_model_checking/06_quiz_formal_methods.md) | 形式化方法（L4） | 15+3 | 代码阅读/单选/多选/判断 | 1/5/9 | ✅ |
| [02_quiz_rust_vs_systems](../../05_comparative/03_domain_comparisons/02_quiz_rust_vs_systems.md) | Rust vs 系统编程语言（L5） | 15+3 | 代码阅读/单选/多选/判断 | 2/9/4 | ✅ |
| [06_quiz_toolchain](../../06_ecosystem/00_toolchain/06_quiz_toolchain.md) | Rust 工具链（L6） | 15+3 | 代码阅读/单选/多选/判断 | 5/10/0 | ✅ |

### L6 生态子领域（`concept/06_ecosystem/13_quizzes/`，W3-b 新增）

| Quiz | 主题 | 题数 | 题型构成 | 难度分布（🟢/🟡/🔴） | 回链 |
|:---|:---|:---:|:---|:---:|:---:|
| [01_quiz_networking_async_ecosystem](../../06_ecosystem/13_quizzes/01_quiz_networking_async_ecosystem.md) | 网络与异步生态 | 15 | 代码阅读/单选/多选/判断 | 3/7/5 | ✅ |
| [02_quiz_database_storage](../../06_ecosystem/13_quizzes/02_quiz_database_storage.md) | 数据库与存储生态 | 15 | 代码阅读/单选/多选/判断 | 3/7/5 | ✅ |
| [03_quiz_security_testing](../../06_ecosystem/13_quizzes/03_quiz_security_testing.md) | 安全与测试生态 | 15 | 代码阅读/单选/多选/判断 | 3/7/5 | ✅ |
| [04_quiz_domain_applications](../../06_ecosystem/13_quizzes/04_quiz_domain_applications.md) | 领域应用生态 | 15 | 代码阅读/单选/多选/判断 | 3/7/5 | ✅ |

### L7 前沿层（`concept/07_future/05_quizzes/`，W3-b 新增）

| Quiz | 主题 | 题数 | 题型构成 | 难度分布（🟢/🟡/🔴） | 回链 |
|:---|:---|:---:|:---|:---:|:---:|
| [01_quiz_version_and_preview](../../07_future/05_quizzes/01_quiz_version_and_preview.md) | 版本演进、Edition 机制与前沿特性 | 15 | 代码阅读/单选/多选/判断 | 3/7/5 | ✅ |

**合计**：324 题（🟢 71 / 🟡 174 / 🔴 79），难度标注率 100%，题型多样性每 quiz ≥3 种（20 个为 4 种）。
**W3-b 缺口已闭合**：L0/L7 独立 quiz 已建并扩至 15 题；L6 生态子领域 quiz 已补 4 个（网络/数据库/安全测试/领域应用）；
concept→quiz 回链 22/22 完成（`scripts/add_quiz_backlinks.py` 幂等批量补链，`scripts/refresh_quiz_registry.py` 从文件实测重算统计）；
2026-07-16 新增 L3 语义模型与跨语言对比 quiz（15 题，🟢3/🟡10/🔴2）。

---

## 二、嵌入式测验（concept/ 页内）

概念页末尾的 `### 测验 N` + `<details>` 答题块，按页聚合明细见 `quiz_registry.yaml` 的 `embedded_quizzes.items`。

| 层级 | 页数 | 答题块 |
|:---|---:|---:|
| 00_meta | 38 | 112 |
| 01_foundation | 39 | 159 |
| 02_intermediate | 30 | 132 |
| 03_advanced | 29 | 116 |
| 04_formal | 27 | 122 |
| 05_comparative | 18 | 88 |
| 06_ecosystem | 72 | 345 |
| 07_future | 44 | 216 |
| README.md / sources | 4 | 12 |
| **合计** | **301** | **1299** |

> W3-b（2026-07-12）新增 15 页嵌入式测验（L1×6：patterns/statements/functions/structs/enums/impls；
> L2×5：dispatch/derive/GAT/const_generics/panic；L3×4：send_sync/future_executor/cancellation/memory_model），
> 每页 3 题（🟢🟡🔴 各 1），共 +45 答题块。
> 2026-07-13 再补 3 页（L1：06_keywords；L2：03_type_level_programming；L3：08_syn_quote_reference），共 +9 答题块；
> TOP-20 清单中 04_unsafe_rust_patterns 为重定向 stub，按 canonical 规则不加测验，其权威页 01_unsafe.md 已有 4 块嵌入式测验。

---

## 三、exercises 分层测试套件

`exercises/tests/` 下 12 个含 `#[test]` 的测试文件，合计 **139 个测试函数**（明细见 yaml `exercises_tests.items`）：

| 分层 | 代表文件 | 内容 |
|:---|:---|:---|
| L1 基础 | `l1_foundation.rs` | 所有权/借用/类型系统/错误处理等基础断言 |
| L2 进阶 | `l2_intermediate.rs` | 泛型/trait/智能指针/迭代器 |
| L3 高级 | `l3_*.rs`（core / advanced_systems / async_concurrency / unsafe_rust / ecosystem_alignment） | 并发、异步、unsafe、生态对齐 |
| 版本对齐 | `l3_rust_196/197/198_alignment.rs` | 版本特性对齐测试 |
| quiz 配套 | `quizzes/` 子目录 | 与独立 quiz 联动的可编译验证 |

## 四、Brown inventories 与 rustlings 映射

| 资产 | 路径 | 规模 |
|:---|:---|:---:|
| Brown 大学所有权 inventories 配套练习 | `exercises/src/ownership_borrowing/brown_inventories/` | 8 个 inventory 练习（inventory_01–08.rs） |
| rustlings 习题 ↔ 项目 C01–C17 模块映射 | `exercises/rustlings_mapping.md` | 17 个模块映射 |
| Brown 所有权 inventories 概念页 | [06_ownership_inventories_brown_book](../../01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md) | — |

---

## 五、质量校验

```bash
python scripts/check_quiz_system.py           # 观察模式（exit 0）
python scripts/check_quiz_system.py --strict  # 注册表一致性/题型多样性/难度标注失败即阻断
```

校验项：① yaml 注册表与实际文件一致性（题数/题型/难度分布/嵌入式统计）；② 独立 quiz 题型多样性 ≥3 种；
③ 难度标注率（目标 100%）；④ quiz→concept 与 concept→quiz 双向链接率（回链 22/22）。

> 本页统计由 `scripts/check_quiz_system.py` 机器复核；最后核对：2026-07-16（`--strict` 0 失败；回链 22/22；324/324 题难度标注 100%）。
