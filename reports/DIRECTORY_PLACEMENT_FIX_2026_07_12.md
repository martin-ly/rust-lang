# 目录归档错位与编号冲突修正报告

> **日期**: 2026-07-12
> **范围**: `concept/` 目录结构修正（L2/L3/L6/L7），全仓引用链接更新
> **依据**: AGENTS.md §2 Canonical 规则、§4 命名规范
> **git**: 未做任何 commit/stage（按任务要求）

---

## 一、逐文件裁定与理由

### 1. 版本治理文件迁出 `02_intermediate/00_traits/`

| 文件 | 裁定 | 理由 |
|---|---|---|
| `32_editions.md` | **迁移** → `concept/07_future/00_version_tracking/32_editions.md` | Rust Editions 是版本/工具链治理主题，与 trait 无关；目标目录已承载 `05_rust_version_tracking.md`、各版本 stabilized/preview 页，语义一致。目标目录 32 号空闲，沿用原编号减少 churn。 |
| `33_rust_release_process.md` | **迁移** → `concept/07_future/00_version_tracking/33_rust_release_process.md` | 发布流程（release train、channel、SemVer）同属版本治理；33 号空闲，沿用原编号。 |

SUMMARY.md 中两条目从 L2 段移至 L7 段（`05_rust_version_tracking.md` 之后）。

### 2. `03_advanced/02_unsafe/` 非 unsafe 主题裁定

| 文件 | 裁定 | 理由 |
|---|---|---|
| `29_memory_model.md` | **保留** + 文件头加"目录归属说明" | 内存模型（抽象字节、provenance、未初始化内存）是 unsafe 代码 UB 判定的语义基础（Rust Reference — Memory Model 与 Behavior Considered Undefined 直接衔接），与 unsafe 语义强相关，迁移反而割裂前置/后置链。 |
| `08_nll_and_polonius.md` | **保留** + 文件头加"目录归属说明" | NLL/Polonius 的数据流分析精度直接决定 unsafe 代码中别名与生命周期推断的可靠性边界（RustBelt 形式化链一环），且其后置概念链指向本目录 `03_unsafe.md` 与 L4 RustBelt。 |
| `31_panic.md` | **迁移** → `concept/02_intermediate/03_error_handling/31_panic.md` | panic 属错误处理体系。未迁入 `01_foundation/08_error_handling/` 是因该目录已有初学者级 `13_panic_and_abort.md`（综述级），而 `31_panic.md` 为专家级规范语义页（S — Specification），与 `02_intermediate/03_error_handling/` 的 `16_error_handling_deep_dive.md` 层级匹配，构成 L1 入门 → L2 深化的分层互补，不违反 canonical（两页受众/深度不同，且互相前置引用）。 |
| `30_rust_runtime.md` | **迁移** → `concept/03_advanced/06_low_level_patterns/30_rust_runtime.md` | 运行时主题（`#[global_allocator]`、`#[windows_subsystem]`、启动流程）属低层模式而非 unsafe 语义；`06_low_level_patterns/` 已承载 `14_custom_allocators.md`（本页前置依赖），同层迁移、深度不变、链接成本最低。未选 06_ecosystem 是因该页为语言规范层（Reference runtime 章）而非生态主题。 |

### 3. 编号冲突

| 冲突 | 裁定 | 理由 |
|---|---|---|
| `03_advanced/02_process_ipc` vs `02_unsafe` | **重编号** → `03_advanced/08_process_ipc`（目录改名） | `03_advanced` 下 00–07 已占用，08 为最小空闲序号；进程/IPC 是独立系统编程主题，保留独立目录。 |
| `06_ecosystem/09_networking` vs `09_testing_and_quality`，且与 `04_web_and_networking` 领域重叠 | **重编号** → `06_ecosystem/12_networking` + 分工说明 | 内容比对后裁定**互补而非重复**：`04_web_and_networking/` 为 Web/云原生应用架构层（Web 框架、HTTP 客户端、WebSocket、云原生、分布式系统），`12_networking/` 为网络编程基础与协议实现层（socket 基础、协议快速入门、gRPC/MQTT/QUIC、网络安全、自定义协议、形式化协议理论），无需按 canonical 合并为 stub。12 为最小空闲序号。分工说明写入 `06_ecosystem/README.md` 与新建的 `12_networking/README.md`。 |

### 4. C++ 对比文件（L2 vs L5 职责）

**裁定：保留在 L2 + 分工声明 + L5 登记反链**（低成本且语义正确方案）。

- 5 个文件（`25_rtti_and_dynamic_typing.md`、`26_c_preprocessor_vs_rust_macros.md`、`27_exception_safety_rust_cpp.md`、`28_construction_and_initialization.md`、`29_friend_vs_module_privacy.md`）各自嵌入对应 L2 概念目录（类型/宏/错误处理/构造/可见性），服务于就近对照学习；迁往 L5 需改 5 文件路径 + 全部引用 + 破坏 L2 学习路径。
- 每文件头部已加"层级分工声明"（指明属跨语言对比专题，L5 索引反链）。
- `concept/05_comparative/README.md` 新增"七、L2 跨语言对比专题登记"表，登记 5 条反链及对应 L5 入口。

### 5. `07_future` 稀疏目录

| 目录 | 裁定 | 理由 |
|---|---|---|
| `02_stabilized_features/`（仅 `borrow_sanitizer.md`） | **合并** → 文件迁入 `03_preview_features/borrow_sanitizer.md`，删除空目录 | BorrowSanitizer 为 nightly 实验特性（`#[experimental]`，跟踪 nightly 1.98.0），置于"已稳定特性"目录本身是归档错误；`03_preview_features/` 已有其预研页 `20_borrowsanitizer_preview.md`（历史参考，已指向深度页），迁入后同目录互链。 |
| `05_roadmaps/`（仅 `24_roadmap.md`） | **合并** → 文件迁入 `01_edition_roadmap/24_roadmap.md`，删除空目录 | Rust 2027 Edition 路线图与 `01_edition_roadmap/` 的 edition 指南（19/23/44）同主题；24 号空闲，沿用原编号。 |

`scripts/concept_config.py` 的目录清单已同步（删除 07_future 两目录、新增 `08_process_ipc`、`12_networking`）。

---

## 二、移动清单（共 8 项移动 + 2 项目录删除）

| # | 源路径 | 目标路径 |
|---|---|---|
| 1 | `concept/02_intermediate/00_traits/32_editions.md` | `concept/07_future/00_version_tracking/32_editions.md` |
| 2 | `concept/02_intermediate/00_traits/33_rust_release_process.md` | `concept/07_future/00_version_tracking/33_rust_release_process.md` |
| 3 | `concept/03_advanced/02_unsafe/31_panic.md` | `concept/02_intermediate/03_error_handling/31_panic.md` |
| 4 | `concept/03_advanced/02_unsafe/30_rust_runtime.md` | `concept/03_advanced/06_low_level_patterns/30_rust_runtime.md` |
| 5 | `concept/03_advanced/02_process_ipc/`（10 文件） | `concept/03_advanced/08_process_ipc/` |
| 6 | `concept/06_ecosystem/09_networking/`（6 文件） | `concept/06_ecosystem/12_networking/` |
| 7 | `concept/07_future/02_stabilized_features/borrow_sanitizer.md` | `concept/07_future/03_preview_features/borrow_sanitizer.md` |
| 8 | `concept/07_future/05_roadmaps/24_roadmap.md` | `concept/07_future/01_edition_roadmap/24_roadmap.md` |

删除空目录：`07_future/02_stabilized_features/`、`07_future/05_roadmaps/`。
新增：`concept/06_ecosystem/12_networking/README.md`（目录分工 + 文件索引）。

## 三、链接更新计数

| 类别 | 文件数 | 说明 |
|---|---|---|
| 全仓 token 替换（8 组路径片段） | 135 | 覆盖 concept/docs/knowledge/content/crates/scripts 的 md/py/json/yaml/html（`02_process_ipc`→`08_process_ipc`、`09_networking`→`12_networking` 等） |
| 移动文件内部相对链接修正 | 7 | 同目录/兄弟目录链接按新深度重写（`../04_ffi/...`、同目录 `03_unsafe.md` 等） |
| 残留引用修正（kg 数据 + `32_memory_allocation_and_lifetime.md`） | 6 | `kg_data_v3.json(.bak)`、`kg_index.json`、`concept_kb.json`（含 Windows 反斜杠路径）、`tools/kg_browser/index.html` |
| crates/knowledge 深度错误修复 | 26 文件 / 44 链接 | 移动暴露的**既有**相对深度错误（如 `../../concept/` 应为 `../../../concept/`），按仓库根重算修复 |
| `02_unsafe/` 内同目录链接修复 | 2 | `29_memory_model.md`、`35_unsafe_reference.md` 指向已迁出文件的裸文件名链接 |
| SUMMARY.md | 1 | 8 处路径更新 + 2 条目从 L2 段迁至 L7 段 |
| 图谱/地图元数据 | 3 | `01_concept_definition_atlas.md`、`02_attribute_relationship_atlas.md`（含层级标签 L2→L7、L3→L2 修正）、`07_intra_layer_mapping_atlas.md`（含关系描述修正） |
| 脚本配置 | 3 | `concept_config.py`（目录清单）、`generate_kg_index.py`、`topic_authority_aligner.py` |
| 头部说明/分工声明 | 7 + 3 README | 2 个 unsafe 归属说明、5 个 C++ 对比分工声明；`05_comparative/README.md`、`06_ecosystem/README.md`、`12_networking/README.md` |

**未修改**（有意保留历史记录）：`CHANGELOG.md`（4 处旧路径，历史变更记录）、`reports/`、`.kimi/`、`archive/`（只读历史归档）、`tmp/`、`book/`（构建产物）、`__pycache__/`、`*.pkl`（二进制缓存，再生成时自动刷新）。

## 四、验证结果（全部通过）

| 验证项 | 结果 |
|---|---|
| 旧路径残留 grep（8 组 token，排除历史目录） | ✅ 仅剩 2 处有意保留的"重编号说明"文本 |
| `python scripts/check_canonical_uniqueness.py --strict` | ✅ exit=0（213 条 WARN 为既有跨层同主题提示，非阻断） |
| `python scripts/check_template_cliches.py --strict` | ✅ exit=0 |
| mdbook SUMMARY 悬空条目 | ✅ 0（全部链接目标存在） |
| 移动文件内部相对链接 | ✅ 0 断裂 |
| 全仓指向移动路径的链接 | ✅ 0 断裂（除下述既有问题） |
| `scripts/concept_config.py` 可导入 | ✅ |

### 既有问题（非本次引入，已记录未改）

1. `crates/c07_process/docs/tier_03_references/04_synchronization_primitives_reference.md` → `08_process_ipc/06_synchronization_primitives.md`（2 处）：目标文件在重命名前的 `02_process_ipc/` 中即不存在，属既有悬空引用，需内容侧补页或改链。
2. `crates/c10_networks/docs/tier_03_references/02_network_library_comparison.md`、`crates/c12_wasm/docs/tier_04_advanced/06_container_technology_integration.md` 中 `../06_ecosystem/04_web_and_networking/...`（各 1 处）：指向未移动目录的既有深度错误，与本次移动无关。
3. `docs/` 全量 link check（`scripts/check_links.py`）基线 7029 条损坏链接为既有状态，本次未引入新增（移动相关链接已逐条验证）。
