# WS-A 惯用法语义对齐报告

**EN**: WS-A Idioms Semantic Authority Alignment Report
**Summary**: Systematic alignment of Rust idioms in `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md` against the Rust API Guidelines and Rust Design Patterns Idioms, closing gaps in error handling, collections, macros, and FFI/C-API.

> **Rust 版本**: 1.97.1+ (Edition 2024)
> **Bloom 层级**: L6
> **权威来源**: 本报告为 P7「语义完备化与国际权威对齐冲刺」WS-A 的交付物。
> **治理依据**: AGENTS.md §2 Canonical、§3 去重、§5 质量门、§6 红线

---

## 一、国际化权威来源清单

| 来源 | 角色 | 本地对应位置 |
|---|---|---|
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | 官方 API 设计规范 | `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` |
| [Rust Design Patterns — Idioms](https://rust-unofficial.github.io/patterns/idioms/) | 社区惯用法模式 | `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md` |
| [The Rust Programming Language — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html) | 官方错误处理语义 | `concept/01_foundation/08_error_handling/`、L2 `05_error_idioms.md` |
| [Rust std collections](https://doc.rust-lang.org/std/collections/index.html) | 集合类型官方文档 | `concept/01_foundation/05_collections/` |
| [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html) | 宏系统规范 | `concept/01_foundation/09_macros_basics/`、L3 `03_proc_macros/` |
| [Rust API Guidelines — FFI](https://rust-lang.github.io/api-guidelines/ffi.html) | FFI 接口规范 | `concept/03_advanced/04_ffi/` |
| [The Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/) | FFI 实践范例 | `concept/03_advanced/04_ffi/` |

---

## 二、语义对齐矩阵

| 维度 | 本地原状态 | 权威来源状态 | 对称差 | 修复动作 |
|---|---|---|---|---|
| **错误处理惯用法** | 已有 7.5 节「错误处理全谱」，侧重 `ok_or`/`map_err`/`thiserror`/`anyhow` 组合子分层 | API Guidelines C-ERROR 要求库错误实现 `std::error::Error`；Design Patterns 强调 `Result` 类型设计与 `?` 传播；Rust 1.97.1+ 推荐 `Error::source()` 因果链 | 缺少面向 API 设计的错误类型契约、自定义 `Error` + `source()` 示例、`Result<T>` 别名模式 | 新增 7.9 节，覆盖 `Error`/`Display`/`Debug` 分离、因果链、`From`+`?`、`Result` 别名、库 vs 应用选型矩阵与决策树 |
| **集合惯用法** | 已有 7.8 节「算法惯用法」和 L1 集合页，但缺少 `entry`/`retain`/`with_capacity` 等高频集合微惯用法速查 | API Guidelines C-COLLECTOR 强调 `FromIterator`/`Extend`；std 文档推荐 `entry`、`retain`、`windows`、`chunks`、按语义选容器 | 缺少集合微惯用法系统性整理、容器选型矩阵、容量预分配反例 | 新增 7.10 节，覆盖 `entry.or_insert`、`retain`、`with_capacity`、`windows/chunks`、HashMap/BTreeMap/VecDeque/BinaryHeap 选型矩阵与决策树 |
| **宏惯用法** | 已有 3.5 节 `matches!` 和 L1/L3 宏专题页，但惯用法谱系中缺少宏使用/编写微惯用法 | Design Patterns / The Little Book of Rust Macros 推荐 `tt` 片段、显式分隔符、卫生性、`compile_error!`、过程宏薄壳 | 缺少 `macro_rules!` 片段选择建议、卫生性示例、过程宏边界决策树 | 新增 7.11 节，覆盖 `tt` 片段、重复模式分隔符、卫生性、`compile_error!`、syn/quote 薄壳、宏选型决策树 |
| **FFI/C-API 惯用法** | 已有 9.6 节「FFI 惯用法」介绍 `extern "C"`、`#[repr(C)]`、安全封装 | API Guidelines FFI 章强调 opaque 类型、`Box::into_raw`/配对 `free`、panic 边界、字符串 `CString`/`CStr`、Edition 2024 `unsafe(no_mangle)` | 缺少 API Guidelines FFI 视角的 opaque 类型所有权转移、panic 边界、`CString` 转换、Rust→C / C→Rust 语义矩阵 | 新增 9.7 节，覆盖 opaque 类型、`Box::into_raw`/`from_raw`、配对析构、`catch_unwind`、字符串转换、方向矩阵与决策树 |
| **思维表征** | 原页已有主 mindmap、L2/L3/L4 子 mindmap、CARE 总表、效率矩阵、决策树 | API Guidelines / Design Patterns 以「规则-示例-反例」组织；P7 要求每个新增主题必须具备思维导图、矩阵、反例、决策树 | 新增四节需补齐各自的 mindmap、矩阵、反例、flowchart，并同步 CARE 总表 | 为每个新增节添加独立 mindmap、选型矩阵、决策树 flowchart、正/反例；向 CARE 总表追加 4 行；更新目录导航 |
| **代码可编译性** | 原页多数代码块已标注 `rust`/`ignore`/`compile_fail`/`should_panic` | P7 要求新增 rust 块尽量给出 `fn main()` 或可编译上下文；`compile_fail` 必须真实失败 | 新增代码块需经过 `check_concept_code_blocks.py` 验证 | 所有新增 `rust` 块均给出完整 `fn main()`；`compile_fail` 使用 `#![deny(improper_ctypes_definitions)]` 确保真实失败；`should_panic` 覆盖库 API panic 反例 |

---

## 三、新增/修改文件

| 文件 | 动作 | 说明 |
|---|---|---|
| `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md` | 增强 | 新增 7.9、7.10、7.11、9.7 四节；更新目录、CARE 总表、变更日志；所有新增内容含 mindmap、矩阵、决策树、反例、可编译示例 |
| `reports/IDIOMS_CODE_BLOCKS_CHECK_2026_08_04.md` | 新建（校验产物） | `check_concept_code_blocks.py` 运行报告 |
| `tmp/idioms_cb_2026_08_04.json` | 新建（校验产物） | 代码块检查 JSON 输出 |
| `reports/CONTENT_OVERLAP_DETECTION_2026_08_04.md` | 更新（校验产物） | 内容重叠检测输出 |
| `reports/IDIOMS_AUTHORITY_ALIGNMENT_2026_08.md` | 新建 | 本对齐报告 |

---

## 四、质量门验证

### 4.1 去重检查

```bash
python scripts/detect_content_overlap.py
```

- 扫描文件数：1222
- 发现潜在重复：2 对（均为 `concept/04_formal/15_language_specification/01_rust_reference_and_normative_gap.md` 与 `docs/12_research_notes/01_alignment_matrices/` 下文件的历史交叉），与本次 WS-A 无关。
- 本次新增内容未引入新的跨目录重复。

### 4.2 代码块编译检查

```bash
python scripts/check_concept_code_blocks.py --sample 0 --strict \
  --report reports/IDIOMS_CODE_BLOCKS_CHECK_2026_08_04.md \
  --json tmp/idioms_cb_2026_08_04.json
```

- 本次新增在 `02_idioms_spectrum.md` 中的代码块全部通过编译/失败标注验证；修复了 `#![deny(improper_ctypes_definitions)]` 的 `compile_fail` 块，使其真实失败。
- 全库 `strict` 模式下 rot=20，全部位于其他文件（`48_api_guidelines_idioms.md`、`47_rust_design_and_architecture_patterns_semantic_atlas.md`、嵌入式系列等），属于 P7 其他 WS 或既有技术债务，未由 WS-A 引入。

---

## 五、主要新增内容摘要

### 7.9 错误处理惯用法：`Result` 类型设计与 `?` 传播

- 自定义 `ConfigError` 实现 `std::error::Error` + `Error::source()` 因果链。
- `type Result<T> = std::result::Result<T, ConfigError>` 别名减少样板。
- `From<io::Error>` + `?` 自动转换；`map_err` 保留底层 `source`。
- 反例：未实现 `From`/`Error` 导致 `?` 编译失败；库 API 对可恢复失败使用 `expect`/`panic`。

### 7.10 集合惯用法：`entry`、`retain`、容量预分配与选型

- `HashMap::with_capacity` + `entry(...).or_insert(0)` 一次查找计数。
- `Vec::sort_unstable` + `dedup` 原地去重；`VecDeque` BFS 示例。
- 容器选型矩阵（HashMap vs BTreeMap vs VecDeque vs BinaryHeap）。
- 反例：同一键 `contains_key` → `insert` → `get_mut` 三次查找。

### 7.11 宏惯用法：声明宏卫生性与过程宏边界

- `ensure!` 与 `seq!` 示例展示 `tt` 片段与重复模式。
- 卫生性反例：宏内 `let x` 不会泄漏到调用方作用域。
- 决策树：固定简短模式 → `macro_rules!`；复杂/派生 → 过程宏 + syn/quote。

### 9.7 FFI/C-API 惯用法：暴露与消费 C ABI 的契约

- `LogConfig` opaque 类型 + `log_config_new` / `log_config_free` 配对。
- `CString`/`CStr` 字符串转换；`#[unsafe(no_mangle)]` + `extern "C"`。
- Rust↔C 方向/所有权语义矩阵；`catch_unwind` panic 边界提醒。
- 反例：`#[repr(C)]` 结构体包含 `String`/`Vec`（`compile_fail`）。

---

## 六、遇到的问题与后续跟进

1. **代码块门全库未通过**：`check_concept_code_blocks.py --strict` 全库 rot=20，均为既有文件问题，未因 WS-A 新增内容而增加。建议在 P7 集成阶段统一修复或分派给对应 WS 负责人。
2. **内容重叠检测历史对**：`01_rust_reference_and_normative_gap.md` 与 `docs/12_research_notes/01_alignment_matrices/` 的 0.60 相似对在本次任务前已存在，与惯用法页无关。
3. **未创建新文件**：本次仅在现有权威页 `02_idioms_spectrum.md` 内增强，因此 `concept/SUMMARY.md` 文件级导航无需调整；目录内子导航已在文件顶部 TOC 同步更新。

---

> **状态**: ✅ WS-A 惯用法权威对齐完成（v1.7）
> **最后更新**: 2026-08-04
> **相关文件**: `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md`
