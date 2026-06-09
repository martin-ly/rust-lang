# 四轨执行计划 2026-06-09 至 2026-07-07

> **基线**: A类0 / B类1 / C类883 / L3测验8文件覆盖
> **决策确认**: 测验可运行化 ✅ / 先治 rust-ownership-decidability/ ✅ / 新增国际化 ✅

---

## 第1周（2026-06-09 至 06-15）轨道一 P0 + 轨道二 P0

### 轨道一：L3 核心补完 + 可运行验证

| 日 | 任务 | 目标文件 | 产出 |
|:---|:---|:---|:---|
| D1 | async_advanced 测验 | `concept/03_advanced/02_async_advanced.md` | 4道测验 + 可运行代码 |
| D2 | async_patterns 测验 | `concept/03_advanced/02_async_patterns.md` | 4道测验 + 可运行代码 |
| D3 | concurrency_patterns 测验 | `concept/03_advanced/10_concurrency_patterns.md` | 4道测验 + 可运行代码 |
| D4 | exercises 测验提取 | `exercises/tests/quizzes/l3_async_concurrency.rs` | 提取上述测验为可运行测试 |
| D5 | 已有测验可运行化改造 | `exercises/tests/quizzes/l3_core.rs` | 02_async/03_unsafe/04_macros/05_ffi 提取 |

### 轨道二：rust-ownership-decidability/ 高重复度评估

| 日 | 任务 | 目标 | 产出 |
|:---|:---|:---|:---|
| D1-D2 | 重复度 >0.8 文件清单 | `reports/ROD_HIGH_OVERLAP_INVENTORY_2026_06.md` | 精确文件对 + 处理建议 |
| D3-D4 | 样本深度评估 | 选10对完全重复(1.0)和10对高度重复(0.8-0.99) | 每对给出:保留/迁移/归档/删除 决策 |
| D5 | 治理脚本改进 | `scripts/detect_content_overlap.py` | 增加内容指纹去重 + 自动标记建议 |

---

## 第2周（2026-06-16 至 06-22）轨道一 P1 + 轨道二 P1

### 轨道一：L3 高价值主题 + 可视化

| 日 | 任务 | 目标文件 | 产出 |
|:---|:---|:---|:---|
| D1-D2 | atomics 测验 | `concept/03_advanced/11_atomics_and_memory_ordering.md` | 4道 + 内存序 Mermaid 图 |
| D3 | inline_assembly 测验 | `concept/03_advanced/13_inline_assembly.md` | 4道 + 寄存器图 |
| D4 | lock_free 测验 | `concept/03_advanced/16_lock_free.md` | 4道 + 算法流程图 |
| D5 | exercises 提取 | `exercises/tests/quizzes/l3_advanced_systems.rs` | 可运行测试 |

### 轨道二：重复内容迁移/归档

| 日 | 任务 | 目标 | 产出 |
|:---|:---|:---|:---|
| D1-D2 | 完全重复处理 | 10对1.0相似度文件 | 统一主轨/添加引用标记/删除副本 |
| D3-D4 | 高度重复处理 | 10对0.8-0.99相似度文件 | 评估后迁移 unique 内容 |
| D5 | 进度报告 | `reports/ROD_GOVERNANCE_WEEK2_REPORT.md` | 处理数量 + C类问题下降统计 |

---

## 第3周（2026-06-23 至 06-29）轨道三 + 轨道五 P0

### 轨道三：1.96 稳定化后文档刷新

| 日 | 任务 | 目标文件 | 变更 |
|:---|:---|:---|:---|
| D1 | assert_matches 刷新 | `concept/02_intermediate/05_assert_matches.md` | 移除 nightly 标记 → stable |
| D2 | core::range 速查表 | `docs/02_reference/quick_reference/02_collections_iterators_cheatsheet.md` | 新增 RangeToInclusive 等 |
| D3 | From<T> 文档补全 | `concept/02_intermediate/01_traits.md` | 补充 AssertUnwindSafe/LazyCell/LazyLock |
| D4 | Cargo 安全公告 | `docs/06_toolchain/` + `CHANGELOG.md` | 记录 CVE-2026-5222/5223 |
| D5 | 版本声明刷新 | 全部速查表头部 | 统一标注 1.96.0+ stable |

### 轨道五：mdBook 升级 + exercises 可运行化

| 日 | 任务 | 目标 | 产出 |
|:---|:---|:---|:---|
| D1 | book/ mdBook 检查 | `book/theme/book.js` | 确认 edition 2024 检测支持 |
| D2-D3 | exercises 测验架构 | `exercises/tests/quizzes/` | 模块化测试结构 + CI 集成 |
| D4 | 已有测验提取 | `exercises/tests/quizzes/l3_all.rs` | 整合所有 L3 测验为可运行测试 |
| D5 | CI 集成 | `.github/workflows/` | 新增 quizzes 测试 job |

---

## 第4周（2026-06-30 至 07-07）轨道一 P2 + 轨道五 P1 + 轨道四

### 轨道一：L4 形式化入门测验

| 日 | 任务 | 目标文件 | 产出 |
|:---|:---|:---|:---|
| D1-D2 | 所有权逻辑 | `concept/04_formal/` 相关文件 | 4道 Coq/Lean 伪代码对比测验 |
| D3 | 类型系统形式化 | `concept/04_formal/` 相关文件 | 4道 typing rule 推导测验 |

### 轨道五：国际化 + Cargo 优化

| 日 | 任务 | 目标 | 产出 |
|:---|:---|:---|:---|
| D4 | LEARNING_MVP_PATH_EN.md | `LEARNING_MVP_PATH_EN.md` | 英文版学习路径 |
| D5 | cargo update 同步脚本 | `scripts/sync_cargo_versions.py` | 自动化版本同步 |

### 轨道四：依赖管理

| 日 | 任务 | 目标 | 产出 |
|:---|:---|:---|:---|
| D5 | cargo vet 配置 | `.cargo/vet/` | 供应链审计初始化 |

---

## 关键里程碑

| 日期 | 里程碑 | 验收标准 |
|:---|:---|:---|
| 06-15 | Week 1 完成 | L3 新增12道可运行测验 + ROD高重复度清单 |
| 06-22 | Week 2 完成 | L3 再增12道 + ROD处理20对重复 |
| 06-29 | Week 3 完成 | 1.96文档刷新完成 + exercises测验CI集成 |
| 07-07 | Week 4 完成 | L4测验8道 + 英文路径 + cargo vet配置 |

## 每日节奏

- **上午**: 轨道一（测验开发）—— 需要高度专注的创造性工作
- **下午**: 轨道二/三/四/五（治理/刷新/基础设施）—— 可并行批处理
- **每日结束**: 更新本计划进度 + `cargo check --workspace` 验证

---

> **计划文件**: `reports/EXECUTION_PLAN_2026_06_09_WEEK1_4.md`
> **维护者**: Kimi Code CLI
> **下次更新**: 每周末同步实际进度
