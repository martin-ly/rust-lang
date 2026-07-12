# KG 消费层验证报告（v3 升级后）

**日期**: 2026-07-12
**范围**: `tools/` 消费层（doc_search / kg_rag / kg_browser）+ 退役物确认
**KG 真相源**: `concept/00_meta/kg_data_v3.json`（v3.1，491 实体 / 5853 关系）

---

## 1. tools/doc_search 裁定：**(b) 删除**

目录仅含一个自述 placeholder 的 README.md，无任何代码。

裁定理由：

1. **无独立价值，与既有能力重复**：仓库在 2026-07-12 已明确搜索架构——
   读者侧由 mdbook 内置 searchindex 提供（`book.toml [output.html.search]` 已启用），
   语义检索由 `tools/kg_rag/`（v3 向量混合检索）提供，编辑/代理侧由 ripgrep 提供。
   同日退役的 `scripts/build_search_index.py`（死代码，依赖不存在的 `concept_kb.json`）
   已印证"独立搜索索引无消费方"的结论。
2. **新增 FTS5 CLI 将违背仓库自身决策与 AGENTS.md 最小变更原则**，重新引入第二套
   搜索真相源，且需长期维护索引新鲜度。
3. **入链清理**：全库 grep 确认无活跃引用——仅 `archive/`（只读历史）、
   `reports/`（历史报告）、`.kimi/`（审计记录）提及，按归档政策不改动。
   `tools/` 下无索引 README，无需更新。

执行：删除 `tools/doc_search/` 整个目录。

## 2. kg_rag 端到端验证与修复

### 修复的 bug（3 个）

| # | Bug | 修复 |
|---|---|---|
| 1 | **向量索引缓存失效**：缓存键仅比较模型名+路径字符串，KG 从 474→491 实体后仍静默使用旧缓存 | 缓存键改为 fingerprint（模型 + 绝对路径 + KG 文件 mtime_ns + 实体数），失配自动重建 |
| 2 | **CWD 相对路径**：`KG_PATH = Path("concept/00_meta/kg_data_v3.json")` 仅在仓库根目录运行时有效 | 改为基于 `__file__` 锚定仓库根（`kg_core.REPO_ROOT`） |
| 3 | **venv 守卫失效**：`import numpy` 在 `_ensure_venv()` 之前，系统 Python 直接 ModuleNotFoundError，不会重入 venv | 重排导入顺序，numpy 纳入守卫检查 |

附带改进：抽出 stdlib-only 数据层 `tools/kg_rag/kg_core.py`（load_kg / iter_entities /
kg_adjacency / typed_edges / kg_paths），`entity_summary` 增加非英文 scopeNote 回退
（`ex:TableOfContents` 仅 zh）；`iter_entities` 兼容 `@type` 为列表的情形。

### Smoke 测试（`tools/kg_rag/smoke_test.py`，可复跑）

- venv 完整跑：**16/16 PASS**（含向量索引重建 491 实体 + 混合检索）
- 系统 Python（stdlib）：**12/12 PASS**，向量检索自动 SKIP

代表性查询场景实测：

| 场景 | 结果 |
|---|---|
| "Vec 是什么的实例"（instanceOf） | `Vec -instanceOf-> Collections` ✅ |
| "unsafe 相关有哪些工具 appliesTo" | 5 条：Miri、TreeBorrowsDeepDive、BehaviorConsideredUndefined、BorrowSanitizer(BSan)、RustBelt_02separation → `SafeAndEffectiveUnsafeRust` ✅ |
| "lifetimes_advanced 的等价节点"（equivalentTo） | `LifetimesAdvanced -equivalentTo-> Lifetimes_00traits` ✅ |
| 混合检索 "Vec dynamic array" | top-1 = `Vec`（combined 0.4274），top-5 含 Vec ✅ |
| 关系端点完整性 | 5853 条关系 0 个悬空端点 ✅ |

## 3. kg_browser 验证

- `generate_links.py` 重新生成 `kg_links.json`：**491 条**。
- 新增 `tools/kg_browser/validate_links.py` 脚本验证：**491 valid / 0 None / 0 stale / 0 broken**，
  即 100% 链接指向存在的 concept 文件，且全部实体仍在 KG 中。
- `build.py` 重建 `index.html`（2.37 MB，内嵌 v3.1 数据，含 `instanceOf` 等新类型化边渲染）。
- 登记：`tools/kg_browser/README.md`（新建）、`tools/kg_rag/README.md`（补充 smoke 用法）。

## 4. 退役物确认

| 退役物 | 状态 |
|---|---|
| `concept_index.json` | ✅ 已退役：活跃目录无此文件，实体在 `archive/2026/concept_index_retired_2026-05-21.json`；4 处活跃文档引用均为"已退役，以 kg_data_v3.json 为唯一真相源"的说明性注记，无代码消费者 |
| `kg_data_v2.json` | ✅ 已退役：`archive/2026/kg_data_v2_retired_2026-07-12.json`，活跃目录无残留 |
| `concept/00_meta/kg_data.json`（**v1**，version 1.0，2026-05-23，28 实体/20 关系） | ⚠️→✅ 本次发现并处置：仍滞留活跃目录、构成第二套过期真相源。已移至 `archive/2026/kg_data_v1_retired_2026-05-23.json`；同步更新 `kg_ontology_v2.md`（叙述 + kg-validate 示例命令改指 v3）、`kg_shapes.ttl`（注释）、`scripts/apply_renumber.py`（注释；跳过集合保留作防御） |

全库 grep（排除 archive/book/tmp/reports/.kimi）确认：退役后无任何活跃代码引用
`kg_data.json` / `kg_data_v2` / `concept_index.json`。

## 5. 质量门验证

| 门 | 结果 |
|---|---|
| `python tools/kg_rag/smoke_test.py`（venv） | ✅ 16/16 |
| `python tools/kg_browser/validate_links.py` | ✅ exit 0（491/491） |
| `python scripts/check_kg_shapes.py --strict` | ✅ exit 0（K1–K7 全 0） |
| `python scripts/kb_auditor.py` | ✅ exit 0，死链 0 |
| `mdbook build` | ✅ 通过；`book/00_meta/kg_data.json` 已随构建清除 |

## 6. 变更清单

- 删除：`tools/doc_search/`（空壳目录）
- 移动：`concept/00_meta/kg_data.json` → `archive/2026/kg_data_v1_retired_2026-05-23.json`
- 新增：`tools/kg_rag/kg_core.py`、`tools/kg_rag/smoke_test.py`、
  `tools/kg_browser/validate_links.py`、`tools/kg_browser/README.md`
- 修改：`tools/kg_rag/kg_rag.py`（3 bug 修复 + 重构）、`tools/kg_rag/README.md`、
  `concept/00_meta/knowledge_topology/kg_ontology_v2.md`、`concept/00_meta/kg_shapes.ttl`、
  `scripts/apply_renumber.py`（注释）
- 重建：`tools/kg_rag/.cache/index.pkl`（491 实体）、`tools/kg_browser/kg_links.json`、
  `tools/kg_browser/index.html`
