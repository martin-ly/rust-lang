# KB Auditor 扩展报告：Z3 — docs/content/knowledge 死链检查纳入

> **任务**: 将 `docs/`、`content/`、`knowledge/` 三轨本地 markdown 链接纳入 `kb_auditor.py` 死链检查。
> **执行时间**: 2026-07-14
> **执行者**: Agent Z3

---

## 1. 扩展内容

### 1.1 `scripts/kb_auditor.py` 改动

- 新增常量 `EXTRA_DIRS = ["docs", "content", "knowledge"]`。
- 新增函数 `find_extra_md_files()`：递归收集三轨下所有 `.md` 文件。
- 新增函数 `extract_markdown_links()`：按行提取 `[text](url)`，返回 `(行号, 文本, url)`；
  已排除代码块与行内代码（`` `...` ``），避免把代码片段/正则误识别为死链。
- 新增函数 `check_extra_dirs_dead_links()`：
  - 跳过 `http://`、`https://`、`mailto:`、纯锚点 `#`、跨仓库绝对路径 `/`；
  - 按源文件相对路径解析本地链接；
  - 无扩展名时尝试补 `.md`；
  - 收集失效链接的 `file/line/url/resolved`。
- `generate_dashboard()` 新增 `extra_dead_links` 参数：
  - 全局指标表新增 `docs/content/knowledge 死链数量`；
  - 报告新增「docs/content/knowledge 死链检查」小节，列示所有失效链接。
- `main()` 调用新检查，并将其计入退出码：任意死链 >0 则 exit 非 0。

### 1.2 CI / 文档同步

- `.github/workflows/quality_gates.yml`:
  - job 名称改为 `KB Auditor Link Check (concept + docs + content + knowledge)`；
  - step 名称/注释说明覆盖范围。
- `AGENTS.md` §5.1:
  - 门 7 描述补充为覆盖 `concept/ + docs/ + content/ + knowledge/` 死链；
  - §5 常用命令与 §7 长期治理机制中的死链检查注释同步更新。

---

## 2. 死链扫描与修复统计

| 阶段 | 死链数 | 说明 |
|:---|---:|:---|
| 扩展前 concept/ 死链 | 0 | 历史基线保持 |
| 扩展后首次扫描（docs/content/knowledge） | 707 | 含相对路径错误、文件重编号/归档、目录深度错误、行内代码误报 |
| 自动修复（`tmp/fix_extra_dead_links.py`） | 670 | 按仓库内目标路径重新计算相对链接 |
| 剩余实际死链 | 37 | 代码误报 3 + 需人工确认路径 34 |
| 人工/半自动修复后 | 0 | 逐条核对并修复或降级为纯文本 |

### 修复示例（优先 concept/ 链接）

- `docs/01_core/README.md`: `.../08_error_handling/01_error_handling.md` → `01_error_handling_basics.md`
- `docs/03_reference/07_trpl_3rd_ed_diff.md`: 多个 `../concept/...` 深度错误 → `../../concept/...`
- `docs/08_usage_guides/14_kani_practical_guide.md`: `./concept/04_formal/.../32_kani.md` → `../../concept/04_formal/04_model_checking/09_kani.md`
- `docs/12_research_notes/.../02_tower_architecture.md`: `.../06_ecosystem/05_formal_ecosystem_tower.md` → `.../08_formal_verification/01_formal_ecosystem_tower.md`
- 已不存在的 `data/i18n_terminology.yaml`：7 个文件中的链接降级为纯文本，避免死链。

---

## 3. 验证结果

### 3.1 KB Auditor

```bash
python scripts/kb_auditor.py --link-check
```

- concept/ 死链: **0**
- docs/content/knowledge 死链: **0**
- 跨层引用问题: **0**
- 模板化 ⟹: **0**
- **EXIT=0**

`reports/kb_quality_dashboard.md` 已包含新增「docs/content/knowledge 死链检查」小节。

### 3.2 全量质量门

```bash
bash scripts/run_quality_gates.sh
```

结果：

```text
✅ All 23 quality gates passed (23 blocking + 0 semantic observe).
EXIT=0
```

逐项均通过：

| # | 门 | 结果 |
|---|:---|:---|
| 1 | Cargo Check | ✅ |
| 2 | Cargo Test | ✅ |
| 3 | Cargo Clippy | ✅ |
| 4 | Cargo Audit | ✅ |
| 5 | Cargo Vet | ✅ |
| 6 | mdBook Build | ✅ |
| 7 | KB Auditor Link Check (concept + docs + content + knowledge) | ✅ |
| 8 | Content Overlap Detection | ✅ |
| 9 | i18n Term Coverage | ✅ |
| 10 | Mermaid Syntax Check | ✅ |
| 11 | Metadata Consistency (strict) | ✅ |
| 12 | Content Overlap v2 (blocking) | ✅ 可处理项=0 |
| 13 | Topology Quality (strict) | ✅ |
| 14 | KG SHACL Validation (strict) | ✅ |
| 15 | Semantic Health (strict) | ✅ 99.6 grade=OK |
| 16 | Concept Authority Coverage (strict, --include-crates) | ✅ any=100% none=0 crates=64/64 |
| 17 | Canonical Uniqueness (strict) | ✅ |
| 18 | Concept Consistency Audit (strict) | ✅ |
| 19 | Naming Convention (strict) | ✅ ERROR=0 |
| 20 | Concept Code Blocks (strict) | ✅ rot=0 |
| 21 | Mindmap Coverage (strict) | ✅ |
| 22 | Quiz System (strict) | ✅ |
| 23 | Examples Compile Check (strict) | ✅ |

---

## 4. 结论

`kb_auditor.py` 已成功扩展为同时审计 `concept/` 与 `docs/`/`content/`/`knowledge/` 的本地 markdown 链接；历史 concept/ 基线与输出格式保持不变。扩展后首次扫描发现的 707 条死链已全部修复或处理，当前三轨死链数为 **0**，全部 23 个阻断质量门通过。
