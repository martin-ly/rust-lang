# Q4 2026 外部链接批量修复计划

> **日期**: 2026-07-09
> **依据**: `reports/I18N_LINK_HEALTH_CHECK_2026_06_28.md`
> **原则**: 只产出计划与脚本策略，不手动修复全部链接。

---

## 1. 当前基线

| 指标 | 数值 |
|---|---|
| 扫描范围 | `concept/`、`knowledge/`、`docs/` |
| 外部链接总数 | 4,365 |
| 手动检查（跳过） | 2,258 |
| 重定向链接 | **203** |
| 失效/异常链接 | **0** |

- 现有 `reports/link_replacements_*.json` 已按来源分类整理，共 9 个文件、约 125 条已验证替换/归档规则。
- 这些 JSON 文件是本次批量修复的**主要输入**，而非重新从头爬取。

---

## 2. 链接来源分类

按权威性与可修复性，将需要处理的链接分为 5 类：

### A. 官方 Rust 项目（高优先级、低风险）

- **来源**: `rust-lang.org`、`doc.rust-lang.org`、`rustfoundation.org`、`bevy.org`（已迁移）、`crates.io` 等。
- **特点**: 目标 URL 稳定，通常只是 `www.` 前缀去除、路径规范化、或域名迁移。
- **示例**:
  - `https://www.rust-lang.org/tools/install` → `https://rust-lang.org/tools/install/`
  - `https://foundation.rust-lang.org/news/` → `https://rustfoundation.org/media/`
- **策略**: 优先批量替换；替换后只需抽样验证 HTTP 200。

### B. 技术标准与 RFC（高优先级、中低风险）

- **来源**: `tools.ietf.org` → `datatracker.ietf.org`、IEEE 标准、Unicode、W3C、RTCA DO-178C 等。
- **特点**: 重定向通常由官方机构维护，目标 URL 语义等价。
- **示例**:
  - `https://tools.ietf.org/html/rfc3629` → `https://datatracker.ietf.org/doc/html/rfc3629`
  - `https://standards.ieee.org/standard/754-2019.html` → `https://standards.ieee.org/ieee/754/6210/`
- **策略**: 按规则批量替换；注意 RFC 锚点可能变化，需人工复核关键页面。

### C. 学术资源（中优先级、中风险）

- **来源**: `link.springer.com`、大学主页/讲义、ACM/IEEE Xplore、arXiv、个人学术博客等。
- **特点**:
  - Springer 常因 cookie 提示产生带 `?error=cookies_not_supported` 的 URL，实际内容不变；
  - 大学个人主页可能整体下线，需要寻找课程主页或替代入口；
  - PDF 链接可能迁移但文件名不变。
- **示例**:
  - `https://homepages.inf.ed.ac.uk/gdp/publications/Structural_Operational_Semantics.pdf` → `sos_jlap.pdf`
  - `https://www.cs.brown.edu/~mph/HerlihyShavit/` → Brown 课程页
- **策略**: 优先处理高引用量链接；对无法找到等价内容的链接标记为 `archive` 或补充 Wayback Machine 链接。

### D. 企业与平台文档（中优先级、中低风险）

- **来源**: Microsoft Learn、GitHub Docs、Azure docs、JetBrains、MongoDB、Redis、Sentry、Stripe 等。
- **特点**: 文档重构频繁，路径变化大，但通常有明确的新首页或重定向。
- **示例**:
  - `https://docs.microsoft.com/en-us/dotnet/csharp/` → `https://learn.microsoft.com/en-us/dotnet/csharp/`
  - `https://docs.github.com/en/actions/using-workflows/reusing-workflows` → 新 how-to 路径
- **策略**: 按 JSON 中的 `new_url` 批量替换；对“最接近但非等价”的替换在注释中标注，便于后续审校。

### E. 社区博客与第三方项目（低优先级、高风险）

- **来源**: 个人博客（without.boats、ralfj.de、smallcultfollowing.com）、Rust 社区站点、初创公司主页等。
- **特点**: 域名/路径变更、文章下线、站点整体迁移。
- **示例**:
  - `https://without.boats/blog/pin-and-suffering/` → `/blog/pin/`
  - `https://rust-secure-code.github.io/` → GitHub 仓库
- **策略**: 逐个审校，不盲目批量替换；对无法修复的链接采用 `archive` 策略或删除。

---

## 3. 批量修复策略

### 3.1 输入数据

- 主来源：`reports/I18N_LINK_HEALTH_CHECK_2026_06_28.md` 中的 **203 条重定向记录**。
- 辅助来源：`reports/link_replacements_*.json` 中已人工验证的 125 条规则。

### 3.2 处理流程

```text
Step 1: 解析 → 从报告中提取 (old_url, new_url, source_files) 三元组。
Step 2: 合并 → 与现有 JSON 替换规则去重、校验一致性（同名 old_url 必须指向相同 new_url）。
Step 3: 分类 → 按上述 A–E 类打上标签。
Step 4: 风险评估 → 对每类设定处理模式：
        - replace：直接文本替换（A、B、大部分 D）
        - archive：保留 old_url，但标注为历史/归档（C、E 中无等价内容者）
        - manual：需要人工判断（高引用量学术链接、社区博客）
Step 5: 执行 → 编写 Python 脚本 `scripts/batch_fix_external_links.py`，
        仅对 `replace` 模式执行 safe-in-place 替换（先备份、再 diff 复核）。
Step 6: 验证 → 重新运行 `python scripts/kb_auditor.py --link-check` 或等效命令，
        确认重定向数量下降、无新增 404。
Step 7: 归档 → 将已应用和未应用的规则更新到 `reports/link_replacements_*.json`，
        并生成本次修复报告。
```

### 3.3 脚本设计要点

- **精确匹配 URL**：使用正则或 Markdown 链接解析，避免误替换子串。
- **按文件去重**：同一文件内同一 old_url 只替换一次。
- **保留锚点**：如果 old_url 带 `#section`，且 new_url 也带锚点则保留；否则移除或人工处理。
- **生成审计日志**：输出 `reports/Q4_EXTERNAL_LINK_FIX_APPLIED_2026_07_09.json`，记录每处修改。
- **dry-run 模式**：默认不写入，先输出 diff 供 review。

### 3.4 分批建议

| 批次 | 类别 | 预估链接数 | 处理方式 | 目标时间 |
|---|---|---|---|---|
| Batch 1 | A 官方 Rust | ~50 | 自动替换 + 抽样验证 | 2026-07 |
| Batch 2 | B 标准/RFC | ~30 | 自动替换 + 抽样验证 | 2026-07 |
| Batch 3 | D 企业文档 | ~60 | 自动替换 + 按域名抽样验证 | 2026-08 |
| Batch 4 | C 学术资源 | ~40 | 半自动：脚本替换 + 人工复核 | 2026-08 |
| Batch 5 | E 社区/第三方 | ~23 | 人工审校，必要时 archive | 2026-09 |

---

## 4. 风险与缓解

| 风险 | 缓解措施 |
|---|---|
| 批量替换引入错误链接 | 所有替换必须来自已验证报告或 JSON；脚本默认 dry-run。 |
| 锚点丢失导致内容定位失败 | 替换后保留原锚点，若新 URL 无对应锚点则人工处理。 |
| 社区博客再次迁移 | 对高价值博客链接考虑补充 Wayback Machine 存档地址。 |
| 学术链接需要付费/订阅 | 优先保留 DOI；无法直接访问时在链接旁加注说明。 |
| 报告与实际文件状态不同步 | 每次批量修复后重新运行链接检查，更新报告。 |

---

## 5. 交付物

1. `scripts/batch_fix_external_links.py`（dry-run + apply + audit log）。
2. `reports/Q4_EXTERNAL_LINK_FIX_APPLIED_2026_07_09.json`（应用记录）。
3. 更新后的 `reports/I18N_LINK_HEALTH_CHECK_YYYY_MM_DD.md`（重跑链接检查后生成）。
4. 未解决链接清单 `reports/Q4_EXTERNAL_LINK_UNRESOLVED_2026_07_09.md`（含 archive/manual 标记）。

---

## 6. 结论

- 以 `reports/I18N_LINK_HEALTH_CHECK_2026_06_28.md` 中的 **203 条重定向** 和现有 `link_replacements_*.json` 为输入，按 **A→B→D→C→E** 的优先级分 5 批处理。
- 不手动修复全部链接，而是通过脚本实现可审计、可回滚的批量替换。
- 预计可将重定向链接降至 20 条以内，并把剩余无法自动处理的链接明确标记为 archive 或 manual。
