# 2027 Q1 国际化维护机制

> **目标**: 建立可持续的国际化（i18n）维护流程，确保双语元数据、术语一致性、权威来源链接长期有效
> **生效日期**: 2027-01-01
> **维护周期**: 每季度一次（1 月、4 月、7 月、10 月）
> **责任人**: 项目维护者 + 社区贡献者

---

## 一、维护范围

1. **双语元数据**: 所有 `concept/` Markdown 文件的 `**EN**` / `**Summary**` 头
2. **术语一致性**: `concept/` EN 标题与 `concept/00_meta/terminology_glossary.md` 的对齐
3. **权威来源链接**: `concept/` / `knowledge/` / `docs/` 中外部链接的健康状态
4. **学习路径入口**: `LEARNING_MVP_PATH.md` 中国际资源链接的可用性
5. **社区反馈**: issue/PR 中关于 i18n 的响应

---

## 二、季度检查清单

### 2.1 双语元数据检查

```bash
python scripts/i18n/check_concept_headers.py
```
- 验收标准：符合 EN + Summary 要求的文件比例 = 100%
- 如发现缺失：由维护者或贡献者在 7 天内补齐

### 2.2 术语一致性检查

```bash
python scripts/i18n/check_terminology_consistency.py
```
- 验收标准：无“通用占位符误用”
- 如发现不一致：在 issue 中标注 `i18n-terminology`，7 天内讨论并修复

### 2.3 链接健康检查

```bash
python scripts/i18n/check_external_links.py
```
- 验收标准：
  - 失效链接（4xx/5xx/timeout）< 1% 的外部链接总数
  - 重定向链接逐步更新为最终 URL
- 如发现失效：
  - 官方链接（TRPL / Reference / RFC）优先修复
  - 学术论文 / 商业网站链接可替换为 archive.org 镜像或标注 `[已失效]`

### 2.4 学习路径入口检查

- 手动验证 `LEARNING_MVP_PATH.md` 中 4 个国际资源入口可访问
- 验证 `authority_source_map.md` 中新增锚点是否仍然有效

### 2.5 社区反馈响应

- 统计上季度 i18n 相关 issue/PR 数量
- 更新 `CONTRIBUTING.md` 中的国际化贡献指南（如有必要）

---

## 三、Issue / PR 标签与 SLA

| 标签 | 含义 | 响应 SLA | 解决 SLA |
|---|---|---|---|
| `i18n-terminology` | 术语对照问题 | 48h | 7 天 |
| `i18n-link` | 外部链接失效 | 48h | 14 天 |
| `i18n-translation` | 翻译/英文摘要改进 | 72h | 21 天 |
| `i18n-audit` | 季度审计任务 | 7 天 | 季度末 |

---

## 四、自动化工具链

| 脚本 | 用途 | 触发方式 |
|---|---|---|
| `scripts/i18n/check_concept_headers.py` | 检查 EN/Summary 头 | 季度审计 + CI（可选） |
| `scripts/i18n/check_terminology_consistency.py` | 检查术语一致性 | 季度审计 + CI（可选） |
| `scripts/i18n/check_external_links.py` | 检查外部链接 | 季度审计（手动触发） |

**建议 CI 集成**（可选）：

- 在 `.github/workflows/ci.yml` 中新增 `i18n-metadata` job
- 每次 PR 修改 `concept/` 文件时运行前两个脚本
- 链接检查因耗时较长，保留为季度手动任务

---

## 五、报告模板

每季度审计完成后，创建报告 `reports/I18N_AUDIT_YYYY_MM_DD.md`，包含：

1. 执行摘要
2. 元数据完整性数据
3. 术语一致性状态
4. 链接健康状态（总数 / 失效 / 重定向 / 手动检查）
5. 社区反馈统计
6. 下季度改进计划

---

## 六、人员分工建议

| 角色 | 职责 |
|---|---|
| 项目维护者 | 季度审计触发、最终审核、标签管理 |
| 内容贡献者 | 补齐 EN/Summary、修复术语不一致 |
| 社区志愿者 | 报告失效链接、参与可用性测试 |
| 翻译审校者 | 审核英文摘要质量、对接 TRPL 术语 |

---

## 七、持续改进指标

| 指标 | 目标 |
|---|---|
| EN/Summary 覆盖率 | 100% |
| 术语一致性脚本通过 | 100% |
| 外部链接失效率 | < 1% |
| i18n issue 响应率 | 100%（按 SLA） |
| 季度审计报告产出 | 4 份 / 年 |
