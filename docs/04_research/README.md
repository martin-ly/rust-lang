# Research 目录 {#research-目录}

> **EN**: Research Index
> **Summary**: Research 目录 Research Index. (stub/archive redirect)
> **定位**: 已归档的**研究笔记与探索性内容**入口。本目录原用于存放早期研究材料，目前大部分内容已迁移至 `concept/`、`knowledge/` 或 `archive/`。
> **状态**: 维护模式 —— 不再主动新增研究笔记；新研究应直接写入 `concept/` 或 `knowledge/`，或按 C-class 治理规则归档。
> **最后整理**: 2026-06-25

---

## 目录结构 {#目录结构}

```text
docs/04_research/
├── README.md                 # 本文件
└── (子目录与历史研究笔记)    # 见 C-class 治理报告
```

---

## 治理规则 {#治理规则}

根据 `reports/C_CLASS_GOVERNANCE_PLAN_2026_06_09.md`：

1. 禁止在 C 类目录新建文件（除非明确标记为临时研究）。
2. 每季度运行一次 `scripts/detect_content_overlap.py` 检测重复。
3. 研究笔记完成 90 天后必须决定：迁移到主轨 / 归档 / 删除。
4. 每次归档后运行 `scripts/maintenance/fix_archived_research_notes_links.py` 清理引用（Reference）残留。

---

## 如需查找最新内容 {#如需查找最新内容}

- 形式化理论 → `concept/04_formal/`
- 学习路径 → `knowledge/`
- 已归档研究 → `archive/research_notes_2026_06_25/`
