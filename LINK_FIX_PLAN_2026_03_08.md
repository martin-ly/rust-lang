# 断链修复计划

> **日期**: 2026-03-08
> **断链总数**: 616 个
> **策略**: 按优先级分批修复

---

## 📊 断链分类统计

### 按类型分类

| 类型 | 数量 | 修复策略 |
|------|------|----------|
| 目录链接 (无 README) | ~150 | 添加 README.md 或改为具体文件 |
| 路径错误 | ~200 | 修正相对路径 |
| 文件不存在 | ~200 | 创建缺失文件或移除链接 |
| 锚点错误 | ~66 | 修正锚点 |

### 按优先级分类

| 优先级 | 文件 | 断链数 | 状态 |
|--------|------|--------|------|
| P0 | README.md (根) | 20+ | 待修复 |
| P0 | 00_MASTER_INDEX.md | 10+ | 待修复 |
| P1 | crates/*/README.md | 50+ | 待修复 |
| P1 | docs/guides/*.md | 100+ | 待修复 |
| P2 | 其他 | 400+ | 待修复 |

---

## 🔧 修复策略

### 策略 1: 目录链接修复

将目录链接改为指向 README.md：

```markdown
<!-- 修复前 -->
[quick_reference/](./02_reference/quick_reference/)

<!-- 修复后 -->
[quick_reference/](./02_reference/quick_reference/README.md)
```

### 策略 2: 路径修正

修正相对路径错误：

```markdown
<!-- 修复前 -->
[ownership_model](../../research_notes/formal_methods/ownership_model.md)

<!-- 修复后 -->
[ownership_model](../research_notes/formal_methods/ownership_model.md)
```

### 策略 3: 创建缺失文件

为缺失的关键文件创建占位符：

- docs/TROUBLESHOOTING.md
- docs/BEST_PRACTICES.md
- docs/CHANGELOG.md

---

## 📋 修复清单

### P0 - 根目录文件 (立即修复)

- [ ] README.md - 修复 20+ 断链
- [ ] PROJECT_STRUCTURE.md - 修复 10+ 断链
- [ ] 00_MASTER_INDEX.md - 修复 10+ 断链

### P1 - 核心指南 (今日修复)

- [ ] docs/05_guides/*.md - 批量修复
- [ ] docs/01_learning/*.md - 批量修复
- [ ] crates/*/README.md - 批量修复

### P2 - 其他文件 (后续修复)

- [ ] docs/research_notes/*.md
- [ ] docs/06_toolchain/*.md
- [ ] docs/archive/**/*.md

---

## ✅ 验收标准

- [ ] 根目录文件断链 < 5 个
- [ ] 核心指南断链 < 10 个
- [ ] 总断链数 < 100 个
- [ ] 关键用户路径无断链
