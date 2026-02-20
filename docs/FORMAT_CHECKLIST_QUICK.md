# 文档格式快速检查清单

> **用途**: 快速检查 Markdown 文档格式合规性
> **适用**: 所有 docs 目录下的 .md 文件

---

## ✅ 元信息检查（所有文档必需）

- [ ] 包含 `> **创建日期**: YYYY-MM-DD`
- [ ] 包含 `> **最后更新**: YYYY-MM-DD`
- [ ] 包含 `> **Rust 版本**: 1.93.0+ (Edition 2024)`
- [ ] 包含 `> **状态**: ✅ 已完成 / 🔄 进行中 / 📋 规划中`
- [ ] 日期格式为 `YYYY-MM-DD`（非 `YYYY/MM/DD` 或其他）
- [ ] key 与冒号间无空格 (`**创建日期**:` 非 `**创建日期** :`)
- [ ] 冒号后有一空格 (`: 2026` 非 `:2026`)

---

## ✅ 标题层级检查

- [ ] 一级标题 `#` **不含 emoji**
- [ ] 二级标题 `##` 可选 emoji，但同类文档统一
- [ ] 目录块标题统一为 `## 📊 目录`
- [ ] 标题层级不跳跃（无 `#` → `###` 跳过 `##`）

---

## ✅ 表格格式检查

- [ ] 分隔行使用 `| :--- | :--- | :--- |`（左对齐）
- [ ] 不使用 `|---|` 或 `|:---:|`（居中对齐）
- [ ] 每行列数相同
- [ ] 表格前后有空行

**正确示例**:
```markdown
| 列 A | 列 B | 列 C |
| :--- | :--- | :--- |
| 内容 | 内容 | 内容 |
```

**错误示例**:
```markdown
| 列 A | 列 B | 列 C |
| --- | --- | --- |
| 内容 | 内容 |
```

---

## ✅ 链接格式检查

- [ ] 使用相对路径 `./path` 或 `../path`
- [ ] 不使用绝对路径 `/docs/path`
- [ ] 格式为 `[文本](路径)`
- [ ] 链接指向的文件存在

---

## ✅ 中文格式检查

- [ ] 术语使用一致（不混用 `泛型` / `generics`）
- [ ] 中文标点使用正确（，`。` 非 `,` `.`）

---

## ✅ 文末元信息（核心研究笔记必需）

适用于: formal_methods/, type_theory/, software_design_theory/, experiments/

- [ ] 文末包含 `---` 分隔线
- [ ] 包含 `**维护者**: 团队名称`
- [ ] 包含 `**最后更新**: YYYY-MM-DD`
- [ ] 包含 `**状态**: ✅ 已完成`

**正确示例**:
```markdown
---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-20
**状态**: ✅ 已完成
```

---

## 🔧 常用修复命令

### PowerShell 批量检查

```powershell
# 检查所有 .md 文件
Get-ChildItem -Path docs -Recurse -Filter "*.md" | ForEach-Object {
    Write-Host "检查: $($_.FullName)"
    # 检查元信息
    $content = Get-Content $_.FullName -Raw
    if ($content -notmatch "\*\*Rust 版本\*\*:") {
        Write-Host "  ⚠️ 缺少 Rust 版本" -ForegroundColor Yellow
    }
    if ($content -notmatch "\*\*创建日期\*\*:") {
        Write-Host "  ⚠️ 缺少创建日期" -ForegroundColor Yellow
    }
}
```

---

## 📖 相关文档

- [DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT](./DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md) - 完整审计报告
- [QUALITY_CHECKLIST](research_notes/QUALITY_CHECKLIST.md) - 质量检查清单
- [FORMAT_AND_CONTENT_ALIGNMENT_PLAN](research_notes/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md) - 格式统一计划
