# 贡献指南 (Contributing)

> **最后更新**: 2026-02-11

感谢您对本 Rust 学习项目的关注！

---

## 如何贡献

1. **报告问题**: 发现错误或有改进建议 → 提交 Issue
2. **改进文档**: 修正错别字、完善说明 → 提交 PR
3. **添加示例**: 分享实用代码示例 → 提交 PR
4. **分享经验**: 写博客、录视频 → 加入社区讨论

---

## 贡献流程

```bash
# 1. Fork 项目
git clone <your-fork-url>

# 2. 创建分支
git checkout -b feature/your-feature

# 3. 进行修改
# ... 编辑文件 ...

# 4. 提交改动
git add .
git commit -m "描述你的改动"

# 5. 推送分支
git push origin feature/your-feature

# 6. 创建 Pull Request
```

---

## 模块贡献

各模块可能有独立的贡献指南：

- [C01 所有权](./crates/c01_ownership_borrow_scope/CONTRIBUTING.md)
- [C02 类型系统](./crates/c02_type_system/CONTRIBUTING.md)
- [研究笔记](./docs/research_notes/CONTRIBUTING.md)

---

---

## 文档链接规范

**链接格式**：确保文档内链接正确指向目标文件。

- **从 docs/ 引用 crates**：使用 `../crates/` 或 `../../crates/`（取决于文档所在目录深度）
- **tier 目录**：统一使用 `tier_01_foundations`、`tier_02_guides`、`tier_03_references`、`tier_04_advanced` 命名（不含 `tier1_foundation`、`tier3_advanced` 等旧格式）
- **文件名**：与实际文件名保持一致（大小写、下划线），如 `01_wasm_基础指南.md` 而非 `01_WASM快速入门.md`
- **链接检查**：提交 PR 前建议运行 `cargo deadlinks` 或 `markdown-link-check` 检查断链

详见 [LINK_FIX_PLAN_2026_02.md](./docs/LINK_FIX_PLAN_2026_02.md) 与 [PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md](./docs/PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md)。

---

## 相关文档

- [项目结构](./PROJECT_STRUCTURE.md)
- [README](./README.md)
