# 📅 每季度权威来源同步检查表

> **使用说明:** 每季度初（1月、4月、7月、10月）由维护者执行此检查表，确保项目内容与权威来源保持同步。
>
> **本季度:** ******年 第 __ 季度
> **执行人:** ________________
> **执行日期:** ____-**-**
> **预计完成日期:** ____-**-__

---

## 1️⃣ Rust 官方生态更新

### Rust 官方博客

- [ ] 阅读 [Rust 官方博客](https://blog.rust-lang.org/) 本季度所有文章
- [ ] 检查新版本发布说明（如有）
- [ ] 识别与项目相关的新特性或重大变更
- [ ] 记录待学习/待集成的特性

| 文章/发布 | 日期 | 相关特性 | 影响评估 | 行动计划 |
|-----------|------|----------|----------|----------|
| | | | | |
| | | | | |

### crates.io 生态更新

- [ ] 运行 `cargo outdated -R` 检查所有根依赖
- [ ] 检查是否有主版本号更新（semver-major）
- [ ] 评估关键依赖（tokio, serde, axum 等）的更新影响
- [ ] 检查 `Cargo.lock` 中是否有已知漏洞

| Crate | 当前版本 | 最新版本 | 更新类型 | 影响评估 | 决策 |
|-------|----------|----------|----------|----------|------|
| | | | | | |
| | | | | | |

### RUSTSEC 安全公告

- [ ] 查阅 [RUSTSEC 数据库](https://rustsec.org/advisories/)
- [ ] 检查项目依赖是否涉及本季度新公告
- [ ] 运行 `cargo audit` 确认当前状态
- [ ] 如有漏洞，记录修复计划

| 公告 ID | 受影响 Crate | 严重程度 | 修复版本 | 状态 |
|---------|-------------|----------|----------|------|
| | | | | |
| | | | | |

---

## 2️⃣ 国际权威来源覆盖度

### Google / Microsoft / AWS 官方更新

- [ ] 检查 [Google Rust 博客/指南](https://opensource.googleblog.com/search/label/Rust) 新内容
- [ ] 检查 [Microsoft Rust 团队博客](https://devblogs.microsoft.com/rust/) 新文章
- [ ] 检查 [AWS Rust SDK 更新](https://github.com/awslabs/aws-sdk-rust/releases)
- [ ] 检查 [Rust Foundation](https://foundation.rust-lang.org/news/) 新闻

| 来源 | 新文章/更新 | 日期 | 相关主题 | 是否需覆盖 |
|------|------------|------|----------|-----------|
| | | | | |
| | | | | |

### 学术与行业标准

- [ ] 检查 [Rust RFC 仓库](https://github.com/rust-lang/rfcs) 本季度合并的 RFC
- [ ] 检查 [Rust Reference](https://doc.rust-lang.org/reference/) 更新
- [ ] 关注 [This Week in Rust](https://this-week-in-rust.org/) 中的最佳实践

| RFC / 文档 | 状态 | 影响 | 计划 |
|------------|------|------|------|
| | | | |
| | | | |

---

## 3️⃣ 项目内容同步

### 代码库对齐

- [ ] 检查各 crate 是否使用推荐的最新 API 模式
- [ ] 验证示例代码是否仍在最新稳定版上编译通过
- [ ] 检查是否有已废弃的 API 仍在使用
- [ ] 评估是否需要新增 crate 覆盖新领域

| Crate | 检查项 | 状态 | 备注 |
|-------|--------|------|------|
| c01_ownership_borrow_scope | 编译通过 | ⬜ | |
| c02_type_system | 编译通过 | ⬜ | |
| c03_control_fn | 编译通过 | ⬜ | |
| c04_generic | 编译通过 | ⬜ | |
| c05_threads | 编译通过 | ⬜ | |
| c06_async | 编译通过 | ⬜ | |
| c07_process | 编译通过 | ⬜ | |
| c08_algorithms | 编译通过 | ⬜ | |
| c09_design_pattern | 编译通过 | ⬜ | |
| c10_networks | 编译通过 | ⬜ | |
| common | 编译通过 | ⬜ | |

### 文档完整性

- [ ] 检查 `docs/` 目录是否有需要新增的指南
- [ ] 验证知识库索引 `knowledge/INDEX.md` 是否最新
- [ ] 检查 `README.md` 和 `CHANGELOG.md` 是否需要更新
- [ ] 确认所有外部链接仍然有效

---

## 4️⃣ 技术债务评估

- [ ] 统计并审查 Clippy 警告数量趋势
- [ ] 审查未解决的 GitHub Issues
- [ ] 审查未合并的 Pull Requests
- [ ] 检查是否有技术债务需要本季度偿还

| 类型 | 数量 | 上季度 | 趋势 | 备注 |
|------|------|--------|------|------|
| Clippy 警告 | | | | |
| 开放 Issues | | | | |
| 开放 PRs | | | | |
| 已知 TODO | | | | |

---

## 5️⃣ 归档与总结

### 本季度决策记录
<!-- 在此记录本季度做出的重要决策 -->

1.
2.
3.

### 下季度关注项
<!-- 记录需要下季度优先处理的事项 -->

1.
2.
3.

### 检查表完成确认

- [ ] 所有检查项已审核
- [ ] 发现的问题已记录到 Issues
- [ ] 本季度总结已归档到 `archive/202X/QX/`
- [ ] 下季度 PDCA 计划已更新

---

> 📁 **归档路径:** `archive/YYYY/QN/quarterly-sync-checklist-YYYY-QN.md`
>
> 🔄 **关联文档:** [PDCA 循环模板](./PDCA_TEMPLATE.md)
