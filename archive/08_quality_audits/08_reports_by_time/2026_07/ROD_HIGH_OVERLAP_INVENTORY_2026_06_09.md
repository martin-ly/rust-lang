# rust-ownership-decidability/ 高重复度文件评估清单

> **扫描日期**: 2026-06-09
> **评估标准**: 与 concept/ / knowledge/ / docs/ 主轨的相似度 ≥ 0.75
> **处理策略**: [保留] / [迁移] / [归档] / [删除]

---

## 完全重复（相似度 = 1.00）— 优先处理

| # | ROD 文件 | 主轨文件 | 决策 | 理由 | 行动 |
|:---|:---|:---|:---:|:---|:---|
| 1 | `17-unsafe-rust/01-intro.md` | `concept/03_advanced/03_unsafe.md` | **归档** | ROD 版本更侧重形式化视角，但概念覆盖完全被 concept/ 包含 | 添加 `[ARCHIVED: 内容已迁移至 concept/03_advanced/03_unsafe.md]`，移至 `archive/` |
| 2 | `extensions/unsafe-rust-patterns.md` | `concept/03_advanced/03_unsafe.md` | **归档** | 与 concept/ 中 unsafe patterns 章节完全重叠 | 同上 |
| 3 | `extensions/rust-for-linux.md` | `concept/07_future/19_rust_for_linux.md` | **归档** | ROD 版本更简短，concept/ 覆盖更深 | 同上 |

## 高度重复（相似度 = 0.80-0.99）— 次要处理

| # | ROD 文件 | 主轨文件 | 相似度 | 决策 | 理由 | 行动 |
|:---|:---|:---|:---:|:---:|:---|:---|
| 4 | `16-program-semantics/rust-194-features/05-edition-2024-semantics.md` | `concept/07_future/19_rust_edition_preview.md` | 0.90 | **迁移** | ROD 版本侧重借用规则语义形式化，可补充至 concept/ 的「形式化视角」节 | 提取 unique 内容，合并至 concept/，ROD 添加引用标记 |
| 5 | `comparative-analysis/rust-vs-cpp.md` | `concept/05_comparative/01_rust_vs_cpp.md` | 0.75 | **保留** | ROD 版本侧重工程视角（性能基准、代码示例），concept/ 侧重形式化论据，双轨互补 | 添加 `[对比视角: concept/05_comparative/01_rust_vs_cpp.md]` 引用标记 |
| 6 | `comparative-analysis/rust-vs-java.md` | `concept/05_comparative/06_rust_vs_java.md` | 0.75 | **保留** | 同上，工程视角 vs 教学视角 | 同上 |
| 7 | `comparative-analysis/rust-vs-python.md` | `concept/05_comparative/07_rust_vs_python.md` | 0.75 | **保留** | 同上 | 同上 |
| 8 | `comparative-analysis/rust-vs-go.md` | `concept/05_comparative/02_rust_vs_go.md` | 0.75 | **保留** | 同上 | 同上 |
| 4 | `16-program-semantics/rust-194-features/05-edition-2024-semantics.md` | `concept/07_future/19_rust_edition_preview.md` | 0.90 | **保留** | ROD 版本含形式化语义、安全定理、借用图分析等 unique 内容，concept/ 为教学文档 | 添加 `[形式化视角: ROD/...]` 引用标记至 concept/ 文件 |

## 中度重复（相似度 = 0.60-0.79）— 长期跟踪

| # | ROD 文件 | 主轨文件 | 相似度 | 决策 | 备注 |
|:---|:---|:---|:---:|:---:|:---|
| 9 | `03-verification-tools/03-08-gillian-rust.md` | `concept/03_advanced/03_unsafe.md` | 0.75 | **保留** | ROD 独有的验证工具视角，无 concept/ 对应 |
| 10 | `comparative-analysis/` 其他文件 | `concept/05_comparative/` 其他文件 | 0.60-0.75 | **保留** | 形式化视角 vs 教学视角，双轨合理 |

---

## 本周执行清单（Week 1）

- [ ] **D1-D2**: 处理 #1-3（完全重复归档）
- [ ] **D3**: 评估 #5-8（对比分析文件人工审阅）
- [ ] **D4**: 处理 #4（Edition 语义迁移）
- [ ] **D5**: 更新治理策略文档，记录本周处理量

## 关键原则

1. **concept/ 为主轨**: 所有教学性内容以 concept/ 为权威版本
2. **ROD 保 unique**: 仅保留 ROD 独有的形式化/研究视角内容
3. **归档非删除**: 完全重复文件移至 `archive/`，保留 git 历史
4. **引用链完整**: 归档文件添加 `[ARCHIVED: 参见 concept/...]` 链接

---

> **维护者**: Kimi Code CLI
> **下次更新**: 2026-06-15
