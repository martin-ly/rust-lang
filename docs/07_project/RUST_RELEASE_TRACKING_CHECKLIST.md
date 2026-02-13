# Rust 新版本发布追踪 Checklist

> **创建日期**: 2026-02-12
> **用途**: Rust 新版本发布后的文档与配置更新流程

---

## 触发时机

- Rust 稳定版发布（通常每 6 周）
- 官方公告：<https://blog.rust-lang.org/releases/>
- 详细 changelog：<https://releases.rs/>

---

## Checklist

### 1. 获取权威信息

- [ ] 阅读 [Rust Blog 发布公告](https://blog.rust-lang.org/releases/)
- [ ] 阅读 [releases.rs 详细 changelog](https://releases.rs/)
- [ ] 记录破坏性变更与未来不兼容警告

### 2. 更新 toolchain 文档

- [ ] 新建 `docs/06_toolchain/0X_rust_1.XX_vs_1.YY_comparison.md`（或更新序号）
- [ ] 更新 [toolchain/README.md](../06_toolchain/README.md) 文档列表
- [ ] 新建 `docs/06_toolchain/0X_rust_1.XX_compatibility_notes.md`（若有兼容性变更）
- [ ] 更新 [08_rust_version_evolution](../06_toolchain/08_rust_version_evolution_1.89_to_1.93.md) 或新建演进链

### 3. 更新版本声明

- [ ] 根 [Cargo.toml](../../Cargo.toml) 中 `rust-version`
- [ ] [Cargo.workspace](../../Cargo.workspace) 中 `target-rust-version`
- [ ] 各 crate 的 `rust-version`（c01–c12）

### 4. 更新速查卡

- [ ] 批量更新 `docs/02_reference/quick_reference/*.md` 中的「Rust 版本」元数据
- [ ] 更新 [quick_reference/README.md](../02_reference/quick_reference/README.md) 版本声明

### 5. 更新思维表征

- [ ] 更新 [THINKING_REPRESENTATION_METHODS.md](../04_thinking/THINKING_REPRESENTATION_METHODS.md) 中的版本特性思维导图
- [ ] 更新 [MULTI_DIMENSIONAL_CONCEPT_MATRIX.md](../04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)（若有新选型维度）

### 6. 更新权威源同步日期（权威源元数据规范）

- [ ] 在 [07_rust_1.93_full_changelog.md](../06_toolchain/07_rust_1.93_full_changelog.md) 等 toolchain 文档末尾更新「最后对照 releases.rs: YYYY-MM-DD」
- [ ] 规范：所有 `docs/06_toolchain/*.md` 文档应在文末或元数据中包含「最后对照 releases.rs: 日期」，便于可维护性与可信度

### 7. 更新模块适配状态

- [ ] 更新 [MODULE_1.93_ADAPTATION_STATUS.md](./MODULE_1.93_ADAPTATION_STATUS.md)（或对应版本表）
- [ ] 在相关 crate 中增加新版本 API 示例（若有稳定化 API）

### 8. 验证

- [ ] `cargo build` 通过
- [ ] `cargo test` 通过
- [ ] `cargo test -p c01_ownership_borrow_scope --doc` 通过（含 compile_fail 反例）
- [ ] 检查文档断链：`./scripts/check_links.ps1` 或 `cargo deadlinks`（若已安装）

---

## 季度审查（每季度执行一次）

- [ ] 检查 [DECISION_GRAPH_NETWORK](../04_thinking/DECISION_GRAPH_NETWORK.md)、[PROOF_GRAPH_NETWORK](../04_thinking/PROOF_GRAPH_NETWORK.md) 等引用是否有效
- [ ] 核对各模块 README 中的版本声明与兼容性链接
- [ ] 确认 [10_rust_1.89_to_1.93_cumulative_features_overview](../06_toolchain/10_rust_1.89_to_1.93_cumulative_features_overview.md) 等累积文档是否需要扩展
- [ ] 更新「最后对照 releases.rs」日期（见 [07_rust_1.93_full_changelog](../06_toolchain/07_rust_1.93_full_changelog.md) 末尾）

---

## 模板：新版本对比文档结构

```markdown
# Rust 1.XX vs 1.YY 全面对比分析

- 版本概览
- 核心改进（3–5 项）
- 标准库更新
- 编译器改进
- 工具链更新
- 迁移指南
- 参考资源
```

---

## 相关文档

- [Rust 1.93 vs 1.92 对比](../06_toolchain/05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性注意事项](../06_toolchain/06_rust_1.93_compatibility_notes.md)
- [版本演进链](../06_toolchain/08_rust_version_evolution_1.89_to_1.93.md)
- [各模块 1.93 适配状态一览表](./MODULE_1.93_ADAPTATION_STATUS.md)
