# Rust 补丁版本响应工作流

**EN**: Rust Patch Release Response Workflow
**Summary**: 当 Rust 发布补丁版本（如 1.97.1 → 1.97.2）或出现关键安全公告（RUSTSEC/CVE）时，维护者应在 48 小时内完成的本工作流。

> **Rust 版本**: 1.97.1+ (Edition 2024)
> **最后更新**: 2026-07-28
> **权威来源**: [AGENTS.md §7 长期治理机制](../../AGENTS.md)

---

## 触发条件

- Rust 官方发布新的补丁版本（patch release）。
- RUSTSEC、CVE 或其他关键安全公告影响当前 MSRV 依赖链。
- `rust-version` 需要因上游工具链 bug 修复而提升。

---

## 响应时间

**目标：触发后 48 小时内完成以下全部可自动化检查，并提交更新。**

---

## 检查清单

### 阶段 1：确认影响范围（人工，0.5–1 小时）

- [ ] 阅读 [Rust Release Notes](https://releases.rs/) 或官方博客，确认补丁版本变更范围。
- [ ] 检查 [RUSTSEC 公告](https://rustsec.org/advisories/) 是否影响本仓库依赖。
- [ ] 判断是否需要提升 MSRV（`rust-version`）。

### 阶段 2：更新 MSRV 与工具链（人工 + 脚本）

- [ ] 更新根 `Cargo.toml` 的 `rust-version`。
- [ ] 更新 `rust-toolchain.toml` 的 `channel`（如使用）。
- [ ] 更新 `.clippy.toml` 的 `msrv`（如配置）。
- [ ] 运行自动化检查：

```bash
python scripts/patch_release_response.py 1.97.2
```

- [ ] 若需全部门验证，追加 `--check-gates`：

```bash
python scripts/patch_release_response.py 1.97.2 --check-gates
```

### 阶段 3：更新版本跟踪页（人工）

- [ ] 新建或更新 `concept/07_future/00_version_tracking/rust_1_XX_Y.md` 补丁权威页。
- [ ] 在 `concept/07_future/00_version_tracking/rust_1_XX_stabilized.md` 中引用该补丁。
- [ ] 更新 `concept/07_future/00_version_tracking/01_rust_version_tracking.md` 索引。
- [ ] 同步相关 Cargo 特性页（如 `cargo_1_XX_features.md`）。
- [ ] 更新 `concept/SUMMARY.md` 导航。

### 阶段 4：修复 MSRV 声明不一致（脚本）

```bash
python scripts/check_msrv_consistency.py --strict
```

- [ ] 修复所有不一致的 MSRV 声明。

### 阶段 5：运行全部 23 阻断质量门（脚本）

```bash
bash scripts/run_quality_gates.sh
```

- [ ] 全部通过。

### 阶段 6：人工复核与提交

- [ ] 复核补丁权威页是否包含：变更事实、影响范围、迁移建议、权威来源链接。
- [ ] 提交变更（由维护者执行 `git commit`）。

---

## 自动化辅助脚本

| 脚本 | 作用 |
|---|---|
| `scripts/patch_release_response.py <version>` | 校验 rust-version 声明、补丁页存在性、SUMMARY 引用、MSRV 一致性 |
| `scripts/patch_release_response.py <version> --check-gates` | 额外运行部分阻断门子集 |
| `scripts/check_msrv_consistency.py --strict` | 扫描全库 MSRV 声明一致性 |
| `scripts/run_quality_gates.sh` | 运行全部 23 阻断门 + 6 观察门 |

---

## 相关文件

- [AGENTS.md §7](../../AGENTS.md)
- `concept/07_future/00_version_tracking/`
- `scripts/check_msrv_consistency.py`
- `scripts/run_quality_gates.sh`
