# 项目综合状态梳理报告

> **梳理时间**: 2026-06-25  
> **项目根目录**: `E:\_src\rust-lang`  
> **Rust toolchain**: stable 1.96.0（默认 nightly 1.98.0）  
> **对应周期**: 2026-06-23 ~ 2026-07-20（第 4 周检查清单执行中）

---

## 一、执行摘要

- **代码构建**: `cargo check --workspace` 通过，无编译错误。
- **供应链安全**: `cargo audit` 0 个安全漏洞；`atomic-polyfill` 已修复，剩余 3 个 `unmaintained` 依赖已显式忽略并记录 rationale。
- **文档质量**: `docs/` A/B 类问题均为 **0**；C 类问题 **228**（均为最后更新超过 90 天的研究综述文件）。
- **链接健康**: 全库扫描 92,077 条链接，损坏 1,917 条（主要为历史/外部链接），问题文件 550 个。
- **C 类治理**: `docs/research_notes/` 已从 296 个文件精简至 **38** 个，归档 259 个文件到 `archive/research_notes_2026_06_25/`。
- **待提交改动**: 当前工作区有 12 个已修改/未跟踪文件，集中在 `cargo audit` 收尾、`cargo update` 版本刷新与报告生成。

---

## 二、代码与构建状态

| 检查项 | 命令 | 结果 |
|:---|:---|:---|
| Workspace 编译 | `cargo check --workspace` | ✅ 通过（0.54s，依赖已缓存） |
| 测试入口 | `cargo test --workspace` | 待执行（发布日 / 重大依赖变更后执行） |
| Clippy | `cargo clippy --workspace --all-features -- -D warnings` | 2026-06-24 通过 |

### 关键 crate 状态

- `c10_networks`: 已移除 `postcard` dev-dependency，消除 `atomic-polyfill` 传递依赖。
- `c12_wasm`: `web-sys` 已同步更新至 `0.3.103`。
- `c06_async`: `glommio` 0.9.0 保留（Linux io_uring 教学内容），其 `instant` 传递依赖已接受并忽略。
- `c13_embedded`: `cortex-m` 0.7.7 保留，`bare-metal` 传递依赖已接受并忽略。

---

## 三、供应链安全审计

### 3.1 `cargo audit` 结果

```bash
cargo audit --db "D:\_program\cargo\advisory-db" --file Cargo.lock
```

- **退出码**: 0
- **安全漏洞**: 0
- **`unmaintained` 警告**: 0（3 个已忽略）
- **Cargo.lock crate 实例数**: 1009

### 3.2 已处理的 `unmaintained` 依赖

| Crate | Advisory | 状态 | 来源 / 影响范围 |
|:---|:---|:---|:---|
| `atomic-polyfill` | RUSTSEC-2023-0089 | ✅ 已修复 | 原 `postcard` → `heapless` 传递依赖；已移除 c10_networks 的 `postcard` |
| `bare-metal` | RUSTSEC-2026-0110 | ⏸️ 已忽略 | `cortex-m` 0.7.7 传递依赖；仅 ARM 嵌入式 target |
| `instant` | RUSTSEC-2024-0384 | ⏸️ 已忽略 | `glommio` → `futures-lite` → `fastrand`；仅 Linux 实验性模块 |
| `paste` | RUSTSEC-2024-0436 | ⏸️ 已忽略 | `candle-core` / `libp2p` → `gemm` 等深层传递依赖；dev/benchmark |

### 3.3 已忽略的安全公告

| Advisory | 说明 |
|:---|:---|
| RUSTSEC-2023-0071 | `rsa` Marvin Attack；已移除 sqlx mysql feature，不再编译 |
| RUSTSEC-2026-0118 | `hickory-proto` 0.25.2 DNS 漏洞；libp2p 内部残留，未启用 mdns |
| RUSTSEC-2026-0119 | 同上 |

---

## 四、依赖版本刷新（2026-06-25 `cargo update`）

| Crate | 旧版本 | 新版本 | 配置位置 |
|:---|:---|:---|:---|
| `uuid` | 1.23.3 | 1.23.4 | `Cargo.toml` workspace |
| `wasm-bindgen` | 0.2.125 | 0.2.126 | `Cargo.toml` workspace |
| `js-sys` | 0.3.102 | 0.3.103 | `Cargo.toml` workspace |
| `wasm-bindgen-futures` | 0.4.75 | 0.4.76 | `Cargo.toml` workspace |
| `web-sys` | 0.3.102 | 0.3.103 | `crates/c12_wasm/Cargo.toml` |

> `wasm-bindgen-macro`、`wasm-bindgen-macro-support`、`wasm-bindgen-shared` 作为传递依赖已随 lock 自动升级。

---

## 五、文档与内容质量

### 5.1 `docs/` 价值审计

| 分类 | 文件数 | 问题数 | 说明 |
|:---|:---:|:---:|:---|
| A (核心参考) | 48 | 0 | 速查表、学习路径、核心参考 |
| B (指南工具) | 127 | 0 | 指南、工具链、实践文档 |
| C (研究综述) | 595 | 228 | 研究笔记、思考记录、大型专项（最后更新 >90 天） |

- 扫描文件数：770
- 报告：`reports/DOCS_VALUE_AUDIT_2026_06_25.md`

### 5.2 链接健康检查

| 指标 | 数值 |
|:---|---:|
| 总链接数 | 92,077 |
| 有效链接 | 31,181 |
| 损坏链接 | 1,917 |
| 外部链接 | 58,970 |
| 仅锚点链接 | 27,868 |
| 问题文件数 | 550 |

- 报告：`docs/LINK_CHECK_REPORT.md`

### 5.3 目录规模

| 目录 | 文件数 |
|:---|---:|
| `docs/` | 1,092 |
| `concept/` | 352 |
| `knowledge/` | 141 |
| `book/` | 324 |
| `content/` | 40 |
| `crates/` | 2,322 |
| `examples/` | 14 |
| `exercises/` | 514 |

### 5.4 C 类目录治理成果

- `docs/research_notes/` 当前剩余：**38** 个文件
- 已归档到 `archive/research_notes_2026_06_25/`：**259** 个文件
- ROD 核心结论已迁移到 `concept/04_formal/`：
  - `28_borrow_checking_decidability.md`
  - `29_type_inference_complexity.md`
  - `30_aeneas_symbolic_semantics.md`
- 精选内容已合并到 `knowledge/04_expert/academic/`：
  - `03_ownership_model_comprehensive.md`
  - `04_borrow_checker_proof_guide.md`
  - `05_type_system_foundations_guide.md`

---

## 六、工作流检查清单状态

依据 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`：

### P0：版本对齐与工具链

- ✅ Week 1（06-23 ~ 06-29）全部完成（async-std 清理、WASI target 迁移、L3 生态对齐测验）
- ✅ Week 2（06-30 ~ 07-06）全部完成（cargo audit、backoff/backon、sea-orm 跟踪、pingora 清理、rustls 验证、1.97 脚本）
- ⏳ Week 3（07-07 ~ 07-13）待 2026-07-09 发布日执行（Rust 1.97.0 升级、测试、CHANGELOG 更新）
- ✅ Week 4（07-14 ~ 07-20）1.98 预览与 L4 形式化工具完成

### P1：内容去重与质量基线

- ✅ 高相似文件合并完成（无 ≥0.90 重复对）
- ✅ `docs/research_notes/` 与 `docs/rust-ownership-decidability/` 元数据头 100% 覆盖
- ✅ C 类目录治理阶段 3 完成、阶段 4 维护规则进行中

### P1：学习体验与测验

- ✅ L3 核心测验 24 个 + 生态对齐测验 12 个，均已集成 CI

### P1：形式化工具与 L4 内容

- ✅ Safety Tags / BorrowSanitizer / AutoVerus / Tree Borrows / Kani 0.66 概念页创建完成

### P2：编译器/Cargo 深度内容

- ✅ 17 个规划文件已创建并通过质量检查

---

## 七、风险与阻塞项

| 风险 | 影响 | 当前状态 |
|:---|:---|:---|
| Rust 1.97 某特性未如期稳定 | A3.3 无法完成 | 已准备等效实现 / 推迟至 1.98 方案 |
| `cargo audit` 网络拉取不稳定 | A2.1 受阻 | 已使用本地 advisory-db 绕过 |
| Sea-ORM 2.0 stable 延迟 | A2.3 决策受阻 | 维持 `2.0.0-rc.41`，持续跟踪 |
| C-class 文件数量大 | B4.x 进度风险 | 已大幅归档，C 类问题从 676 降至 228 |
| 链接损坏 1,917 条 | 文档体验 | 多为历史 / 外部链接，不影响核心 A/B 类内容 |

---

## 八、当前工作区改动

### 已修改文件（11）

1. `.cargo/audit.toml` — 添加 3 个 `unmaintained` 依赖的 ignore 与 rationale
2. `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` — 同步 cargo audit 与 docs 审计结果
3. `CHANGELOG.md` — 记录 cargo audit 收尾与 cargo update 版本刷新
4. `Cargo.lock` — `cargo update` 自动更新
5. `Cargo.toml` — 更新 `uuid`、`wasm-bindgen`、`js-sys`、`wasm-bindgen-futures` 版本与注释
6. `crates/c10_networks/Cargo.toml` — 移除 `postcard` dev-dependency
7. `crates/c10_networks/benches/network_benchmarks.rs` — 移除 postcard 相关代码并添加注释
8. `crates/c12_wasm/Cargo.toml` — 更新 `web-sys` 至 0.3.103
9. `docs/LINK_CHECK_REPORT.md` — 链接检查脚本自动生成
10. `reports/CARGO_AUDIT_2026_06_25.md` — 更新 audit 报告
11. `reports/SUPPLY_CHAIN_AUDIT_2026_06_25.md` — 更新供应链审计报告

### 未跟踪文件（1）

1. `reports/LINK_CHECK_2026_06_25.md` — 本次链接检查摘要

---

## 九、后续建议

1. **2026-07-09 发布日**：执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`，升级 toolchain、激活 `rust_197_features.rs`、跑 `cargo test --workspace`。
2. **每周例行**：运行 `cargo audit`（本地 db 兜底）与 `scripts/docs_value_audit.py docs --days-old 90`。
3. **链接修复**：对 1,917 条损坏链接分批处理，优先修复 A/B 类核心文档内部断链。
4. **上游跟踪**：
   - `cortex-m` 0.8 发布 → 移除 `bare-metal` 忽略
   - `glommio` 升级 `futures-lite` 2.x → 移除 `instant` 忽略
   - `candle-core` / `libp2p` 迁移出 `paste` → 移除 `paste` 忽略
5. **提交当前改动**：`git add` 后提交，避免工作区长期堆积自动生成的报告文件。

---

*本报告由 `reports/PROJECT_COMPREHENSIVE_STATUS_2026_06_25.md` 自动生成。*
