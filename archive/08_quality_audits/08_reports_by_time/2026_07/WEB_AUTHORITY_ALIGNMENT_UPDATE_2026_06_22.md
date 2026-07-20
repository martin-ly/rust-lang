# 网络权威内容对齐更新报告

> **对齐日期**: 2026-06-22
> **对齐范围**: Rust 官方发布、Project Goals 2026、形式化工具生态、Sea-ORM 发布状态
> **策略**: 中文为主 + 关键术语中英双语 + 来源标注英文 URL

---

## 已对齐文件

| 文件 | 对齐内容 | 新增/更新权威来源 |
|:---|:---|:---|
| `concept/07_future/rust_1_97_preview.md` | 标注 beta 1.97.0 分支日期（2026-05-22），补充 releases.rs 来源 | [releases.rs 1.97.0 beta](https://releases.rs/docs/1.97.0/) |
| `concept/07_future/rust_1_98_preview.md` | 补充 Project Goals 子页面链接（Beyond the `&`、BorrowSanitizer、Field Projections） | [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/) 及子目标页 |
| `concept/04_formal/22_safety_tags.md` | 新增 Safety Tags 研究仓库链接；补充 21 个基础标签覆盖 std 96% unsafe API 的进展说明 | [safer-rust/safety-tags](https://github.com/safer-rust/safety-tags) · [RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) |
| `concept/04_formal/23_borrow_sanitizer.md` | 补充 2026 项目目标技术路线（shadow stack、`__rust_retag` intrinsics、LLVM 上游 PR） | [BorrowSanitizer 项目主页](https://borrowsanitizer.com/) · [Project Goal](https://rust-lang.github.io/rust-project-goals/2026/borrowsanitizer.html) |
| `concept/06_ecosystem/47_formal_verification_tools.md` | Kani 0.66 能力补充：Autoharness 派生 `Arbitrary`、loop-modifies、`--prove-safety-only`；统一来源引用 | [Kani Documentation](https://model-checking.github.io/kani/) · [Kani GitHub Releases](https://github.com/model-checking/kani/releases) |
| `reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md` | 记录第三方文章与 crates.io 索引不一致，明确以 crates.io 为准 | `cargo search sea-orm` 返回 `2.0.0-rc.41` |

---

## 权威来源快照

### Rust 发布与路线图

- **Rust 1.96.0** 已稳定（2026-05-28）：`core::range`、assert_matches!、Wasm 链接严格化、CVE-2026-5222/5223 修复。
  - 来源: [Rust Blog](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)
- **Rust 1.97.0** 处于 beta，目标稳定日期 **2026-07-09**，分支日期 2026-05-22。
  - 来源: [releases.rs](https://releases.rs/docs/1.97.0/)
- **Rust Project Goals 2026** 已正式化为年度目标周期，共 66 个 accepted goals。
  - 来源: [RFC #3935](https://github.com/rust-lang/rfcs/pull/3935) · [Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)

### Cargo / 供应链

- **CVE-2026-5222 / CVE-2026-5223**：Cargo 处理恶意 tarball 与 sparse registry URL 的安全问题，已在 Rust 1.96 修复。
  - 来源: [Rust Blog](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/) · [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)
- **RFC #3945**：Cargo workspace 继承 `default-features`。
- **RFC #3923**：Cargo min publish age 机制。
- **RFC #3946**：crates.io username for identity。

### 形式化工具

- **Kani**：0.66（2026-05）引入 quantifiers、autoharness、loop contracts、`--prove-safety-only`。
  - 来源: [Kani Docs](https://model-checking.github.io/kani/) · [Releases](https://github.com/model-checking/kani/releases)
- **BorrowSanitizer**：2026 Project Goal，目标从研究原型转为可用工具。
  - 来源: [borrowsanitizer.com](https://borrowsanitizer.com/) · [Project Goal](https://rust-lang.github.io/rust-project-goals/2026/borrowsanitizer.html)
- **Safety Tags**：RFC #3842 讨论中，研究原型提出 21 个基础标签。
  - 来源: [RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) · [safer-rust/safety-tags](https://github.com/safer-rust/safety-tags)
- **Verus / AutoVerus**：活跃开发中，用于系统级 Rust 代码的功能正确性验证。
  - 来源: [Verus](https://github.com/verus-lang/verusverus/) · [AutoVerus paper](https://doi.org/10.1145/3763174)

### 数据库生态

- **Sea-ORM 2.0**：网络上存在第三方文章称其已于 2026-01 发布，但 crates.io 官方索引截至 2026-06-22 仍为 `2.0.0-rc.41`。
  - 来源: `cargo search sea-orm` · [Sea-ORM GitHub Releases](https://github.com/SeaQL/sea-orm/releases)

---

## 待继续对齐项

1. **2026-07-09 Rust 1.97.0 发布日**：执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`，激活 `rust_197_features.rs`，迁移 `rust_1_97_preview.md` 为稳定文档。
2. **形式化工具页**：Kani 示例待转为可编译/可验证形式；Verus、Prusti、Creusot 链接待按最新文档校验。
3. **knowledge/ 核心文件**：108 个文件仍缺少「模块 8: 国际化对齐」，需批量补充官方 + 学术 + 社区来源。
4. **C-class 元数据头**：继续推进 `docs/research_notes/` 与 `docs/rust-ownership-decidability/` 的元数据标准化。
5. **供应链安全**：`cargo audit` 仍受网络阻塞，继续使用 `scripts/supply_chain_audit.py` fallback；等待 `cargo-vet` Windows 兼容修复。

---

## 验证

- `cargo check --workspace` ✅
- `cargo test --test l3_ecosystem_alignment` ✅ 12 passed
- `cargo test -p c02_type_system --lib` ✅ 192 passed
- `cargo clippy -p c02_type_system -- -D warnings` ✅
- `cargo clippy -p exercises --tests -- -D warnings` ✅
