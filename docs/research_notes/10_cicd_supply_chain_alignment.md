# CI/CD 与供应链安全权威来源对齐矩阵 {#cicd-与供应链安全权威来源对齐矩阵}

> **EN**: Cicd Supply Chain Alignment
> **Summary**: CI/CD 与供应链安全权威来源对齐矩阵 Cicd Supply Chain Alignment.
> **概念族**: 权威来源对齐 / CI/CD / 供应链安全
> **内容分级**: [核心级]
> **层级**: L0-L4
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [CI/CD 与供应链安全权威来源对齐矩阵 {#cicd-与供应链安全权威来源对齐矩阵}](#cicd-与供应链安全权威来源对齐矩阵-cicd-与供应链安全权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、CI/CD 流水线 {#二cicd-流水线}](#二cicd-流水线-二cicd-流水线)
    - [2.1 GitHub Actions {#21-github-actions}](#21-github-actions-21-github-actions)
    - [2.2 GitLab CI {#22-gitlab-ci}](#22-gitlab-ci-22-gitlab-ci)
    - [2.3 cargo-make {#23-cargo-make}](#23-cargo-make-23-cargo-make)
    - [2.4 release-plz {#24-release-plz}](#24-release-plz-24-release-plz)
    - [2.5 cargo-dist {#25-cargo-dist}](#25-cargo-dist-25-cargo-dist)
  - [三、测试与质量 {#三测试与质量}](#三测试与质量-三测试与质量)
    - [3.1 codecov {#31-codecov}](#31-codecov-31-codecov)
    - [3.2 cargo-tarpaulin {#32-cargo-tarpaulin}](#32-cargo-tarpaulin-32-cargo-tarpaulin)
    - [3.3 nextest {#33-nextest}](#33-nextest-33-nextest)
    - [3.4 cargo-llvm-cov {#34-cargo-llvm-cov}](#34-cargo-llvm-cov-34-cargo-llvm-cov)
  - [四、供应链安全 {#四供应链安全}](#四供应链安全-四供应链安全)
    - [4.1 cargo-audit {#41-cargo-audit}](#41-cargo-audit-41-cargo-audit)
    - [4.2 cargo-deny {#42-cargo-deny}](#42-cargo-deny-42-cargo-deny)
    - [4.3 cargo-vet {#43-cargo-vet}](#43-cargo-vet-43-cargo-vet)
    - [4.4 Sigstore {#44-sigstore}](#44-sigstore-44-sigstore)
    - [4.5 SLSA {#45-slsa}](#45-slsa-45-slsa)
    - [4.6 SBOM {#46-sbom}](#46-sbom-46-sbom)
  - [五、发布与签名 {#五发布与签名}](#五发布与签名-五发布与签名)
    - [5.1 crates.io 政策与 token {#51-cratesio-政策与-token}](#51-cratesio-政策与-token-51-cratesio-政策与-token)
    - [5.2 GitHub Releases {#52-github-releases}](#52-github-releases-52-github-releases)
    - [5.3 Attestation / Provenance {#53-attestation-provenance}](#53-attestation--provenance-53-attestation-provenance)
  - [六、项目文档映射 {#六项目文档映射}](#六项目文档映射-六项目文档映射)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 及项目代码库中的 CI/CD、测试质量、供应链安全、发布签名内容与国际化权威来源建立映射，确保：

- CI/CD 配置可追溯至 [GitHub Actions](https://docs.github.com/en/actions)、[GitLab CI](https://docs.gitlab.com/ee/ci/) 官方文档及 Rust 社区发布工具文档。
- 测试覆盖率与质量工具（codecov、tarpaulin、nextest、cargo-llvm-cov）与项目工作流对齐。
- 供应链安全实践（cargo-audit、cargo-deny、cargo-vet、Sigstore、SLSA、SBOM）有权威来源支撑。
- 发布与签名流程（crates.io、GitHub Releases、attestation）与 [Cargo Book](https://doc.rust-lang.org/cargo/)、平台官方文档对齐。

---

## 二、CI/CD 流水线 {#二cicd-流水线}

### 2.1 GitHub Actions {#21-github-actions}

| 权威来源/主题 | 项目工作流 | 状态 | 备注 |
|---------------|------------|------|------|
| [GitHub Actions 官方文档](https://docs.github.com/en/actions) | [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) | ✅ | fmt / clippy / build / test / docs |
| [Workflow syntax](https://docs.github.com/en/actions/using-workflows/workflow-syntax-for-github-actions) | [`.github/workflows/ci_optimized.yml`](../../.github/workflows/ci_optimized.yml) | ✅ | 跨平台矩阵、sccache |
| [Reusable workflows](https://docs.github.com/en/actions/using-workflows/reusing-workflows) | [`.github/workflows/pr_checks.yml`](../../.github/workflows/pr_checks.yml) | ✅ | PR 专属检查 |
| [Scheduled workflows](https://docs.github.com/en/actions/using-workflows/events-that-trigger-workflows#schedule) | [`.github/workflows/weekly_dependency_check.yml`](../../.github/workflows/weekly_dependency_check.yml) | ✅ | 依赖更新与安全检查 |
| [Security hardening](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions) | [`.github/workflows/security_audit.yml`](../../.github/workflows/security_audit.yml) | ✅ | 权限最小化、 artifact 保留策略 |

### 2.2 GitLab CI {#22-gitlab-ci}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [GitLab CI/CD YAML](https://docs.gitlab.com/ee/ci/yaml/) | — | ⏳ | 项目当前以 GitHub Actions 为主，GitLab CI 模板待补充 |
| [Rust GitLab CI templates](https://docs.gitlab.com/ee/ci/examples/rust.html) | — | ⏳ | 可移植的 fmt/clippy/test 模板 |

### 2.3 cargo-make {#23-cargo-make}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [cargo-make Book](https://sagiegurari.github.io/cargo-make/) | — | ⏳ | 复杂任务编排脚本待引入 |
| [Makefile.toml 任务定义](https://sagiegurari.github.io/cargo-make/#task-config-modifiers) | — | ⏳ | 可统一 dev/check/release 命令 |

### 2.4 release-plz {#24-release-plz}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [release-plz 文档](https://release-plz.ienalich.com/) | — | ⏳ | 自动化 changelog / PR / 发布 |
| [release-plz GitHub Action](https://release-plz.ienalich.com/docs/github/) | — | ⏳ | 与 workspace 版本管理结合 |

### 2.5 cargo-dist {#25-cargo-dist}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [cargo-dist Book](https://opensource.axo.dev/cargo-dist/) | — | ⏳ | 跨平台二进制分发、installer |
| [cargo-dist 与 GitHub Releases 集成](https://opensource.axo.dev/cargo-dist/book/ci/github.html) | — | ⏳ | 发布产物与签名流程 |

---

## 三、测试与质量 {#三测试与质量}

### 3.1 codecov {#31-codecov}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [Codecov Docs](https://docs.codecov.com/) | — | ⏳ | 覆盖率趋势与 PR 注释 |
| [codecov/codecov-action](https://github.com/codecov/codecov-action) | — | ⏳ | 与 cargo-llvm-cov / tarpaulin 输出集成 |

### 3.2 cargo-tarpaulin {#32-cargo-tarpaulin}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [cargo-tarpaulin README](https://github.com/tarpaulin/tarpaulin) | — | ⏳ | 代码覆盖率收集 |
| [Tarpaulin config](https://github.com/tarpaulin/tarpaulin?tab=readme-ov-file#config-file) | — | ⏳ | `.tarpaulin.toml` 待创建 |

### 3.3 nextest {#33-nextest}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [nextest Book](https://nexte.st/) | [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) | 🔄 | 当前使用 `cargo test`；nextest 替换可提升速度与重试能力 |
| [nextest profile / retries [已失效]]<!-- 原链接: https://nexte.st/book/ --> | — | ⏳ | flakiness 重试与分区运行 |

### 3.4 cargo-llvm-cov {#34-cargo-llvm-cov}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [cargo-llvm-cov](https://github.com/taiki-e/cargo-llvm-cov) | — | ⏳ | 基于 LLVM profile 的覆盖率 |
| [Integration with Codecov](https://github.com/taiki-e/cargo-llvm-cov#codecov) | — | ⏳ | `lcov` / `cobertura` 输出 |

---

## 四、供应链安全 {#四供应链安全}

### 4.1 cargo-audit {#41-cargo-audit}

| 权威来源/主题 | 项目文档/配置 | 状态 | 备注 |
|---------------|---------------|------|------|
| [cargo-audit / RustSec](https://github.com/rustsec/rustsec) | [`.github/workflows/security_audit.yml`](../../.github/workflows/security_audit.yml) | ✅ | rustsec/audit-check + 详细 JSON/Markdown 报告 |
| [Advisory DB](https://github.com/rustsec/advisory-db) | [`.cargo/audit.toml`](../../.cargo/audit.toml) | ✅ | 忽略项附影响评估与理由 |
| [cargo audit 配置](https://github.com/rustsec/rustsec/blob/main/cargo-audit/README.md) | [`.cargo/audit.toml`](../../.cargo/audit.toml) | ✅ | `[advisories]` 忽略规则 |

### 4.2 cargo-deny {#42-cargo-deny}

| 权威来源/主题 | 项目文档/配置 | 状态 | 备注 |
|---------------|---------------|------|------|
| [cargo-deny Book](https://embarkstudios.github.io/cargo-deny/) | [`.github/workflows/security_audit.yml`](../../.github/workflows/security_audit.yml) | 🔄 | 已运行 advisories/licenses/bans/sources；`deny.toml` 待创建 |
| [Check advisories](https://embarkstudios.github.io/cargo-deny/checks/advisories/index.html) | — | 🔄 | 与 cargo-audit 互补 |
| [Check licenses](https://embarkstudios.github.io/cargo-deny/checks/licenses/index.html) | — | 🔄 | 许可证合规矩阵待补充 |
| [Check bans / sources](https://embarkstudios.github.io/cargo-deny/checks/bans/index.html) | — | 🔄 | 禁用 crate / 限制 registry 来源 |

### 4.3 cargo-vet {#43-cargo-vet}

| 权威来源/主题 | 项目文档/配置 | 状态 | 备注 |
|---------------|---------------|------|------|
| [cargo-vet 文档](https://mozilla.github.io/cargo-vet/) | [`supply-chain/config.toml`](../../supply-chain/config.toml) | ✅ | 已初始化并导入 Mozilla audits |
| [Policy & criteria](https://mozilla.github.io/cargo-vet/config.html) | [`supply-chain/config.toml`](../../supply-chain/config.toml) | ✅ | `safe-to-deploy` / `safe-to-run` / `license` |
| [Imports & audits](https://mozilla.github.io/cargo-vet/performing-audits.html) | `supply-chain/audits.toml` / `imports.lock` | ✅ | 本地 crate 免检策略 |

### 4.4 Sigstore {#44-sigstore}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [Sigstore 文档](https://docs.sigstore.dev/) | — | ⏳ | cosign / gitsign 用于签名发布产物与 Git 提交 |
| [Sigstore Rust 客户端](https://github.com/sigstore/sigstore-rs) | — | ⏳ | 与 crates.io / GitHub Releases 签名集成 |

### 4.5 SLSA {#45-slsa}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [SLSA Specification](https://slsa.dev/spec/v1.0/about) | — | ⏳ | Supply-chain Levels for Software Artifacts |
| [SLSA GitHub Generator](https://github.com/slsa-framework/slsa-github-generator) | — | ⏳ | 达到 SLSA Build L3 的可复用 workflow |

### 4.6 SBOM {#46-sbom}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [SPDX](https://spdx.dev/) | — | ⏳ | `cargo-sbom` / `cargo-cyclonedx` 生成 SPDX |
| [CycloneDX](https://cyclonedx.org/) | — | ⏳ | 依赖与漏洞 SBOM 清单 |
| [NTIA SBOM](https://www.ntia.gov/SBOM) | — | ⏳ | 最小元素与合规要求 |
| [cargo-sbom](https://github.com/psastras/sbom-rs) | — | ⏳ | 从 Cargo.lock 生成 SBOM |

---

## 五、发布与签名 {#五发布与签名}

### 5.1 crates.io 政策与 token {#51-cratesio-政策与-token}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [crates.io policies](https://crates.io/policies) | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | ✅ | 命名、 squatting、 安全披露 |
| [Publishing on crates.io](https://doc.rust-lang.org/cargo/reference/publishing.html) | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) §7 | ✅ | `cargo publish`、metadata、SemVer |
| [API tokens](https://doc.rust-lang.org/cargo/reference/publishing.html#cargo-login) | — | 🔄 | 建议使用 fine-grained token 并存储于 GitHub Secrets |
| [Crates.io 2FA / account security](https://crates.io/settings/tokens) | — | ⏳ | 发布账号安全策略 |

### 5.2 GitHub Releases {#52-github-releases}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [Releasing projects on GitHub](https://docs.github.com/en/repositories/releasing-projects-on-github) | — | ⏳ | release note、tag、asset |
| [Automated release notes](https://docs.github.com/en/repositories/releasing-projects-on-github/automatically-generated-release-notes) | — | ⏳ | 与 release-plz / cargo-dist 结合 |
| [GitHub Release Assets](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases) | — | ⏳ | 二进制、checksum、SBOM |

### 5.3 Attestation / Provenance {#53-attestation-provenance}

| 权威来源/主题 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [GitHub Artifact Attestations](https://docs.github.com/en/actions/security-guides/using-artifact-attestations-to-establish-provenance-for-builds) | — | ⏳ | `actions/attest-build-provenance` |
| [Sigstore provenance](https://docs.sigstore.dev/) | — | ⏳ | 与 SLSA provenance 互补 |
| [SLSA Provenance](https://slsa.dev/spec/v1.0/provenance) | — | ⏳ | 构建来源、依赖、环境 |

---

## 六、项目文档映射 {#六项目文档映射}

| 主题 | 项目内部锚点 | 说明 |
|------|--------------|------|
| Cargo 发布与 SemVer | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | package、workspace、features、发布流程 |
| 工具链与 lint | [10_tools_guide.md](10_tools_guide.md) | rustfmt、clippy、rust-analyzer、cargo-expand |
| 性能与测试 | [10_performance_and_testing_alignment.md](10_performance_and_testing_alignment.md) | Criterion、Miri、Sanitizer、测试策略 |
| 安全/unsafe 权威来源 | [10_safety_and_unsafe_authoritative_alignment.md](10_safety_and_unsafe_authoritative_alignment.md) | unsafe 边界与安全论证 |
| 版本演进 | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) | rust-version、MSRV、Edition |
| CI 工作流目录 | [`.github/workflows/`](../../.github/workflows) | 全部工作流 YAML 文件 |
| cargo-audit 配置 | [`.cargo/audit.toml`](../../.cargo/audit.toml) | 忽略规则与影响评估 |
| cargo-vet 配置 | [`supply-chain/config.toml`](../../supply-chain/config.toml) | 审计标准与策略 |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. **GitLab CI 模板**：项目当前使用 GitHub Actions，缺少可移植的 GitLab CI `.gitlab-ci.yml` 模板。
2. **cargo-make / task runner**：未引入 `Makefile.toml` 统一本地开发、CI、发布命令。
3. **发布自动化**：未配置 `release-plz` 或 `cargo-dist`；发布、changelog、GitHub Release 仍为手工流程。
4. **覆盖率收集**：未在工作流中集成 `cargo-tarpaulin`、`cargo-llvm-cov` 或 codecov。
5. **nextest 迁移**：仍使用 `cargo test`；未利用 nextest 的分区、重试、JUnit 输出能力。
6. **cargo-deny 配置**：工作流已运行 `cargo deny`，但根目录缺少 `deny.toml` 策略文件。
7. **许可证合规矩阵**：未将各 crate 依赖许可证整理为可读矩阵。
8. **Sigstore / SLSA / SBOM**：未配置发布产物签名、SLSA provenance、SBOM 生成。
9. **crates.io token 策略**：未文档化 fine-grained token 使用、轮换与 Secret 管理。
10. **GitHub Artifact Attestations**：未在 CI 中生成构建来源证明。

> **权威来源**: [GitHub Actions Docs](https://docs.github.com/en/actions) | [GitLab CI Docs](https://docs.gitlab.com/ee/ci/) | [Cargo Book](https://doc.rust-lang.org/cargo/) | [RustSec](https://rustsec.org/) | [cargo-deny](https://embarkstudios.github.io/cargo-deny/) | [cargo-vet](https://mozilla.github.io/cargo-vet/) | [Sigstore](https://www.sigstore.dev/) | [SLSA](https://slsa.dev/) | [SPDX](https://spdx.dev/) | [CycloneDX](https://cyclonedx.org/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [Cargo Book 对齐矩阵](10_cargo_book_alignment.md)
- [研究工具使用指南](10_tools_guide.md)
- [性能优化与测试质量权威来源对齐矩阵](10_performance_and_testing_alignment.md)
- [安全与 unsafe 权威来源对齐矩阵](10_safety_and_unsafe_authoritative_alignment.md)
- [版本演进权威来源对齐矩阵](10_version_evolution_alignment.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
