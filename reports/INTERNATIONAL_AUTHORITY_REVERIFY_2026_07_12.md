# 国际化权威对齐深化复核报告（2026-07-12）

**EN**: International Authority Re-verification Report
**Summary**: 继 2026-07-12 缺口闭合（35 页）后同日复核：权威覆盖门 any=100%/none=0/core_gaps=0 未退化（exit 0）；concept/ 1133 条国际权威外链并发复测，真实失效 2 条（NXDOMAIN）已修复并验证 200；Rust 1.97 release notes 逐条比对无缺口，1.98 周期补入 4 条新合并 RFC，学术层补入 3 篇 2026 新刊论文（均 curl 实测 200）。

> 生成: 2026-07-12 · 前置基线: `reports/INTERNATIONAL_AUTHORITY_GAP_CLOSURE_2026_07_12.md`、`reports/EXTERNAL_LINK_RESTORATION_2026_07_12.md`
> 复核脚本: `python scripts/check_concept_authority_coverage.py --strict` → exit 0；`python scripts/kb_auditor.py` → 死链 0；`mdbook build` → 通过

---

## 1. 覆盖门复跑（任务 1.1）

| 维度 | 07-12 上午（闭合后） | 本轮复跑 | 判定 |
|:---|---:|---:|:---:|
| 内容页 P0 官方 | 100.0% | 100.0% | ✅ 未退化 |
| 内容页 P1 学术 | 100.0% | 100.0% | ✅ 未退化 |
| 内容页 P2 社区 | 100.0% | 99.7% | ✅ 门阈内 |
| 任一权威 any | 100.0% | **100.0%** | ✅ 未退化 |
| none | 0 | **0** | ✅ 未退化 |
| 核心 L1–L4 无 P0 缺口 | 0 | **0** | ✅ 未退化 |
| `--strict` exit | 0 | **0** | ✅ |

证据：`reports/CONCEPT_AUTHORITY_COVERAGE_2026-07-12.{md,json}`（本轮复跑覆盖更新）。

---

## 2. 权威外链存活复测（任务 1.2）

### 2.1 范围与方法

- 范围：`concept/` 内指向国际权威源的全部唯一 URL（rust-lang.org 全系、github.com/rust-lang、arXiv、ACM、Springer、USENIX、IEEE、Rust Foundation、Ferrocene、MPI-SWS 等），共 **1133 条**（`tmp/concept_authority_urls_20260712.txt`）。
- 方法：`curl -L -A Mozilla/5.0 --max-time 15`，并发 10（arXiv 单独并发 2，避免并发限流误报）；原始结果 `tmp/concept_authority_link_check_20260712.txt`。
- 提取伪阳性修正：剔除 autolink 尾缀 `>`（3 条）、inline code 尾缀反引号（1 条）。

### 2.2 统计

| 类别 | 数量 | 处置 |
|:---|---:|:---|
| HTTP 200 存活 | 886 | — |
| 403 反爬豁免 | 36 | 全部 `dl.acm.org`（Cloudflare 反爬，与既有基线一致） |
| 202 反爬豁免 | 5 | 全部 `ieeexplore.ieee.org`（反爬，既有基线豁免规则） |
| 000 区域网络豁免 | 199 | `github.com` Web UI 在本环境被 SNI 阻断（`api.github.com`、`raw.githubusercontent.com` 均 200，证域存活）；其中 40 个目标（repo/issue/PR）经 GitHub API 抽样：**39×200 + 1×301**（keyword-generics-initiative 仓库迁移，浏览器跟随重定向仍可达） |
| 000 瞬时/区域豁免 | 4 | 3× arXiv（并发复测 000，逐条 FetchURL 取得正文确认存活：2605.07788、quant-ph/9508027、html/2602.10527v2）+ 1× `gitlab.mpi-sws.org`（DoH 解析正常 A=139.19.205.205，连接被区域网络阻断；同项目官方页 plv.mpi-sws.org/refinedrust/ 200） |
| 404 非死链豁免 | 1 | `dev-static.rust-lang.org/rustup` 裸根 404 系 rustup 服务端点根（`/rustup/release-stable.toml` 实测 200），文中为 `RUSTUP_UPDATE_ROOT` 环境变量值，非网页链接 |
| **真实失效（NXDOMAIN）** | **2** | **已修复**，替代链接 curl 实测 200（见 2.3） |

### 2.3 真实失效修复明细

判定证据：阿里 DoH（223.5.5.5）查询两域名均返回 **Status 3 NXDOMAIN**（非网络问题，域名已注销）。

| # | 文件 | 失效 URL | 替代链接（curl 实测） |
|--:|:---|:---|:---|
| 1 | `concept/07_future/03_preview_features/21_rust_specification_preview.md` | `spec.rust-lang.org/`（NXDOMAIN） | [RFC 3355 — The Rust Specification](https://rust-lang.github.io/rfcs/3355-rust-spec.html)（200；规范工作官方入口） |
| 2 | `concept/06_ecosystem/07_security_and_cryptography/01_security_practices.md` | `secure-code-guidelines.rust-lang.org/`（NXDOMAIN） | [ANSSI — Secure Rust Guidelines](https://anssi-fr.github.io/rust-guide/)（200；法国网安局安全编码指南，语义匹配引用主张） |

---

## 3. 新增内容缺口扫描与处置（任务 2）

### 3.1 Rust 1.97.0 release notes 逐条比对 —— 无缺口

对照来源：官方 blog（2026-07-09，FetchURL 全文）+ draft release notes（rust-lang/rust#158353，FetchURL 全文）逐条比对 `concept/07_future/00_version_tracking/rust_1_97_stabilized.md`：

| 官方条目类别 | 条数 | 覆盖位置 | 判定 |
|:---|---:|:---|:---:|
| Language（`{float}`→f32 回退、must_use 扩展、5 个 target feature、`cfg(target_has_atomic_primitive_alignment)`、trailing `self`） | 5 | §2.1–2.6 | ✅ |
| Compiler（v0 mangling 默认） | 1 | §2.7 | ✅ |
| Platform（NVPTX 基线提升） | 1 | §3.1 | ✅ |
| Stabilized APIs + const 化 | 14 | §4.1–4.6 | ✅ |
| Cargo（build.warnings、lockfile-path、clean 校验、`-m`、curl 依赖移除） | 5 | §5.1–5.5 | ✅ |
| Rustdoc（`--emit`、`--remap-path-prefix`） | 2 | §6.1–6.2 | ✅ |
| Compatibility Notes（pin! deref、char 弃用、linker_messages、f64 隐藏方法、varargs、模块路径泛型、macho link_section、enum 编码、空 export_name、元组索引简写、link_name 校验、WSAESHUTDOWN、dead_code_pub_in_binary） | 14 | §7 表格 + §7.1/7.2 | ✅ |

**结论：0 缺口，无需改动。**

### 3.2 Rust 1.98 nightly 新合并 RFC —— 补入 4 条 + 修正 3 处过时状态

核查方法：GitHub API `search/issues?q=repo:rust-lang/rfcs+is:pr+is:merged+merged:>2026-05-25` → 10 条，剔除 CI/依赖类 6 条，内容 RFC 4 条；渲染页均 curl 实测 200。

| RFC | 合并日 | 处置 |
|:---|:---|:---|
| #3955 Named `Fn` trait parameters | 2026-07-08 | 补入 `rust_1_98_preview.md` 新增 §1.7；`01_rust_version_tracking.md:1481` 状态由「FCP 中」改为「2026-07-08 已合并」并换链接为 RFC Book 页 |
| #3928 todo-overreach（`todo!()` 免 `unreachable_code`） | 2026-06-25 | 补入 §1.7 |
| #3808 `#![register_{attribute,lint}_tool]` | 2026-06-10 | 补入 §1.7；`06_data_and_distributed/01_application_domains.md:387` 状态由「FCP 中」改为「已合并（2026-06-10）」 |
| #3946 crates.io username identity | 2026-05-26 | 补入 §1.7 |

附带修正：`03_safety_tags_preview.md` 状态表「RFC 草案 🔴 尚未提交」与正文 RFC #3842 矛盾，改为「🟡 已提交（PR #3842，open 未合并）」。

未合并高关注提案（Safety Tags #3842、Scalable Vectors #3838、`extern "custom"`）在 §1.7 注记，维持跟踪态。

### 3.3 2026 国际动态 —— 无缺口（核查证据）

| 核查项 | 查询词 | 结果摘要 | 覆盖判定 |
|:---|:---|:---|:---|
| Rust Foundation 公告 | "Rust Foundation announcement July 2026" | OpenAI Platinum + $600k 捐赠（6-17）、Maintainers Fund 启动（RFC#3931，6-2）、Rust Commercial Network（6-25）、Trusted Training Program、Canonical Gold | ✅ `01_rust_version_tracking.md` Batch 28/29 已覆盖 |
| Ferrocene 新认证 | "Ferrocene certification 2026 ISO 26262 IEC 61508" | Ferrocene 26.02.0（2026-03）：core 认证函数 2,903→5,169，ISO 26262 ASIL B + IEC 61508 SIL 2 core 子集 | ✅ version_tracking §12.x（v1.7 起）+ `04_formal/04_model_checking/03_aerospace_certification_formal_methods.md` 已覆盖 |
| Project Goals 2026 | "Rust Project Goals 2026H2 flagship" | 2026 全年期目标册（7 旗舰主题、稳定化清单）；2025H2 收官更新（2026-05-18） | ✅ version_tracking「2026 Project Goals 目录与旗舰主题」「Project Goals 2025H2 收官」已覆盖；`rust_1_98_preview.md` 头部已链目标册 |
| 重大安全公告 | "RUSTSEC OR CVE-2026 Rust Cargo advisory 2026" | Cargo CVE-2026-5222/5223（5-25）为年内唯一 toolchain 级公告；其余均为 crate 级 RUSTSEC | ✅ 专页 `06_ecosystem/01_cargo/13_cargo_security_cves.md` 已覆盖 |

### 3.4 学术新刊（2025–2026）—— 补入 3 篇（均 curl 实测 200）

| 论文 | 出处 | 补入位置 |
|:---|:---|:---|
| Kani: A Model Checker for Rust（arXiv:2607.01504, 2026-07） | 工具论文 | `06_ecosystem/08_formal_verification/02_formal_verification_tools.md` 权威来源行 |
| Verifying the Rust Standard Library（arXiv:2606.17374, 2026-06） | verify-rust-std 计划综述 | 同上 + `04_formal/04_model_checking/01_verification_toolchain.md`「权威来源索引」（该节原为空占位，一并补全 5 条真实条目） |
| Annotating and Auditing the Safety Properties of Unsafe Rust（arXiv:2504.21312v2, 2026-04） | Safety Tags 标注审计研究 | `07_future/03_preview_features/03_safety_tags_preview.md` 来源表 |

已覆盖无需补：Miri 论文（Jung et al., POPL 2026）——`01_verification_toolchain.md` 与 version_tracking 已收录；Tree Borrows（PLDI 2025）——多页已收录。

---

## 4. 验证结果（机器可复核）

| 检查 | 命令 | 结果 |
|:---|:---|:---|
| 权威覆盖门 | `python scripts/check_concept_authority_coverage.py --strict` | **exit 0**：any=100% none=0 core_gaps=0 |
| 死链审计 | `python scripts/kb_auditor.py` | **死链 0**，跨层问题 0，模板化 ⟹ 0 |
| mdbook 构建 | `mdbook build` | **通过**（exit 0） |
| 新增/替代链接 | curl `-L --max-time 15` 逐条 | RFC Book ×4、arXiv ×3、RFC 3355、ANSSI guide 全部 **200** |

## 5. 改动清单（全部在 `concept/` 内，未执行任何 git 命令）

1. `concept/07_future/03_preview_features/21_rust_specification_preview.md` — 死链替换（spec.rust-lang.org → RFC 3355）
2. `concept/06_ecosystem/07_security_and_cryptography/01_security_practices.md` — 死链替换（secure-code-guidelines → ANSSI）
3. `concept/07_future/00_version_tracking/rust_1_98_preview.md` — 新增 §1.7「新近合并的 RFC」
4. `concept/07_future/00_version_tracking/01_rust_version_tracking.md` — RFC #3955 状态更新
5. `concept/06_ecosystem/06_data_and_distributed/01_application_domains.md` — RFC #3808 状态更新
6. `concept/07_future/03_preview_features/03_safety_tags_preview.md` — 补 arXiv:2504.21312 + RFC 状态修正
7. `concept/06_ecosystem/08_formal_verification/02_formal_verification_tools.md` — 补 2026 新刊 2 篇
8. `concept/04_formal/04_model_checking/01_verification_toolchain.md` — 空「权威来源索引」节补全（含 2026 新刊 2 篇）

---
*证据文件：`tmp/concept_authority_urls_20260712.txt`、`tmp/concept_authority_link_check_20260712.txt`、`reports/CONCEPT_AUTHORITY_COVERAGE_2026-07-12.{md,json}`*
