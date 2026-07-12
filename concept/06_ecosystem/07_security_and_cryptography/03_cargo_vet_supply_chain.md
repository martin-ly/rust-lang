# cargo vet 与供应链审计

> **EN**: cargo vet and Supply-Chain Auditing
> **Summary**: How cargo-vet (Mozilla) turns third-party dependency review into a shared, incremental audit workflow — audits.toml / config.toml / imports.lock mechanics, built-in criteria, importing public audit sets — plus cargo-audit for vulnerability tracking, demonstrated with this repository's own supply-chain/ directory and CI quality gate (`cargo vet --locked`).
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶 / 工程]
> **内容分级**: [专家级]
> **Bloom 层级**: L3-L4
> **权威来源**: 本文件为 `concept/` 中 **cargo vet / 供应链依赖审计机制**的权威页；通用供应链安全实践与 CVE 跟踪见 [Security Practices](01_security_practices.md)。
> **A/S/P 标记**: **A** — Application
> **双维定位**: P×App — 依赖审计机制在 CI 中的落地
> **前置概念**: [Cargo Security CVEs](../01_cargo/13_cargo_security_cves.md) · [Security Practices](01_security_practices.md) · [Cargo Registries and Publishing](../01_cargo/08_cargo_registries_and_publishing.md) · [Safety Boundaries 对比](../../05_comparative/03_domain_comparisons/01_safety_boundaries.md)
> **后置概念**: [认证工具链与认证包清单](../../04_formal/04_model_checking/10_certified_toolchains_and_packages.md) · [DevOps and CI/CD](../00_toolchain/03_devops_and_ci_cd.md)
>
> **来源**: [cargo-vet 官方文档（mozilla.github.io/cargo-vet）](https://mozilla.github.io/cargo-vet/)（2026-07-12 curl 实测） · [cargo-vet — How it Works](https://mozilla.github.io/cargo-vet/how-it-works.html) · [RustSec Advisory DB](https://rustsec.org/)（实测 200） · [cargo-audit](https://github.com/rustsec/rustsec/tree/main/cargo-audit)

---

## 📑 目录

- [cargo vet 与供应链审计](#cargo-vet-与供应链审计)
  - [📑 目录](#-目录)
  - [一、为什么需要 cargo vet](#一为什么需要-cargo-vet)
  - [二、cargo vet 的工作模型](#二cargo-vet-的工作模型)
    - [2.1 三个文件](#21-三个文件)
    - [2.2 内置审计标准（criteria）](#22-内置审计标准criteria)
    - [2.3 导入公共审计集](#23-导入公共审计集)
    - [2.4 豁免（exemptions）与收敛](#24-豁免exemptions与收敛)
  - [三、cargo audit：漏洞跟踪的另一条腿](#三cargo-audit漏洞跟踪的另一条腿)
  - [四、本项目实例：supply-chain/ 与质量门 5](#四本项目实例supply-chain-与质量门-5)
    - [4.1 目录实况](#41-目录实况)
    - [4.2 审计条目的写法](#42-审计条目的写法)
    - [4.3 质量门 5 的语义](#43-质量门-5-的语义)
  - [五、cargo vet vs cargo audit vs 功能安全认证](#五cargo-vet-vs-cargo-audit-vs-功能安全认证)
  - [六、落地步骤](#六落地步骤)
  - [七、权威来源索引](#七权威来源索引)
  - [相关概念](#相关概念)

---

## 一、为什么需要 cargo vet

cargo-vet 由 Mozilla 开发，其官方文档开宗明义：大多数开发者精力有限，因此 cargo-vet 的驱动原则是**把"做正确的事"的摩擦降到最小**——初始化近乎零成本、融入既有工作流、逐步引导，并让整个生态**共享对广泛使用 crate 的审计劳动**。

它回答的问题不是"依赖有没有已知漏洞"（那是 cargo audit），而是：**这个依赖的这份代码，有没有被你信任的人按你声明的标准审查过？** 每次 `cargo update` 引入新版本时，只需审计增量（delta），而非全量重审。

---

## 二、cargo vet 的工作模型

### 2.1 三个文件

cargo vet 的全部状态存放在仓库的 `supply-chain/` 目录：

| 文件 | 内容 | 提交策略 |
|:---|:---|:---|
| `config.toml` | 审计策略：每个一方包的 `policy`（所需 criteria）、`imports`（信任的外部审计源）、未审计依赖的 `exemptions` | 提交，评审重点 |
| `audits.toml` | 本仓库完成的审计记录：谁、按什么标准、审了哪个版本或 delta、备注 | 提交，持续追加 |
| `imports.lock` | 导入的外部审计集快照（锁定到具体条目），保证可重现 | 提交，由 `cargo vet` 维护 |

### 2.2 内置审计标准（criteria）

cargo vet 内置两级可直接使用的标准，也支持自定义：

| criteria | 含义 |
|:---|:---|
| `safe-to-deploy` | 代码不会引入严重安全漏洞（内存安全 UB、恶意行为、不安全的 crypto 误用等），可进入生产 |
| `safe-to-run` | 代码可以执行（构建/测试工具、开发依赖），不做部署级安全保证 |

审计粒度是**版本或 delta**（`0.3.31 -> 0.3.32`）：delta 审计只读变更部分，是增量模型的核心。

### 2.3 导入公共审计集

`config.toml` 的 `[imports.<name>]` 声明信任的外部审计源（URL 指向对方的 `audits.toml`）。主流公开审计集包括 Mozilla、Google、Bytecode Alliance 等组织的仓库。导入后：

- 被外部源按**不低于**你要求的标准审计过的依赖，自动满足，无需本地重审；
- `imports.lock` 固化导入快照，`--locked` 模式下不因上游审计集变化而漂移；
- 审计因此具备**网络效应**：一个组织的审计劳动可被全生态复用。

### 2.4 豁免（exemptions）与收敛

初始化时（`cargo vet init`），所有未审计依赖进入 `config.toml` 的 `exemptions` 清单——这是"先让 CI 变绿，再逐步消化"的机制。每个 exemption 都是**显式的技术债务条目**：消除它的方式只有两种——完成本地审计写入 `audits.toml`，或升级/替换依赖使其被导入审计集覆盖。`exemptions` 可附带过期版本上限，防止无限期豁免。

---

## 三、cargo audit：漏洞跟踪的另一条腿

`cargo audit`（RustSec 维护）查询 [RustSec Advisory DB](https://rustsec.org/)，报告依赖树中的**已知漏洞、安全警告与未维护 crate**：

| 维度 | cargo vet | cargo audit |
|:---|:---|:---|
| 回答 | 这段代码被按标准审查过吗？ | 这个版本有已知安全公告吗？ |
| 数据源 | 仓库内 `supply-chain/` + 导入审计集 | RustSec Advisory DB（在线/本地镜像） |
| 触发时机 | 依赖变更（新增/升级） | 新公告发布、依赖变更 |
| 失效模式 | 未审计即 CI 失败 | 命中公告即 CI 失败 |

两者互补而非替代：vet 防"没人看过"，audit 防"看过后才发现问题"。`cargo audit --no-fetch` 使用本地数据库副本，适合离线 CI。

---

## 四、本项目实例：supply-chain/ 与质量门 5

本仓库自身就是 cargo vet 的生产用例（以下数据 2026-07-12 实测）。

### 4.1 目录实况

```text
supply-chain/
├── config.toml     # cargo-vet 0.10；导入 ariel-os、google 两个公共审计集
├── audits.toml     # 16 条本地审计（[[audits.<crate>]] 计数实测）
└── imports.lock    # 84 条导入审计快照（[[audits.*]] 计数实测）
```

`config.toml` 的导入声明（实测片段）：

```toml
[cargo-vet]
version = "0.10"

[imports.ariel-os]
url = "https://raw.githubusercontent.com/ariel-os/ariel-os/main/supply-chain/audits.toml"

[imports.google]
url = "https://raw.githubusercontent.com/google/supply-chain/main/audits.toml"
```

并为每个一方 crate（`c01_ownership_borrow_scope` 等）声明 `policy`（`audit-as-crates-io = false`）。

### 4.2 审计条目的写法

`audits.toml` 中的真实条目模式——每条记录都写明**为什么这个标准足够**：

```toml
[[audits.cc]]
criteria = "safe-to-run"
version = "1.2.67"
notes = "2026-07-11: cc 1.2.67 (rust-lang/cc-rs 官方维护) 为构建脚本通用 C 编译驱动，仅构建期执行。"
```

对"残留但未实际参与编译"的依赖，审计备注会记录范围限定理由（例如某 crate 仅在 `target_arch = "arm"` 时由嵌入式 crate 拉入、宿主机构建图不含），把审计结论与构建图事实绑定——这是审计可辩护性的关键。

### 4.3 质量门 5 的语义

`scripts/run_quality_gates.sh` 中两条相邻的阻断门（实测片段）：

```bash
run_gate "Cargo Audit" cargo audit --no-fetch   # 门 4：已知漏洞
run_gate "Cargo Vet"   cargo vet --locked        # 门 5：审计覆盖
```

`--locked` 的含义：`imports.lock` 与 `Cargo.lock` 必须被严格遵守，CI 上任何"依赖变化但审计状态未更新"的情况直接失败。这把"依赖审计"从自觉行为变成了**与编译、测试同级的合并门禁**——正是 AGENTS.md §5.1 质量门体系中供应链安全的落点。

---

## 五、cargo vet vs cargo audit vs 功能安全认证

| 维度 | cargo vet | cargo audit | 功能安全认证（Ferrocene core 等） |
|:---|:---|:---|:---|
| 保证类型 | 代码审查覆盖（流程证据） | 已知漏洞排除（公告匹配） | 标准符合性（ISO 26262/IEC 61508 等） |
| 证据形式 | 审计记录 + 共享审计集 | Advisory DB 命中报告 | 认证证书 + Qualification Report |
| 适用 | 一切 Rust 项目的依赖卫生 | 一切 Rust 项目的漏洞响应 | 安全关键系统的受监管交付 |
| 局限 | 不证明无漏洞 | 不覆盖未报告问题 | 不覆盖 crates.io 生态 |

> **边界要点**：cargo vet 的审计**不是**功能安全认证。安全关键项目可同时使用 vet（依赖卫生）与认证工具链（编译器/core 证据），但 vet 审计记录不能替代 SEooC 证据包——两者关系见 [认证工具链与认证包清单](../../04_formal/04_model_checking/10_certified_toolchains_and_packages.md) §4.3。

---

## 六、落地步骤

```bash
# 1. 安装
cargo install cargo-vet cargo-audit --locked

# 2. 初始化（生成 supply-chain/，现存依赖进入 exemptions）
cargo vet init

# 3. 接入公共审计集（编辑 supply-chain/config.toml 的 [imports.*]）
cargo vet              # 首次导入会生成 imports.lock

# 4. 逐步消化 exemptions
cargo vet suggest      # 查看按"最小审计成本"排序的建议
cargo vet diff <crate> <from> <to>   # 查看 delta
# 完成审查后写入 audits.toml（cargo vet certify <crate> <version>）

# 5. CI 门禁
cargo vet --locked
cargo audit --no-fetch
```

---

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [cargo-vet 官方文档](https://mozilla.github.io/cargo-vet/) | ✅ 一级 | Mozilla 维护，机制与教程（2026-07-12 实测） |
| [cargo-vet — How it Works](https://mozilla.github.io/cargo-vet/how-it-works.html) | ✅ 一级 | 设计原则与操作模型 |
| [cargo-vet — Configuration Reference](https://mozilla.github.io/cargo-vet/config.html) · [Built-in Criteria](https://mozilla.github.io/cargo-vet/built-in-criteria.html) | ✅ 一级 | config/audits 字段与内置标准参考（实测 200） |
| [RustSec Advisory DB](https://rustsec.org/) | ✅ 一级 | 公告数据库（实测 200） |
| [cargo-audit](https://github.com/rustsec/rustsec/tree/main/cargo-audit) | ✅ 一级 | 漏洞扫描工具 |

---

## 相关概念

- [对应测验](../13_quizzes/03_quiz_security_testing.md) — 安全与测试生态（Kerckhoffs 原则、crypto 原语、cargo vet/audit、分层测试）
- [Security Practices](01_security_practices.md) — 通用供应链安全与 CVE 跟踪（CVE 公告的权威页）
- [Cargo Security CVEs](../01_cargo/13_cargo_security_cves.md) — Cargo 自身 CVE 史
- [认证工具链与认证包清单](../../04_formal/04_model_checking/10_certified_toolchains_and_packages.md) — 功能安全认证生态
- [DevOps and CI/CD](../00_toolchain/03_devops_and_ci_cd.md) — CI 门禁体系
- [Cargo Registries and Publishing](../01_cargo/08_cargo_registries_and_publishing.md) — registry 信任模型
