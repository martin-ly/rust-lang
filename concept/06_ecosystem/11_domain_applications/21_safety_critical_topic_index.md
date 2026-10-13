# 安全关键 Rust 专题索引

> **EN**: Safety-Critical Rust Topic Index
> **Summary**: Navigation index linking the `content/safety_critical/` in-depth suite (ISO 26262 / IEC 61508 / DO-178C / MISRA guides, case studies, checklists) with the related `concept/` canonical pages (formal methods, Ferrocene toolchain).
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L6
> **定位**:
>
> 本文件为 `concept/` 侧的**摘要+链接型导航页**（AGENTS.md §2.1 第 3 条：content/ 专题权威页需在 concept/ 建索引入口）。
> 专题深度内容以 [`content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md`](../../../content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md) 为权威入口；通用概念解释以 `concept/` 相关权威页为准。本页不复制任何正文。
> **国际权威来源（2026-07-13 补录）**:
>
> **P0** [Ferrocene Language Specification](https://spec.ferrocene.dev/)（curl 200 实测 2026-07-13） ·
> **P1** [Rockwell Collins — Field Guidance System 形式化方法案例（DO-333 实践, arXiv:1409.7643）](https://arxiv.org/abs/1409.7643)（curl 200 实测） ·
> **P2** [Rust Blog — Announcing Rust 1.97.0](https://blog.rust-lang.org/2026/07/09/Rust-1.97.0/)（生态官方发布信息，curl 200 实测）
> **前置概念**:
>
> [Formal Verification Tools](../../04_formal/04_model_checking/01_verification_toolchain.md) ·
> [Ferrocene Preview](../../07_future/02_preview_features/12_ferrocene_preview.md)
> **后置概念**:
> [AUTOSAR and Rust](22_autosar_and_rust.md) ·
> [Safety-Critical Ecosystem Master Index](../../../content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md)
>
>
> **受众**: [进阶]
> **内容分级**: [综述级]

---

## 1. 专题套件入口（content/ 权威）

| 入口 | 内容 |
|:---|:---|
| [主索引](../../../content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md) | 39 篇文档、10 大分类、按角色/阶段的使用路线 |
| [ISO 26262 实施指南](../../../content/safety_critical/10_standards/03_iso_26262_rust_implementation_guide.md) | 汽车功能安全合规路径 |
| [IEC 61508 实施指南](../../../content/safety_critical/10_standards/02_iec_61508_rust_implementation_guide.md) | 工业功能安全合规路径 |
| [DO-178C 合规路径](../../../content/safety_critical/10_standards/01_do_178c_rust_compliance_pathway.md) | 航空软件认证 |
| [MISRA C:2025 Addendum 6 指南](../../../content/safety_critical/10_standards/04_misra_c_2025_addendum_6_guide.md) | MISRA 与 Rust 映射 |
| [案例研究：Ferrocene 认证](../../../content/safety_critical/07_case_studies/01_case_study_01_ferrocene_certification.md) | TÜV 认证工具链实践 |
| [案例研究：汽车 ECU](../../../content/safety_critical/07_case_studies/03_case_study_03_automotive_ecus.md) | ISO 26262 落地案例 |
| [案例研究：NASA CFS Rust](../../../content/safety_critical/07_case_studies/02_case_study_02_nasa_cfs_rust.md) | 航天核心飞行软件（cFS）Rust 重写 |
| [案例研究：医疗设备](../../../content/safety_critical/07_case_studies/04_case_study_04_medical_devices.md) | IEC 62304 / FDA 路径 |
| [案例研究：铁路信号](../../../content/safety_critical/07_case_studies/05_case_study_05_railway_signaling.md) | EN 50128 / SIL 4 场景 |
| [监管格局与审批](../../../content/safety_critical/10_standards/05_regulatory_landscape_and_approvals.md) | 各监管域审批实践 |
| [SIL 选择指南](../../../content/safety_critical/03_decision_trees/02_safety_integrity_level_selection_guide.md) | 完整性等级选择决策树 |

## 2. 相关 concept/ 权威页

| 页面 | 主题 |
|:---|:---|
| [航空航天认证与形式化方法](../../04_formal/04_model_checking/03_aerospace_certification_formal_methods.md) | DO-178C/DO-333 与 Rust 形式化映射（定理证明/模型检查/抽象解释） |
| [Ferrocene：已交付认证工具链](../../07_future/02_preview_features/12_ferrocene_preview.md) | TÜV SÜD 鉴定工具链（ASIL D/SIL 3/Class C）与 certified core 子集 |
| [认证工具链与认证包清单](../../04_formal/04_model_checking/10_certified_toolchains_and_packages.md) | Ferrocene/HighTec/AdaCore 生态、认证 crate 现状与边界决策树 |
| [AUTOSAR 与 Rust](22_autosar_and_rust.md) | AUTOSAR CP/AP 标准与 Rust 的关系、WG-SAF 进程 |
| [MC/DC 覆盖率预研](../../07_future/02_preview_features/02_mcdc_coverage_preview.md) | DO-178C A 级覆盖率准则 |
| [Safety Tags 预研](../../07_future/02_preview_features/03_safety_tags_preview.md) | 安全标注机制 |
| [形式化验证工具链](../../04_formal/04_model_checking/01_verification_toolchain.md) | 验证工具全景 |
| [安全关键系统工程](23_safety_critical_systems_engineering.md) | 安全关键系统工程标准矩阵、Rust 资格鉴定与形式方法集成 |

## 3. 分工边界

- **概念解释**（什么是 DO-178C、形式化方法如何映射 Rust、Ferrocene 是什么）：以上 `concept/` 权威页。
- **工程实践**（合规步骤、检查表、模板、培训、ROI、案例）：`content/safety_critical/` 专题套件。
- 两侧仅通过链接互引，不保留重复正文（AGENTS.md §2 Canonical 规则）。

## 4. 安全关键标准 × Rust 认证路径属性矩阵

| 标准 | 适用域 | 完整性等级 | 对语言/工具链的核心要求 | Rust 现状（2026-07） | 权威源 |
|:---|:---|:---|:---|:---|:---|
| DO-178C（+DO-330/331/332/333） | 航空机载软件 | DAL A–E（A 最严） | A 级要求语句/判定/MC/DC 覆盖；DO-330 工具鉴定（TQL-1..5）；DO-333 允许形式化方法替代部分测试 | rustc 上游本身无鉴定；Ferrocene 编译器获 TÜV SÜD 鉴定（DAL C 级工具，ASIL D/SIL 3 同报告）；Kani/Prusti 可作 DO-333 补充证据 | [RTCA 出版物商店](https://my.rtca.org/nc__store)（curl 200 实测 2026-10-14） · [Ferrocene 鉴定报告](https://public-docs.ferrocene.dev/main/qualification/report/index.html)（curl 200 实测） |
| ISO 26262（Part 6 软件单元） | 道路车辆功能安全 | QM / ASIL A–D | ASIL C/D 要求工具鉴定（Part 8 Clause 11）、单元验证、freedom from interference 论证 | Ferrocene 报告覆盖 ASIL D 工具鉴定；`Send`/`Sync` 类型系统支撑干扰自由论证；Safety-Critical Rust Consortium 编码指南面向汽车 | [ISO 26262-6:2018](https://www.iso.org/standard/68383.html)（ISO 官方页，反爬 403 需浏览器访问） · [Safety-Critical Rust Consortium](https://rustfoundation.org/safety-critical-rust-consortium/)（curl 200 实测） |
| IEC 61508（功能安全基础标准） | 工业 E/E/PE 通用（过程/机械/铁路母标准） | SIL 1–4 | 软件框架（Part 3 Clause 7）限制语言特性；工具需 T3/T2 分类；B.2 对 C 的限制可类比映射 Rust | 无 rustc 级 SIL 认证；Ferrocene 鉴定报告覆盖 SIL 3；`#![forbid(unsafe_code)]` 可机械执行"禁用语言子集"类要求 | [IEC 61508 webstore 条目](https://webstore.iec.ch/publication/66912)（curl 200 实测 2026-10-14） |
| EN 50128:2011+A2:2020（= IEC 62279） | 铁路控制与保护系统 | SIL 0–4（SIL4 最严） | 8.2 语言与编译限制；9.x 工具分类与鉴定；对第三方库/OS 组件的复用论证 | 无官方 Rust 鉴定；Ferrocene 报告覆盖 SIL 3；铁路案例（ETCS 联锁试验）走"safe subset + 工具鉴定"路线 | [IEC 62279:2015 webstore 条目](https://webstore.iec.ch/en/publication/22781)（curl 200 实测 2026-10-14） · [CENELEC（EN 50128 归口）](https://www.cenelec.eu/)（curl 200 实测） |
| MISRA C:2025 Addendum 6 | 跨行业编码指南（汽车/铁路/航空均引用） | 非独立标准，随宿主标准 | Addendum 6 给出 MISRA 规则到 Rust 的映射与偏离管理 | 映射指南已发布；`#![deny(...)]` lint 集可把多数 MISRA 规则转为编译期强制 | [MISRA C:2025 Addendum 6 指南（本库 content 套件）](../../../content/safety_critical/10_standards/04_misra_c_2025_addendum_6_guide.md) |

矩阵读法：Rust 的认证证据分三层——**语言层**（RustBelt 语义模型、unsafe 边界）、**工具链层**（Ferrocene/HighTec/AdaCore 编译器鉴定）、**过程层**（Consortium 编码指南 + `cargo vet` 供应链评审）。任何一层缺失，安全案例（safety case）即不成立。

## 5. 「何时选 Rust 做安全关键」判定决策树

```text
Q1 项目是否处于受监管安全关键域（DAL/ASIL/SIL 非零）？
├─ 否 → 常规 Rust 工程实践即可（clippy + cargo audit + 测试），无需本套件
└─ 是 → Q2

Q2 是否需要第三方认证证据（客户/监管机构索取工具鉴定证书）？
├─ 否（内部安全论证）→ 上游 rustc + Kani/Prusti/Verus 形式化补充
│                      + cargo vet 供应链评审；文档化 unsafe 边界即可
└─ 是 → Q3

Q3 目标完整性等级？
├─ ASIL A/B · SIL 1-2 · DAL D/E → 上游 rustc + 严格 lint 门禁
│   （#![deny(unsafe_code)]、clippy deny）+ 自研工具鉴定包
└─ ASIL C/D · SIL 3-4 · DAL A-C → Q4

Q4 是否接受认证工具链成本（Ferrocene/HighTec 商业授权）？
├─ 是 → Q5
└─ 否 → 重新评估架构：把安全关键功能降级到已认证 C 组件 +
        Rust 做非安全侧（freedom from interference 边界隔离）

Q5 目标平台与语言子集？
├─ 裸机/RTOS（no_std）→ Ferrocene certified core 子集
│   （语言规格 spec.ferrocene.dev 明确裁剪掉 std/动态特性）
└─ Adaptive AUTOSAR（POSIX/Linux）→ ARA 应用 + R24-11 Rust 解释文档
    （见 22_autosar_and_rust.md）

Q6 团队是否具备 unsafe 评审与形式化方法能力？
├─ 否 → 强制 #![forbid(unsafe_code)]，只允许经评审的认证 crate
└─ 是 → 允许受控 unsafe 模块 + RustBelt 风格论证 + 模型检查证据
```

反例警示（何时**不**该选 Rust）：团队无认证预算且客户索取工具鉴定证书（Q4 答否且 Q2 答是）——此时 Rust 带来的内存安全收益不足以抵消认证路径缺口，应选已认证 C 工具链（如 AdaCore GNATcert 历史路径）或混合架构。

## 6. rustc 1.99 实测反例：安全参数越界在编译期被拒（E0080）

安全关键项目常用 const 断言把"栈深度/缓冲区上限"等安全参数固化为编译期事实；参数越界时 rustc 直接拒绝编译，而非留到运行时：

```rust,compile_fail
// ❌ 安全参数越界：栈深度上限被写成非法表达式
const STACK_DEPTH: usize = 1 / 0;
fn main() { println!("{STACK_DEPTH}"); }
```

rustc 1.99.0 实测输出（`rustc --edition 2024`，本机 Windows x86_64）：

```text
error[E0080]: attempt to divide `1_usize` by zero
 --> src/main.rs:2:28
  |
2 | const STACK_DEPTH: usize = 1 / 0;
  |                            ^^^^^ evaluation of `STACK_DEPTH` failed here
```

> **工程含义**：E0080 是 const 求值阶段的硬失败——安全参数错误不可能进入二进制，这正是"编译期即第一道安全门禁"论证（可写入 safety case 的语言特性证据）。惯用写法是把上限断言写成 const 数组长度（越界时数组长度非法 → 同样 E0080），或用 `const _: () = assert!(cond);`。注意：`const fn` 内部对**参数**做条件断言会触发 E0435（"attempt to use a non-constant value in a constant"，rustc 1.99.0 实测），断言必须发生在单态化后的具体常量上。
> **来源**: [rustc E0080 解释页](https://doc.rust-lang.org/error_codes/E0080.html) · [Rust Reference — const 求值](https://doc.rust-lang.org/reference/const-eval.html)

## 7. 跨层导航补充

| 页面 | 主题 |
|:---|:---|
| [Rust vs C/C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) | 安全关键语言选型对比（L5 层：内存安全 vs MISRA 约束下的 C） |
| [安全关键系统工程](23_safety_critical_systems_engineering.md) | 标准矩阵正文（本页 §4 为其索引视图，正文以该页为准） |

## 8. 完整性等级跨标准对照（DAL ↔ ASIL ↔ SIL）

三个标准体系等级不可直接画等号，但风险评估输出可映射（用于多域产品复用安全论证）：

| 风险严重度（危害分析输出） | DO-178C DAL | ISO 26262 ASIL | IEC 61508 / EN 50128 SIL | 典型场景 |
|:---|:---|:---|:---|:---|
| 灾难性（单点失效致全员死亡） | A | D | 4 | 飞行控制律、制动控制、铁路列控（ETCS） |
| 危险性（死亡可能但概率较低） | B | C | 3 | 转向/ESC、工业紧急停机 |
| 严重（重伤） | C | B | 2 | 巡航控制、机床联锁 |
| 次要（轻伤） | D | A | 1 | 信息显示降级路径 |
| 可忽略 | E | QM | 0（BI） | 娱乐系统 |

> 注意：EN 50657:2017（铁路机车车辆车载软件）在 SIL 1–4 之外另设 Basic Integrity（BI）级，对应 EN 50128 的 SIL 0；跨标准复用论证时须按目标域标准重新定级，不能沿用来源域等级。[来源: CENELEC EN 50128/EN 50657 归口（curl 200 实测 2026-10-14）](https://www.cenelec.eu/)

## 9. Rust 认证路径的已知缺口（截至 2026-07，写 safety case 前必读）

1. **上游 rustc 无工具鉴定**：Ferrocene 是目前唯一公开 TÜV SÜD 鉴定报告的 Rust 编译器（ASIL D/SIL 3/DAL C 工具），上游 rustc 用于安全关键需自研 DO-330/Part 8 鉴定包。[来源: Ferrocene 鉴定报告](https://public-docs.ferrocene.dev/main/qualification/report/index.html)
2. **std 不在 certified core 内**：Ferrocene 认证语言子集为 certified core（裁剪动态内存、部分 std），裸机安全关键代码须 `no_std` 或经评审的 std 子集。[来源: Ferrocene Language Specification](https://spec.ferrocene.dev/)
3. **第三方 crate 默认不在认证边界内**：crates.io 依赖需逐个供应链评审（`cargo vet` 元数据 + 人工审查），未评审依赖直接破坏 safety case（见 22_autosar_and_rust.md 反例）。[来源: Safety-Critical Rust Consortium](https://rustfoundation.org/safety-critical-rust-consortium/)
4. **形式化验证工具未鉴定**：Kani/Prusti/Verus 可作为 DO-333 补充证据，但工具本身未获 DO-330 TQL 鉴定，证据权重需评估方认可。[来源: Kani](https://github.com/model-checking/kani) · [Verus](https://github.com/verus-lang/verus)
5. **语言语义模型是论证基础而非证书**：RustBelt 给出 Rust 类型系统的语义模型（可引用为语言层证据），但它不是认证产物。[来源: RustBelt](https://plv.mpi-sws.org/rustbelt/)

## 10. 认证证据类型速查（safety case 论证要素 → Rust 侧证据来源）

| 论证要素 | 标准条款锚点 | Rust 侧证据来源 | 本库入口 |
|:---|:---|:---|:---|
| 语言语义可预期 | DO-333 §3 / IEC 61508-3 Annex B | RustBelt 语义模型、Rust Reference 规范性文本 | [形式化验证工具链](../../04_formal/04_model_checking/01_verification_toolchain.md) |
| 编译器无引入缺陷 | DO-330 TQL / ISO 26262-8 Clause 11 | Ferrocene TÜV SÜD 鉴定报告、编译器测试套件 | [Ferrocene 预览页](../../07_future/02_preview_features/12_ferrocene_preview.md) |
| 覆盖率达标 | DO-178C Table A-6（A 级 MC/DC） | cargo test + 覆盖率工具；MC/DC 预研 | [MC/DC 预研](../../07_future/02_preview_features/02_mcdc_coverage_preview.md) |
| 编码规则符合性 | MISRA 映射 / Consortium 指南 | `#![deny(...)]` lint 门禁 + clippy 配置 + 偏离记录 | [MISRA 指南](../../../content/safety_critical/10_standards/04_misra_c_2025_addendum_6_guide.md) |
| 第三方组件可信 | ISO 26262-8 Clause 12（SEooC） | `cargo vet` 审计元数据 + crate 逐个评审记录 | [cargo vet 供应链审计](../07_security_and_cryptography/03_cargo_vet_supply_chain.md) |
| 干扰自由分区 | ISO 26262-6 / DO-178C 分区论证 | 类型系统 Send/Sync、no_std 静态分区、内存布局审查 | [安全关键系统工程](23_safety_critical_systems_engineering.md) |

> 使用顺序：先按 §5 决策树定路径，再按本表逐项收集证据；每项证据缺失即 safety case 的 open issue。

## 11. 按角色的阅读路线（30 分钟上手）

| 角色 | 路线 | 目标产出 |
|:---|:---|:---|
| 系统工程师（定级阶段） | §8 等级对照 → §5 决策树 Q1–Q4 → [SIL 选择指南](../../../content/safety_critical/03_decision_trees/02_safety_integrity_level_selection_guide.md) | 目标 DAL/ASIL/SIL + 工具链预算决策 |
| 软件架构师（选型阶段） | §4 属性矩阵 → §9 已知缺口 → [认证工具链清单](../../04_formal/04_model_checking/10_certified_toolchains_and_packages.md) | 语言/工具链/依赖三层边界草案 |
| 开发工程师（实现阶段） | §6 编译期门禁反例 → §10 证据速查 → [22_autosar_and_rust.md](22_autosar_and_rust.md) 收窄转换反例 | lint 门禁配置 + 编码规则偏离记录模板 |
| 评估/审计方（确认阶段） | §10 证据速查 → §9 缺口清单 → content 案例套件（[Ferrocene](../../../content/safety_critical/07_case_studies/01_case_study_01_ferrocene_certification.md) / [铁路信号](../../../content/safety_critical/07_case_studies/05_case_study_05_railway_signaling.md)） | safety case open issue 列表 |
