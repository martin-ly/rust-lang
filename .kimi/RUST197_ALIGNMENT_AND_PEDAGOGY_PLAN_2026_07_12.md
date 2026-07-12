# Rust 1.97 全维度对齐 + 思维表征/测验体系 + Async/并发形式模型深化计划

> 日期：2026-07-12 ｜ 状态：**已确认全量执行**（W0–W5）｜ 裁定：W5 归属 04_formal/07_concurrency_semantics；quiz 保持 .md 按四级规范改造 ｜ 前置：semantic health 99.6（公式上限），全 20 门通过

---

## 0. 盘点结论摘要（三份只读审计，2026-07-12 下午）

| 维度 | 现状 | 核心缺口 |
|---|---|---|
| 1.97 语言特性 | release notes 41 条全覆盖；矩阵化治理（31×9）仅 1.97 有 | target features（scq/lamcas 等）零覆盖；import self 放宽零覆盖；WSAESHUTDOWN 迁移缺口未落地；1.90–1.96 下沉链接仅 3–7 个/版 |
| 编译器 | 管线/MIR/诊断/LLVM 均有权威页 | `-Z` flags 无系统清单页；并行前端/Cranelift 双权威页风险；target tier 变化无 consolidated 页 |
| 构建工具 | Cargo 22 页横幅齐 | 缺 cargo_197_features.md（有 1.96 先例）；rustdoc 停留 1.96 特性集；miri 无版本对齐声明 |
| 认证包/工具链 | ISO 26262/DO-178C/IEC 61508/MISRA 指南齐（content/） | Ferrocene 权威页定性错误（按 nightly 预览写，实为已交付认证工具链）；AUTOSAR concept 零覆盖；cargo vet/供应链认证无专页；content/safety_critical 无 concept 索引入口且 master_index canonical 链接张冠李戴 |
| 思维表征 | 多列矩阵 74%、mermaid 50%（99% 是 flowchart） | mindmap 内容层仅 14 页；示例反例/决策树/推理/判定树四类 atlas 合计仅覆盖 ~8% 概念页；五件套完整率 5–21%（反例最弱） |
| 测验体系 | 15 独立 quiz/144 题 + 275 页嵌入测验 ~1224 块 + exercises 分层测试 | L0/L7 零 quiz；06 层 43 页无测验；题型 90% 是"能否编译"开放题（mdbook-quiz 四级规范零落地）；无逐题难度分级；quiz→concept 单向链接；149 页权威页无任何测验；quizzes 索引腐化（列 3/15） |
| Async | 8 权威页 + 2 交叉页，取消语义/边界全景已形式化 | 无 Tokio 深度权威页；Stream 代数/Executor 公平性/Pin 投射反例集/Waker 契约/async UB 目录未成页 |
| 并发形式模型 | 共享内存模型/共识深度充足；五概念定义页齐 | CSP/Actor/π-calculus/线性化/CRDT/向量时钟无独立形式化页；04_formal 缺并发语义子层；无一页式五模型定义矩阵 |

**即刻勘误项（P0，无需确认直接修）**：① rust_1_94_stabilized.md 正文疑似重复三遍；② content/safety_critical master_index canonical 链接指向 stream_processing（张冠李戴）；③ 并行前端/Cranelift 双权威页定主从；④ quizzes 索引腐化。

---

## 1. 工作流总览（W1–W5 + W0 勘误）

### W0 勘误与止血（0.5 人日，1 个代理）

1. rust_1_94_stabilized.md 三段重复核查与去重；
2. safety_critical master_index canonical 链接勘误 + content/ 套件在 concept/ 建索引入口页（AGENTS §2.1 第 3 条）；
3. 并行前端/Cranelift 双权威裁定：preview 页保留跟踪定位、infrastructure 页相关节改摘要+链接（canonical 规则）；
4. docs/02_learning/quizzes/README.md 索引更新为全量 15 quiz。

### W1 Rust 1.97 全维度对齐深化（2–3 人日，2 个代理并行）

**W1-a 语言/编译器**：

1. target features（scq/lamcas/lam-bh/ld-seq-sa/div32）补入 `05_atomics_and_memory_ordering.md` + 新建「平台 target features」小节；
2. import self 放宽补入 use 声明权威页；WSAESHUTDOWN→BrokenPipe 补入 `01_error_handling.md`；must_use×uninhabited 下沉 `02_never_type.md`；
3. 新建 `concept/06_ecosystem/00_toolchain/15_z_flags_reference.md`（-Z flags 系统清单，rustc-dev-guide 为源）；
4. 新建 target tier 平台支持 consolidated 页（rustc book Platform Support 为源）；
5. std 表面 API 五项在对应权威页加 1.97 注记（迭代器/整数类型/char 页）。

**W1-b 构建工具/认证**：
6. 新建 `05_cargo_197_features.md`（对齐 1.96 先例：build.warnings/lockfile-path/-m/curl 移除）；
7. rustdoc 权威页补 1.97 稳定项（--emit/--remap-path-prefix）；miri 页补版本对齐声明；rustfmt/clippy 补 1.97 行为注记；
8. **Ferrocene 页重写**：按"已交付商业认证工具链"框架（TÜV SÜD 证书、Ferrocene 26.02.0、certified core 边界），改文件定位声明；
9. 新建「认证工具链与认证包清单」权威页（Ferrocene Qualification Report/SCRC 为源；含 certified core 子集、认证 crate 生态）；
10. AUTOSAR 概念页（content 案例升格引用 + concept 权威页）；
11. cargo vet/供应链认证专页（mozilla cargo-vet 为源，与项目自身门 5 呼应）。

### W2 思维表征体系化（3–4 人日，2 个代理并行）

**W2-a 内容层 mindmap + 五件套**：

1. 为 L1–L4 核心权威页（约 40 页，按学习路径优先级）补 mermaid mindmap（每页 1 幅，概念结构总览）；
2. 五件套补齐：对五件套完整率最低的 06 层（5%）与反例短板页（07 层 11%）做批量结构化补全——每页补「反例」节（compile_fail/陷阱/UB 至少 1 例）；
3. 新增 atlas 表征检查器扩展：mindmap 覆盖率、反例存在率纳入 check_association_blocks.py 或新观察门。

**W2-b 深度 atlas 扩展**：
4. 示例反例 atlas（04）从 40 页扩至 ≥120 页（按 extract_concept_topology 的示例/反例抽取，优先 L1–L3）；
5. 场景决策树 atlas（03）从 39 扩至 ≥80 页；推理判定树 atlas（09）从 15 扩至 ≥40；
6. 层间映射 atlas（06）从仅 L0/L1 扩至全层；
7. 全部改动固化进生成器/模板（只重生成不手改纪律）。

### W3 测验体系化（3–4 人日，2 个代理并行）

**W3-a 注册表与规范落地**：

1. 新建 `concept/00_meta/04_navigation/15_quiz_registry.md` + 机器可读 `quiz_registry.yaml`：全库测验资产（15 独立 quiz + 275 页嵌入 + exercises 131 test + Brown/rustlings）统一注册，字段：层级/主题/题型/难度/题数/双向链接状态；
2. 按 mdbook-quiz 指南四级题型规范改造 15 个独立 quiz：补单选/多选/判断题（每 quiz 至少 3 题型混合），逐题标难度（基础/进阶/专家）；
3. 新建 quiz 检查器 `scripts/check_quiz_system.py`：注册表一致性、题型分布、双向链接、难度标注（观察门）。

**W3-b 覆盖补缺与双向链接**：
4. L0/L7 新建独立 quiz（每层 1–2 个，10 题）；06 层按子领域补 4–6 个 quiz（网络/async 生态/数据库/安全/测试/领域应用）；
5. TOP-20 无测验权威页补嵌入测验（每页 3–5 题，按五件套中的"反例"联动）；
6. 双向链接：quiz 注册表生成后，批量在 concept 页「相关概念」节回链对应 quiz（脚本化，幂等）；
7. 修复 quizzes 索引（W0-4 基础上保持同步）。

### W4 Async 全面分析深化（2–3 人日，1–2 个代理）

按盘点成页建议（全部 rustc 1.97 实测 + 国际权威源 curl 验证）：

1. `09_stream_algebra_and_backpressure.md` — Stream/Iterator 对偶、组合子代数、背压信用制形式模型（P1）；
2. `10_executor_fairness_and_scheduling.md` — tokio LIFO/work-stealing 公平性、glommio 对比、饥饿分析（P1）；
3. `11_pin_projection_counterexamples.md` — unsafe 手写投射 UB 目录 + pin-project 正确模式全集（P2）；
4. `12_waker_contract_deep_dive.md` — 自定义 Waker、wake 契约违反反例集（P2）；
5. `13_async_trait_object_safety.md` — dyn-compatible 谱系选型矩阵（P3，06_panorama §9 升格，canonical 迁移）；
6. `concept/06_ecosystem/04_web_and_networking/10_tokio_runtime_internals.md` — Tokio 深度权威页（调度器/mio/blocking 池/JoinSet/LocalSet 语义归一，相关分散节改摘要+链接）；
7. async 权威源索引补 3 项（scheduler internals 博文、async WG 路线图、understanding-async 类深度源）。

### W5 并发/并行/同步/异步/分布形式模型（3–4 人日，1–2 个代理）

新建 `concept/04_formal/07_concurrency_semantics/` 子层（待确认归属）：

1. `01_process_calculi_for_rust.md` — CSP/CCS/π-calculus 与 Rust channel/所有权形式对应（Hoare 1978/Milner 1992）；02_isomorphism 相关节改摘要+链接（canonical 迁移）；
2. `02_linearizability_and_consistency.md` — Herlihy-Wing 线性化定义/证明方法 + 一致性谱系形式化（与 07_spectrum §6.2 分工）；
3. `03_actor_semantics.md` — Actor 形式语义（邮箱/监督/位置透明性）× actix/ractor；
4. `04_crdt_type_zoo.md`（归 06_ecosystem/06_data_and_distributed/）— CRDT 谱系 + 合并格形式化（Shapiro 2011）；
5. `05_causal_ordering_vector_clocks.md`（同目录）— Lamport/向量时钟/因果序；
6. `concept/05_comparative/00_paradigms/04_five_models_definition_matrix.md` — 五模型一页式定义矩阵（摘要+链接型导航页，不复制正文）；
7. SUMMARY/索引/KG 同步；canonical 门保持 0 ERROR。

---

## 2. 执行编排

```
阶段 1（并行）：W0 勘误 + W1-a + W1-b
阶段 2（并行）：W2-a + W3-a + W4（前 3 页）
阶段 3（并行）：W2-b + W3-b + W4（后 4 项）+ W5（1-3）
阶段 4：W5（4-7）+ 全量终验（20 门 + semantic health + mdbook）
```

每线独立代理、只做增量、不动 git；canonical 迁移一律"旧节摘要化+链接"，不产生双权威。

## 3. 质量约束（全部沿用既有红线）

- 新页：AGENTS §4.2 元数据模板、目录内 NN_ 续号、SUMMARY 同步、KG 加节点；
- 代码示例：rustc 1.97 --edition 2024 实测；外链：curl 实测 200；
- 禁止模板套话（check_template_cliches）；每阶段后 kb_auditor 死链 0/跨层 0 + canonical 0 ERROR；
- 预估规模：新页 ~25 个、改造页 ~80 个、quiz 新增/改造 ~30 个、atlas 扩展 ~150 概念覆盖。
