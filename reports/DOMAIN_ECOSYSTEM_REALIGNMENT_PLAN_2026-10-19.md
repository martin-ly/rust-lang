# Domain / 生态主线重定位计划（D 轨道转正）

日期：2026-10-19 ｜ 状态：**已确认生效（2026-10-19 用户 clarify 四项决策）** ｜ 决策依据：用户 2026-10-19 纠偏原话——
「这个做下去 其实和做编译器测试差不多。可是 本项目是针对的 rust 的语言软件开源生态 而不是做测试」

## 0. 用户确认结果（2026-10-19）

1. S2-R3 反例 loop：**方案 A 降格收尾**——只在语言语义组（01_foundation/02_intermediate/03_advanced/04_formal 残余）继续反例单；06_ecosystem domain 组豁免反例单，改走生态实证线。
2. 五要素验收线：**确认固化为账本口径**。
3. D 轨道批次顺序（用户指定优先队列）：**WASM → 算法 → 企业 → 合规**，其后区块链、ML、游戏组。
4. cron `14459c312b92`：**改写为 D 轨道生态批次驱动**。

## 1. 问题认定

S2-R3「实测反例补全」loop（Batch1–17）在 06_ecosystem 的 domain 组产出的内容形态是：
E0599/E0072/E0308 编译报错、Miri UB、溢出回绕——这是**语言语义测试**的产出形态，
不是「Rust 语言软件开源生态」知识库的 domain 内容形态。语言语义反例对 01_foundation～
03_advanced 组是合理的质量锚，但对 11_domain_applications / 14_enterprise_architecture /
16_algorithm_patterns 组，正确锚应是**生态实证**，不是编译器报错。

## 2. 本机盘点事实（2026-10-19 实测）

- domain 组体量：11_domain_applications 28 页/613,594 字符；16_algorithm_patterns 20 页/360,165；
  14_enterprise_architecture 18 页/220,508；00_toolchain 16 页/308,301；01_cargo 24 页/255,102。
- 生态锚点覆盖不均：
  - 高锚点样本：13_machine_learning_ecosystem 11 个真实 crate 锚（candle/burn/linfa/tch-rs/ndarray…）。
  - 零锚点重灾区：16_algorithm_patterns 20 页中 11 页零生态锚（纯教科书算法形态）。
  - 缺口样本：01_blockchain 无 rust-bitcoin/rust-secp256k1；04_licensing 0 锚；
    27_ownership_aware_algorithms 0 锚。
- stub/重复：05_game_development + 06_game_development 双 stub、09_data_structures_in_rust 683B stub、
  12_formal_algorithm_theory 1,212B stub；08/09_data_structures 跨组疑似重复对。

## 3. 新主口径：domain 页的「生态实证」验收线（替代反例线）

对 06_ecosystem 各 domain 组，逐页验收以下五要素（不是 compile_fail 反例）：

1. **具名项目覆盖**：每页点名该领域真实活跃项目（含定位/版本/活跃度），例：
   - blockchain: rust-bitcoin, rust-secp256k1, Substrate/Polkadot, bitcoin core 对照
   - game: Bevy, Fyrox, macroquad, hecs, wgpu, Rapier
   - wasm: wasmtime, wasmer, wasm-bindgen, wasm-pack, Wasmtime 1.x/WASIp2 现状
   - ML: candle, burn, linfa, tch-rs, rust-cnn 现状与分工
   - safety-critical: Ferrocene 认证状态、AUTOSAR/MISRA 对齐、Rust 认证路线图
   - enterprise: tokio/axum/tower/tracing/OpenTelemetry 事实栈 + Discord/Cloudflare/Figma/Amazon 采用证据
2. **版本事实本机/联网核验**：pinned 版本经 crates.io / cargo 实查对齐（如 candle/burn/wgpu 当前版本）。
3. **工业案例引用可核验**：生产采用陈述必须落到可点击权威源（公司工程博客/官方 post-mortem）。
4. **生态缺口队列**：领域内缺失 canonical 页登记（如「WASIp2 实践」「rust-bitcoin 钱包栈」「Rapier 物理引擎」）。
5. **stub/重复治理**：domain 组内 Redirect stub 逐一裁决（充实 or 合并指向 canonical）。

## 4. S2-R3 反例 loop 处置（三选一，待确认）

- **A（推荐）降格收尾**：剩余反例缺口只在语言语义组（01_foundation/02_intermediate/03_advanced/04_formal 残余）继续，
  量小且已有口径；06_ecosystem domain 组豁免反例单，改走第 3 节生态实证线。
- **B 立即停止**：S2-R3 封账于 Batch17（语言语义组覆盖率已高，报告收尾），全部产能转 D 轨道。
- **C 原样继续**：维持现口径直到 design_patterns/algorithm_patterns 残余清零（不推荐——与项目定位冲突）。

cron `14459c312b92`（每 3h）随选定方案改写：A→cron 只跑语言语义残余；B→cron 改跑 D 轨道批次；C→不动。

## 5. D 轨道批次编排（用户确认队列：WASM → 算法 → 企业 → 合规 → 区块链 → ML → 游戏）

- **D1 WASM 组**：03/17-20 五页版本对齐（Wasmtime/Wasmer/wasm-bindgen 2026 现状、WASIp2 实践）+ wasm-pack/cargo-component 覆盖 + 18/19 glossary/FAQ 锚点充实。
- **D2 算法组**：16 组 11 个零锚页逐页补「该算法族的 Rust 生态实现」锚（petgraph/pathfinding/ndarray/ordinals/rayon/crossbeam/divan 基准文化）+ 11 组 07-12/24-28 算法页同线；纯理论页保留理论口径。
- **D3 企业组**：14 组「采用证据可核验化」轮——每条工业案例（Discord/Cloudflare/Figma/Amazon/Finance）配 P0 权威链接 + tokio/axum/tower/tracing/OpenTelemetry 版本事实栈实查。
- **D4 合规/安全关键组**：04_licensing 补 crates.io license 生态数据；21/22/23 Ferrocene 认证状态/AUTOSAR/MISRA 版本对齐。
- **D5 区块链组**：01_blockchain 充实（rust-bitcoin、rust-secp256k1、Substrate/Polkadot 生态全景 + 版本核验）。
- **D6 ML 组**：13 页 candle/burn 2026 版本实查勘误 + 推理部署缺口页登记（candle-onnx/candle-metal/ort）。
- **D7 游戏组**：05/06 双 stub 裁决合并 → Bevy/Fyrox/macroquad/hecs/wgpu/Rapier 锚点充实三页联动。
- 每批完成：语义健康门 + authority coverage 门 → ledger → commit/push（批门全绿即推，沿用 2026-10-16 授权）。

## 6. 不变项

- 治理权威 AGENTS.md（23 门、§6、只移动不删除）不动；语言语义组既有实测反例保留不拆。
- P1/P2 权威覆盖微补（4+2 页）、F 轨道三 canonical、miri README 断链、move_ledger.csv 仍挂账。
- 1.100 GA 对齐 cron `e463a69a99c9`（2026-11-13 后）不动。


---

## 状态更新（2026-10-19 收口，第 2 次）

**D 队列 D1–D7 + V1/T1 全部落地并推送**（main 与 origin/main 同步，HEAD `53557f392`）：

| 批 | 内容 | commit |
|---|---|---|
| D1 WASM | 8页版本实查锚 | `047f2ea3f` |
| D2 算法 | 9页零锚补线 | `7542b629a` |
| D3 企业 | EA 16页锚+工业P0引用 | `920c6a4fa` |
| D4 合规 | 12页工具链锚+Ferrocene勘误 | `b884d548f` |
| D5-D7 区块链/ML/游戏 | 7页锚+substrate口径勘误 | `80ac7442d` |
| V1+T1 | chrono 专页新建(E0277实测)+pin勘误 | `53557f392` |

## 后续队列（下一轮 loop 输入，按优先级）

1. **W2 金融一手引用**：JPMorgan/ABN AMRO 等 Rust 金融采用的一手 P0 来源检索补链（D3 遗留）。
2. **W3 IoT SDK 实查**：AWS IoT / embedded Rust SDK 组件族 crates.io 版本登记（D3 遗留）。
3. **W4 jiff 评估页**：BurntSushi jiff（新一代日期时间库）实查后决定建 canonical 页或并入 29 页。
4. **W5 automotive/AUTOSAR 权威口径**：crates.io automotive 分类（49 crates）逐 crate 实查，替换库内分析性 AUTOSAR 叙述的待核查标注。
5. **语言语义组反例残余**（旧口径 fresh9=72，用户裁决 A）：排在 W 队列之后，仅语言语义组（01/02/03/04），06_ecosystem 永久豁免。
6. **1.100.0 GA 对齐**（2026-11-12 后，cron `e463a69a99c9` 已排 11-13）：版本事实基线全库刷新。
