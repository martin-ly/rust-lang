# 权威对齐对称差报告 2026-10-19（AUTHORITATIVE_SYMMETRIC_DIFF）

状态：**生效** — 本报告是 D 轨道（Rust 语言软件开源生态实证主线）的缺口权威来源。
方法：以 crates.io API 全量实查（2026-10-19，58 分类全量拉取）+ 具名锚点 crate 逐个 API 实查，对照本知识库 669 内容页（排除 00_meta/sources/quiz/placeholder/version_tracking），产出三向对称差：**库缺（外部权威有、库无）/ 库余（库有、外部已废或过时）/ 版本差（库 pin 与 crates.io 当前值不符）**。

## 1. 外部权威基准（本轮实测）

- crates.io 分类全集：**58 类**（API `categories` 全量分页实查，含 2025-2026 新设类：automotive 2025-08、artificial-intelligence 2026-02、security 2025-03、virtualization 2022）。
- 具名锚点当前版本（crates.io API 实查，2026-10-19）：
  wasmtime **49.0.3** · wasmer **7.5.0** · wasm-bindgen **0.2.129** · wasm-pack **0.15.0** · hashbrown **0.17.1** · syn **3.0.9** · getrandom **0.4.3** · bitflags **2.13.0** · rand **0.10.0** · libc **0.2.191** · quote **1.0.47** · proc-macro2 **1.0.107** · base64 **0.23.0** · indexmap **2.14.0**
- 语言版本基线：stable **1.99.1**（2026-10-15 补丁）/ beta **1.100.0**（GA 2026-11-12）。

## 2. 对称差 A：库缺（外部权威主题域，库无专页或覆盖薄弱）

按 crates.io 分类规模 × 库内专页覆盖排出缺口梯队（专页=标题/章节级命中）：

**T1 缺口（0 专页）**
| 分类 | crates.io 规模 | 库现状 | 处置 |
|---|---|---|---|
| web-programming(深部分支) | 16,407 | 有框架页但缺 2026 版实查 | D3 企业批勘误 |
| date-and-time（chrono 系） | 935 | 54 页仅提及、0 专页 | 新增 canonical |
| caching | 1,135 | 17 页提及但无 canonical 缓存生态页 | D3 批 |
| artificial-intelligence（crates.io 2026-02 新设类） | 334 | 库 ML 页早于该类设立，未对齐官方分类 | D6 ML 批勘误 |
| security（crates.io 2025-03 新设类） | 467 | 0 专页（库 07_security 组是密码学口径，非网络安全工具口径） | D4 合规批 |
| computer-vision | 665 | 3 页仅提及 | 登记 canonical 缺口 |
| email | 658 | 0 专页 | 低优先登记 |
| accessibility | 680 | 0 专页 | 低优先登记 |
| localization (L10n) | 535 | 0 专页（i18n 有、L10n 无） | 低优先登记 |
| value-formatting | 732 | 0 专页 | 低优先登记 |
| aerospace | 420 | 2 页（形式化认证+太空展望） | 已达标 |

**T2 弱覆盖（有专页 1-2，不足以承载该域）**
- gui（5,446 crates，1 个偶然专页）→ D 队列外新增建议：**GUI 生态 canonical 缺口**（egui/iced/Slint 工业采用：Figma 方向已有但 egui 版本未实查）。
- automotive（49 crates）→ 22_autosar 页已有，需 Ferrocene 4.0 认证状态 2026 实查（D4）。
- finance（1,613）→ 2 页，需 2026 采用案例刷新（D3）。
- emulators/virtualization → 覆盖可，Firecracker 版本需实查（D3）。

## 3. 对称差 B：版本差（库内 pin 落后 crates.io 当前值，须勘误）

| 锚点 | 库内旧 pin | crates.io 当前 | 落点页 |
|---|---|---|---|
| hashbrown | 0.12.3 / 0.16.1 | **0.17.1** | 04_formal/05_rustc_internals 系列、算法组 |
| indexmap | 2.11.4 | **2.14.0** | 数据结构/性能页 |
| wasm-bindgen | 0.2.105 | **0.2.129** | WASM 组（勘误历史保留） |
| rand | 0.8.5 | **0.10.0** | rand 相关页（0.9/0.10 API 换代需注记） |
| syn | 旧代 pin | **3.0.9**（major 换代） | proc-macro 组需注记 syn 3.x |
| bitflags | 1.3.2 | **2.13.0**（major 换代） | hardware/embedded 页 |
- wasmtime 49.0.3 / wasmer 7.5.0 / wasm-pack 0.15.0：库内无版本 pin → D1 批补版本事实锚点（不算过时，算缺失）。

## 4. 对称差 C：库余（库内口径与外部权威不一致，保留历史+追加勘误）

- 06_ecosystem/07_security_and_cryptography 组的"security"口径=密码学；crates.io 2025 新设 security 类=网络安全工具域（渗透/漏洞/逆向）。两组不互相覆盖，须显式区分并各立 canonical。
- crates.io wasm 分类 top-downloads 前 12 全为基础库（hashbrown 27.6亿、syn 27亿、getrandom、bitflags、rand、libc、proc-macro2、base64、windows-sys、indexmap）——即 WASM 生态主体是**基础库跨 wasm 目标**而非 wasm 专用库；库内 WASM 页偏引擎/互操作叙事，须补此权威事实。
- 旧反例口径残留：`s2_gaps_fresh9.json` 中 domain 组 46 个 gap 不再作反例单（已按 D 口径转生态实证线，账本已固化）。

## 5. 对称差驱动的后续队列（固化）

- **D1 WASM**（进行中）：5 页版本实查勘误（上表 pin 差全落此批+15_web_technologies/17）；补 wasmtime 49.0.3/wasmer 7.5.0/wasm-pack 0.15.0 版本锚；补"wasm 分类 top-downloads=基础库"权威事实；WASIp2/Component Model 现状对齐。
- **D2 算法**：16 组 11 零锚页补 petgraph/rayon/crossbeam/rustc-hash/hashbrown 0.17.1/indexmap 2.14.0 实查锚。
- **D3 企业**：14 组 17 页补 2026 工业采用案例（finance 2 页刷新、Firecracker/Discord/Cloudflare 版本实查）+ caching canonical 缺口裁决。
- **D4 合规**：Ferrocene 认证状态实查 + crates.io security 类（网络安全口径）canonical 缺口登记 + AUTOSAR automotive 类对齐。
- **D5 区块链**（rust-bitcoin 缺锚）、**D6 ML**（对齐 crates.io artificial-intelligence 新类 + candle/burn 版本实查）、**D7 游戏**（bevy 版本实查 + 05/06 双 stub 裁决）。
- **新增候选（本报告产出）**：chrono/日期时间 canonical 页、GUI 生态 canonical 页、computer-vision 缺口登记 —— 排 D7 之后。
- 语言语义组反例残余（仅 2 页：03_advanced/02_unsafe、04_formal/00_type_theory）在 D 队列完成后收尾。

## 6. 验收口径

每批按 domain 五要素（已固化账本）：①具名活跃项目覆盖 ②版本事实 crates.io/cargo 实查 ③工业采用案例可核验 P0 引用 ④canonical 缺口登记 ⑤组内 stub/重复裁决。版本事实一律实查，禁止凭记忆；历史口径保留并追加勘误。
