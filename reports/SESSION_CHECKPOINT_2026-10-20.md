# 会话检查点 2026-10-20（authority 增强波收官 + 外链腐烂波开局）

> **新会话入口**：根 `AGENTS.md` §0 loop 协议 → 本文件 → `reports/S2_R3_PROGRESS.json`（账本）。
> 用户执行偏好（2026-10-20 明确）：**主代理串行单线推进，不并行子代理写库**；此前一次性派发的 4 路只读探针已被叫停/完成，其结论不作为权威，凡需复核一律主线重跑。

## 1. 已闭环（勿重做）

| 波次 | 内容 | 提交 |
|:---|:---|:---|
| W4–W9 领域生态 | jiff/GUI/CV/gRPC/syscall/音频DSP 七页 | 至 be1fddd1d |
| W9 P0 闭环 | 三新页补 std::net/Nomicon FFI×2 权威锚，authority content-scope P0 100% | e956a706b |
| authority 微补录 | 12_linear(RustBelt)/15_refinement(Flux PLDI23)/31 GUI(wasm tier2)/32 CV(Nomicon FFI)/21 stub(RFC3355) | 8721cb9bb |
| 账本 | D/W 队列全清、S2-R3 语言语义反例封账口径 | 71bdbd839 |
| **P1 锚增强（本批）** | 12_linear+Aeneas ICFP22/SoundBorrow PLDI24/Verus OOPSLA23；21 stub+Aeneas/PLDI24；13_grpc+REST-vs-gRPC SOMET22/gRPC隐私 ICWE24；32 CV+Kornia-rs | **384079391** |

## 2. 门基线（2026-10-20，384079391 后）

- authority（`python scripts/check_concept_authority_coverage.py --include-crates`）：content-scope n=691 **P0 100% / P1 98.7% / P2 100% / any 100%**；core L1-L4 gaps=0；全库 none=0。
- 23 阻断门全量：8721cb9bb 批末 23/23 全绿（2,812 行日志快照）。
- 报告再生成必须带 `--include-crates`，否则丢失 crates 扩展附录（569 docs 页 100% 覆盖 + dead_canonical=0 段）。

## 3. 下一波（按序）

### 波A（主项）：外链腐烂清扫
`python scripts/check_all_concept_links_health.py` → **148 FAIL**。curl 抽查 5 条属实：
- `doc.rust-lang.org/reference/ownership.html` 404（Reference 结构改版，改 live 锚）
- `doc.rust-lang.org/book/ch04-00-ownership.html` 404（The Book 章节结构改版）
- `doc.rust-lang.org/nomicon/raii.html` 404（Nomicon 重组）
- `blog.rust-lang.org/2026-01-29/Rust-1.88.0.html` 404（**日期/版本错位**——博客日期不可凭记忆写）
- `rustc-dev-guide.rust-lang.org/targets.html` 404 · `rust-lang.org/production/users` 301
修法：逐 URL curl 核验 → 换 live 等价锚（优先同页新 URL；无等价则删或降级引用）→ 批 dry-run → 批内只跑 dead-links 门、批末全量 23 门。

### 波B：authority P1 残余 9 页锚补录
页清单（门输出，2026-10-20）：24_cargo_basics · 12_container_build_and_delivery_pipeline · 57_posix_syscall_crate_ecosystem · 29_time_and_date_ecosystem · 30_chrono_vs_jiff · 31_desktop_gui_ecosystem · 32_computer_vision_ecosystem(已补 kornia-rs，待门复跑确认) · 33_audio_dsp_ecosystem · rust_1_99_stabilized。

**已在线核验锚池（arXiv API 标题级核验，2026-10-20 直接可用）**：
- 24_cargo_basics：CHRONO-RESOLUTION 依赖解析数据集（arXiv 2607.15315, ICSME 2026, 含 crates.io）· A Closer Look at the Security Risks in the Rust Ecosystem（arXiv 2308.15046, TOSEM preprint）· Is unsafe an Achilles' Heel?（arXiv 2308.04785）
- 12_container_build：Attestable Builds（arXiv 2505.02521, DOI 10.1145/3719027.3765128）· PhantomRun CI 构建复现（arXiv 2604.27075, EASE26）
- 32_computer_vision：Kornia-rs（arXiv 2505.12425）✅ 已落 32 页
- 待核验（未过标题核验，勿直接引用）：Tiwari 日期时间 bug 论文（arXiv API 零命中）· USENIX ATC19 Jangda wasm 性能 · Cooley-Tukey 1965 Springer DOI · ECS 综述（arXiv API 抓取失败）· 57_posix 无直接对口论文（候选 Heimdall eBPF→Rust arXiv 2605.25411 语义不符）· 31 GUI 的 Brendel/Liedtke IMGUI-MR 论文（dl.gi.de，**不在 P1 域清单**，需门口径确认或另找 ACM 锚）· rust_1_99_stabilized 属版本跟踪页，建议走门豁免裁决而非硬凑学术锚。

### 波C：cargo/edition 事实实测复核
rustc 1.99.1 工具链（`C:/_program/rust/rustup/toolchains/1.99.1-x86_64-pc-windows-msvc/bin` 直调，`export CARGO_HOME=C:\_program\rust\cargo`）：cargo new 默认 edition 行、cargo add 写入门径与 features 语义、jiff 依赖树——对应 24_cargo_basics 页事实校验（探针被叫停未产出，主线重跑）。

## 3b. 已停探针的实证结论（可采信，2026-10-20 送达）

- **authority 重扫探针（完成）**：复刻门逻辑独立扫描 792/691 页，与 10-20 报告基线零漂移；确认 **USENIX 不在门 P1 正则域内**（仅 crates 扩展口径有），3 页含 usenix 链接不计 P1 命中——波B 选锚时勿用 USENIX 论文凑 P1。探针基于 HEAD 71bdbd839（早于 384079391）：其 11 页 P1 清单中 13_grpc/21_spec/32_CV 三页已在 384079391 补学术锚闭合，波B 实际剩余 = 波B 清单减去这三页。复刻脚本 `…\cache\scratch\rescan_authority.py`（24h 后清理，需复跑就主线重建）。
- **cargo 实测探针（完成，波C 可直接引用）**：rustc/cargo 1.99.1 下 `cargo new` 默认 **edition = "2024"**；`cargo add jiff` → `jiff = "0.2.38"`（jiff-core 0.1.1 + jiff-tzdb-platform 0.1.3→jiff-tzdb 0.1.9 + windows-link 0.2.1）；`cargo add --features` 仅显式 features 落盘为内联表 `serde_json = { version = "1.0.154", features = ["preserve_order"] }`，默认 features 展示不落盘；dry-run 刷新 index + 预览 + `warning: aborting add due to dry run` 不改文件。→ 24_cargo_basics 页事实校验以此为准。
- 学术锚两探针（中断，部分产出）：仅采信其中已经主线 web_extract/arXiv API 标题级核验过的条目（已入 §3 波B 锚池）；两探针 partial transcript 在 `…\cache\delegation\live\deleg_922e6c0c\`，若波B 需要更多候选可翻 task-1.log / task-2.log 提取候选再主线核验，未核验项不得引用。

## 4. 环境备忘

- terminal 经 bash；原生工具（git/cargo/python）只认 `C:/` 正斜杠路径。
- push：origin SSH（git@github.com:martin-ly/rust-lang.git，已验证）。本检查点提交后 push 状态见 git log/remote。
- 版本事实基线：stable 1.99.1（2026-10-15 补丁）/ beta 1.100.0（GA 预计 2026-11-12，cron e463a69a99c9）。
- 挂机 cron：14459c312b92（每 3h loop 续做，prompt 已指向本检查点后的波序）；S2-R3 反例补全封账（严格口径 174 页缺口完成）。
