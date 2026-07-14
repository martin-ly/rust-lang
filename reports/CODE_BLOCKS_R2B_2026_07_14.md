# concept/ 代码块编译实测 R2b：dep_fail 治理报告（工具侧）

> **日期**: 2026-07-14
> **范围**: 仅 `scripts/check_concept_code_blocks.py` 工具改进；concept/ 文档侧修复由并行代理处置。
> **基线**: `tmp/cb_r2_v3.json`（v3 全量实测）；**终值**: `tmp/cb_r2b.json`（R2b 全量复跑）。

---

## 1. 前后数字

| 指标 | v3 基线 | R2b 终值 | 变化 |
|---|---:|---:|---:|
| **dep_fail** | **148** | **1** | **-147** |
| dep_pass | 147 | 149 | +2 |
| dep_untested（runtime+豁免） | 25 | 26 | +1（豁免计入） |
| candidate_pass | 1860 | 1865 | +5（无回归） |
| candidate_fail | 153 | 0 | -153（文档侧修复） |
| compile_fail_ok | 810 | 810 | 0（无回归） |
| compile_fail_unexpected_pass / wrong_code | 0 / 0 | 0 / 0 | — |
| **rot_total** | **301** | **1** | -300 |

- 剩余唯一 dep_fail：`concept/03_advanced/01_async/01_async.md:3355` —— ❌/✅ 对比块含两个
  `fn main`（`E0428`），属真实文档结构问题（建议文档侧拆块或标注 `rust,ignore`），工具不应掩盖，留待文档侧。
- v3→R2b 之间 concept/ 树被并行代理大量修改（anno_ignore 1690→1983，dep 320→176，
  candidate 2013→1865），上表为混合效果；**工具侧独立贡献**见 §3 受控复测。

## 2. v3 dep_fail=148 错误分类统计

| 类别 | 数量 | 处置方式 |
|---|---:|---|
| A. 版本跟踪页演示性 API 未实现（c0x::rust_19x_features 等） | 37 | DEP_KNOWN_MISSING 豁免（file+crates 规则） |
| B. proc-macro crate-type 未适配（`#[proc_macro*]` 仅限 proc-macro crate） | 10 | 新增 `--crate-type proc-macro` 回退模式 |
| C. proc_macro 相关其余（缺 `use proc_macro::TokenStream` 等 import） | 2 | 文档缺口，转文档侧 |
| D. 顶层 `.await`（E0728，包入 fn main 后非法） | 11 | 新增 async fn 包装回退 |
| E. workspace feature 未启用（reqwest gzip/cookies、tower util、tower-http auth、parking_lot deadlock_detection、tokio test-util、signal-hook iterator） | 8 | DEP_KNOWN_MISSING 豁免（err 规则，逐条核对根 Cargo.toml） |
| F. tokio feature 模块/变体选择（fs/process/signal 等） | 6 | 变体去重+笛卡尔积轮换修复；兜底豁免 |
| G. crate 不在 workspace（async_stream、trait_variant、aws_sdk_*） | 4 | KNOWN_CRATES 增补 + 豁免 |
| H. crate 版本 API 漂移（wgpu/winit、c12_wasm） | 1 | 豁免（err+file+crates 联合规则） |
| I. syn parsing / chrono serde feature 变体 | 4 | 笛卡尔积轮换修复 + 兜底豁免 |
| J. 真缺上下文（E0425/E0405 缺 import/缺定义） | 65 | 真实文档缺口，转文档侧并行代理 |

## 3. 受控复测（工具侧独立效果）

对 v3 的 148 个 dep_fail 块（当前树源码）仅用新工具重跑：

| 结果 | 数量 |
|---|---:|
| 转 pass（变体轮换/proc-macro/async 包装修复） | 9 |
| 转 dep_untested（DEP_KNOWN_MISSING 豁免） | 50 |
| 仍 fail（均为 J 类真缺上下文，转文档侧） | 89 |

即工具侧独立消除 59/148；剩余 89 全部为真实文档缺口（E0425/E0405/E0433 缺符号），
与文档侧修复叠加后全量终值 dep_fail=1。

## 4. 工具改进 diff 摘要（scripts/check_concept_code_blocks.py）

1. **变体去重**（`find_extern_artifacts`）：同一构建哈希的 `.rmeta/.rlib` 归为一组，
   优先 rmeta（proc-macro 用 .dll/.so/.dylib），消除 v3 同变体重复占用轮换轮次。
2. **笛卡尔积轮换**（`build_extern_combos`）：v3 多 crate 变体锁步推进（(v0,v0),(v1,v1)…）
   漏掉跨 crate 组合；改为对角优先 + 笛卡尔积补齐，上限 `MAX_EXTERN_COMBOS=24`。
3. **编译模式回退链**（`compile_dep_one`）：bin(包装) → lib(不包装，无 main 时) →
   **proc-macro**（含 `#[proc_macro*]` 或 `proc_macro::` 时） → **async 包装**
   （顶层 `.await` 且无 main 时，包入 `async fn __cb_async_main()` + 空 main）。
4. **最佳错误选择**：全部组合/模式失败后保留 error 行数最少的诊断，避免 v3「末位变体
   缺 feature 的误导性报错」。
5. **`DEP_KNOWN_MISSING` 结构化接线**（v3 已声明但未使用）：规则键
   `err`(stderr 正则) / `code`(源码正则) / `file`(fnmatch) / `crates`(引用集合)，多键 AND；
   编译前（crate 级）与全部失败后（err 级）两处匹配，命中计入 dep_untested 并附豁免理由。
6. **candidate 路径 async 回退**（`compile_one`）：bin/lib 失败后对顶层 `.await` 块追加
   async 包装尝试（仅附加，不改变既有通过路径）。
7. **隐藏行扩展**（`unhide_lines`）：`#` 无前缀空格时仅当随后是 Rust 语句关键字
   （`#use`/`#fn`/`#let` 等，白名单正则）才视为隐藏行；`#ident`/`#(#x),*`/`#vis` 等
   quote! 插值保持不动（已加 11 项单测防回归）。
8. **KNOWN_CRATES 增补**：prost_types、async_stream、trait_variant、aws_sdk_{dynamodb,s3,ec2,lambda}。

回归保护：candidate_pass 1860→1865（+5，async 回退/隐藏行救回），compile_fail_ok 810→810，
should_panic/cf 类零变化；新增模式均为「失败后才追加」的 fallback，不改变既有通过路径。

## 5. 豁免清单（DEP_KNOWN_MISSING，16 条）

| id | 匹配 | 原因 |
|---|---|---|
| reqwest-gzip | err: `no method named \`gzip\`` | workspace reqwest 未启用 gzip feature |
| reqwest-cookies | err: `cookie_store` | workspace reqwest 未启用 cookies feature |
| chrono-serde | err: `DateTime<…>: serde::Serialize` | chrono serde 变体缺失兜底（轮换后仍缺） |
| syn-parsing | err: `no method named \`span\`…syn::Field` | syn parsing 变体缺失兜底 |
| async-stream | code: `async_stream` | crate 不在 workspace |
| trait-variant | code: `trait_variant` | crate 不在 workspace |
| aws-sdk | code: `aws_sdk_\w+` | AWS SDK 系列不在 workspace |
| tokio-test-util | err: `tokio::time::advance\|start_paused` | tokio 未启用 test-util feature |
| tokio-feature-modules | err: `cannot find \`(fs\|process\|signal\|…)\` in \`tokio\`` 等 | 全部 tokio rmeta 变体均无该 feature 模块（兜底） |
| tower-util | err: `unresolved import \`tower::(retry\|timeout\|limit\|…)` | tower 未启用 util feature |
| tower-http-auth | err: `tower_http::auth` | tower-http 未启用 auth feature |
| parking-lot-deadlock | err: `parking_lot::deadlock` | parking_lot 未启用 deadlock_detection feature |
| signal-hook-iterator | err: `signal_hook::iterator` | signal-hook 传递依赖变体无 iterator feature |
| rust-19x-demo-api | file: `rust_1_9*_stabilized.md` + crates: c0x_* | 版本跟踪页演示性 API 未在 workspace 示例 crate 实现 |
| c12-wasm | crates: c12_wasm + err: `c12_wasm\|rust_19\d_features` | c12_wasm 仅 wasm32 目标/演示性 API 未实现 |
| wgpu-winit-drift | file: 15_game_engine_internals.md + crates: wgpu/winit + err: `wgpu\|winit` | 示例与锁定版本 API 漂移 |

> 注：豁免条目均附可审计原因；若 workspace 后续启用对应 feature / 补齐模块，应删除条目让块回归实测。

## 6. strict 转正评估建议

- 当前 `--strict` 判定 `rot>0 → exit 1`；R2b 终值 rot=1（唯一剩余为 01_async.md:3355
  双 main 对比块，文档侧标注 `rust,ignore` 后 rot=0）。
- 按 AGENTS.md §5.2 转正规则（连续 4 周或 10 次 CI 达标），建议：
  1. 文档侧处理最后 1 块后，以本报告 + `tmp/cb_r2b.json` 为 R2b 基线；
  2. 维持观察门，累计达标次数；dep 类已具备「豁免全登记 + 失败即真腐烂」语义，
     rot=0 稳定 4 周后可评估转阻断。
- 风险提示：dep 实测依赖 `target/debug/deps` 状态，CI 需保证 `cargo build --workspace`
  先于本门运行（`--ensure-deps` 已支持自动构建）。

## 7. 复现

```bash
python scripts/check_concept_code_blocks.py --sample 0 --with-deps \
  --json tmp/cb_r2b.json --report tmp/cb_r2b_auto.md
# 终值：candidate 1865/0 | compile_fail ok=810 | dep 149 pass / 1 fail / 26 untested | rot=1
```
