# 概念文件扩展权威来源链接健康检查报告

> 生成时间: 2026-06-21
> 扫描范围: `concept/` 下 337 个 Markdown 文件的 `> **来源**: ...` 块
> 检查对象: 官方域名 + 生态 crate、学术/跨语言、平台集成等扩展权威域名

## 检查结果

| 指标 | 数值 |
|:---|:---|
| 检查链接数 | 224 |
| HTTP 200 | 224 |
| 404 / 异常 | 0 |

## 本次修复的真实 404 链接

| 原链接 | 修复后链接 | 涉及文件 |
|:---|:---|:---|
| `https://github.com/WebAssembly/WASI/blob/main/preview2/README.md` | `https://github.com/WebAssembly/WASI/blob/main/specifications/wasi-0.2.4/Overview.md` | `07_future/24_wasm_target_evolution.md` |
| `https://rustwasm.github.io/wasm-bindgen/` | `https://rustwasm.github.io/docs/wasm-bindgen/` | `05_comparative/08_rust_vs_javascript.md`, `05_comparative/15_rust_vs_typescript.md`, `06_ecosystem/11_webassembly.md`, `06_ecosystem/54_webassembly_advanced.md`, `07_future/28_rust_for_webassembly.md` |
| `https://rustwasm.github.io/wasm-bindgen/contributing/design.html` | `https://rustwasm.github.io/docs/wasm-bindgen/contributing/design/index.html` | `05_comparative/08_rust_vs_javascript.md` |
| `https://rustwasm.github.io/wasm-bindgen/contributing/design/js-objects.html` | `https://rustwasm.github.io/docs/wasm-bindgen/contributing/design/js-objects-in-rust.html` | `05_comparative/15_rust_vs_typescript.md` |
| `https://rustwasm.github.io/wasm-bindgen/reference/receiving-js-closures.html` | `https://rustwasm.github.io/docs/wasm-bindgen/reference/receiving-js-closures-in-rust.html` | `06_ecosystem/54_webassembly_advanced.md` |
| `https://rustwasm.github.io/wasm-bindgen/api/wasm_bindgen_futures/` | `https://docs.rs/wasm-bindgen-futures/latest/wasm_bindgen_futures/` | `05_comparative/15_rust_vs_typescript.md` |
| `https://www.chromium.org/developers/design-documents/rust/` | `https://www.chromium.org/chromium-os/developer-library/guides/rust/rust-on-cros/` | `06_ecosystem/48_industrial_case_studies.md`, `06_ecosystem/58_platform_rust_integration.md` |
| `https://source.android.com/docs/core/architecture/rust` | `https://security.googleblog.com/2021/05/integrating-rust-into-android-open.html` | `06_ecosystem/48_industrial_case_studies.md`, `06_ecosystem/58_platform_rust_integration.md` |

## 脚本改进

- `scripts/check_source_links_health.py` 与 `scripts/check_source_links_health_extended.py` 的请求头增加 `Accept`，避免 `crates.io`、`foundation.rust-lang.org` 等站点因缺少 `Accept` 头返回 403/404 误报。
- 新增 `scripts/fix_remaining_broken_links.py`，集中维护并批量修复剩余真实 404 链接映射。

## 覆盖率状态

- EN 标题: 337 / 337（100.0%）
- Summary: 337 / 337（100.0%）
- 来源链接: 337 / 337（100.0%）
- 代码块编译: 2118 / 2118 通过（100.0%）

## 说明

- 扩展权威域名包含 `docs.rs`、`crates.io`、`github.com`、`rustwasm.github.io`、`source.android.com`、`www.chromium.org`、`plv.mpi-sws.org` 等；这些来源在各自领域内被视为权威引用。
- 修复后官方与扩展权威来源链接均返回 200，无 404。
- 进一步将扫描范围扩大到 `concept/` 下**全部 Markdown 链接**（不限于 `来源:` 块），结果见 [`concept_links_health_report.md`](concept_links_health_report.md)。
