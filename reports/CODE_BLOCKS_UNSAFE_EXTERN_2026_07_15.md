# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2007 |
| compile_fail（验证确实失败） | 883 |
| 伪代码/占位跳过 | 11 |
| nightly-only(#![feature]) | 18 |
| no_std/no_main | 10 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 20 |
| 需依赖未测(未知 crate) | 85 |
| 依赖块(workspace 依赖,可测) | 175 |
| 无依赖编译候选 | 1958 |
| **合计** | **5167** |

## 实测统计

- 实测块: 1183
- candidate: pass=298 fail=2
- compile_fail: ok=880 unexpected_pass=0 wrong_code=3
- should_panic: pass=0 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 5**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/01_foundation/04_control_flow/03_let_chains.md` | 204 | candidate | fail | error[E0425]: cannot find value `opt` in this scope<br>error[E0425]: cannot find value `body` in this scope<br>error[E0425]: cannot find function `f` in this scope<br>error: aborting due to 3 previous errors |
| `concept/02_intermediate/01_generics/05_const_generics_and_trait_objects.md` | 141 | candidate | fail | error[E0425]: cannot find type `Buf16` in this scope<br>error[E0425]: cannot find type `Buf32` in this scope<br>error[E0425]: cannot find type `Buf64` in this scope<br>error: aborting due to 3 previous errors |
| `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` | 226 | compile_fail | cf_wrong_code | error: aborting due to 1 previous error |
| `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` | 277 | compile_fail | cf_wrong_code | error: aborting due to 1 previous error |
| `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` | 342 | compile_fail | cf_wrong_code | error: aborting due to 1 previous error |
