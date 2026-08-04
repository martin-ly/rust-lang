# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2999 |
| compile_fail（验证确实失败） | 1102 |
| should_panic（验证编译通过） | 5 |
| 伪代码/占位跳过 | 15 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 29 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 33 |
| 需依赖未测(未知 crate) | 92 |
| 依赖块(workspace 依赖,可测) | 235 |
| 无依赖编译候选 | 2889 |
| **合计** | **7434** |

## 实测统计

- 实测块: 3996
- candidate: pass=2870 fail=19
- compile_fail: ok=1101 unexpected_pass=1 wrong_code=0
- should_panic: pass=5 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 20**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/02_intermediate/00_traits/01_traits.md` | 3216 | candidate | fail | error: equality constraints are not yet supported in `where` clauses<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md` | 587 | candidate | fail | error[E0599]: no variant, associated function, or constant named `Unit` found for enum `Expr` in the current scope<br>error[E0599]: no variant, associated function, or constant named `Unit` found for enum `Expr` in the current scope<br>error[E0599]: no variant, associated function, or constant named `Unit |
| `concept/06_ecosystem/03_design_patterns/47_rust_design_and_architecture_patterns_semantic_atlas.md` | 935 | candidate | fail | error[E0425]: cannot find type `Error` in this scope<br>error[E0433]: cannot find module or crate `lexer` in this scope<br>error[E0433]: cannot find module or crate `parser` in this scope<br>error[E0433]: cannot find module or crate `codegen` in this scope<br>error: aborting due to 4 previous errors; 1 warning  |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 139 | candidate | fail | error[E0425]: cannot find type `Duration` in this scope<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 462 | candidate | fail | error[E0425]: cannot find type `HashMap` in this scope<br>error[E0425]: cannot find type `HashMap` in this scope<br>error[E0425]: cannot find type `HashMap` in this scope<br>error: aborting due to 3 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 481 | candidate | fail | error: `self` parameter is only allowed in associated functions<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 635 | candidate | fail | error[E0425]: cannot find type `Config` in this scope<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 664 | candidate | fail | error: `self` parameter is only allowed in associated functions<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md` | 254 | candidate | fail | error[E0152]: found duplicate lang item `panic_impl`<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md` | 719 | candidate | fail | error[E0152]: found duplicate lang item `panic_impl`<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 163 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 189 | candidate | fail | error[E0405]: cannot find trait `OutputPin` in this scope<br>error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 230 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error[E0405]: cannot find trait `ErrorType` in this scope<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 282 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[ |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 363 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 406 | candidate | fail | error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error |
| `concept/06_ecosystem/05_systems_and_embedded/42_interrupts_and_concurrency_on_bare_metal.md` | 207 | candidate | fail | error[E0425]: cannot find value `RCC` in this scope<br>error[E0425]: cannot find value `GPIOA` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/43_rust_safety_critical_systems.md` | 586 | candidate | fail | error: extern blocks must be unsafe<br>error[E0425]: cannot find type `DriverError` in this scope<br>error[E0433]: cannot find type `DriverError` in this scope<br>error: aborting due to 3 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/46_rtos_and_scheduling_in_rust.md` | 324 | candidate | fail | error[E0255]: the name `Future` is defined multiple times<br>error: aborting due to 1 previous error; 1 warning emitted |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 125 | compile_fail | cf_unexpected_pass | compile_fail 块编译通过（标注腐烂或编译器已修复该诊断） |
