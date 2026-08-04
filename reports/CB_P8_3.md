# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 3053 |
| compile_fail（验证确实失败） | 1114 |
| should_panic（验证编译通过） | 5 |
| 伪代码/占位跳过 | 15 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 41 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 33 |
| 需依赖未测(未知 crate) | 92 |
| 依赖块(workspace 依赖,可测) | 238 |
| 无依赖编译候选 | 2947 |
| **合计** | **7573** |

## 实测统计

- 实测块: 4066
- candidate: pass=2927 fail=20
- compile_fail: ok=1111 unexpected_pass=0 wrong_code=3
- should_panic: pass=5 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 23**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/02_intermediate/00_traits/01_traits.md` | 3222 | candidate | fail | error: equality constraints are not yet supported in `where` clauses<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/07_type_theory_and_rust.md` | 189 | candidate | fail | error[E0658]: the `!` type is experimental<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/07_type_theory_and_rust.md` | 300 | candidate | fail | error[E0658]: the `!` type is experimental<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 144 | candidate | fail | error[E0425]: cannot find type `Duration` in this scope<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 467 | candidate | fail | error[E0425]: cannot find type `HashMap` in this scope<br>error[E0425]: cannot find type `HashMap` in this scope<br>error[E0425]: cannot find type `HashMap` in this scope<br>error: aborting due to 3 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 486 | candidate | fail | error: `self` parameter is only allowed in associated functions<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 640 | candidate | fail | error[E0425]: cannot find type `Config` in this scope<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 669 | candidate | fail | error: `self` parameter is only allowed in associated functions<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/52_performance_idioms.md` | 307 | candidate | fail | error[E0658]: use of unstable library feature `likely_unlikely`<br>error[E0658]: use of unstable library feature `likely_unlikely`<br>error[E0658]: use of unstable library feature `likely_unlikely`<br>error: aborting due to 3 previous errors; 1 warning emitted |
| `concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md` | 290 | candidate | fail | error[E0152]: found duplicate lang item `panic_impl`<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md` | 755 | candidate | fail | error[E0152]: found duplicate lang item `panic_impl`<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 163 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 189 | candidate | fail | error[E0405]: cannot find trait `OutputPin` in this scope<br>error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 286 | candidate | fail | error[E0277]: can't compare `SevenBitAddress` with `SevenBitAddress`<br>error[E0277]: the trait bound `SevenBitAddress: Copy` is not satisfied<br>error[E0277]: can't compare `TenBitAddress` with `TenBitAddress`<br>error[E0277]: the trait bound `TenBitAddress: Copy` is not satisfied<br>error: aborting due to 4 p |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 371 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 414 | candidate | fail | error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error |
| `concept/06_ecosystem/05_systems_and_embedded/42_interrupts_and_concurrency_on_bare_metal.md` | 207 | candidate | fail | error[E0425]: cannot find value `RCC` in this scope<br>error[E0425]: cannot find value `GPIOA` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/43_rust_safety_critical_systems.md` | 586 | candidate | fail | error: extern blocks must be unsafe<br>error[E0425]: cannot find type `DriverError` in this scope<br>error[E0433]: cannot find type `DriverError` in this scope<br>error: aborting due to 3 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/46_rtos_and_scheduling_in_rust.md` | 330 | candidate | fail | error[E0255]: the name `Future` is defined multiple times<br>error: aborting due to 1 previous error; 1 warning emitted |
| `concept/06_ecosystem/14_enterprise_architecture/14_data_intensive_patterns.md` | 224 | candidate | fail | error: lifetime may not live long enough<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/07_type_theory_and_rust.md` | 328 | compile_fail | cf_wrong_code | error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/07_type_theory_and_rust.md` | 345 | compile_fail | cf_wrong_code | error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/08_separation_logic_for_rust.md` | 351 | compile_fail | cf_wrong_code | error: aborting due to 1 previous error |
