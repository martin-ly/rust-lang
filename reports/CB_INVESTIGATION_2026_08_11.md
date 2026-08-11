# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 3098 |
| compile_fail（验证确实失败） | 1156 |
| should_panic（验证编译通过） | 5 |
| 伪代码/占位跳过 | 15 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 41 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 33 |
| 需依赖未测(未知 crate) | 93 |
| 依赖块(workspace 依赖,可测) | 237 |
| 无依赖编译候选 | 3057 |
| **合计** | **7770** |

## 实测统计

- 实测块: 4218
- candidate: pass=3036 fail=21
- compile_fail: ok=1156 unexpected_pass=0 wrong_code=0
- should_panic: pass=5 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 21**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/02_intermediate/00_traits/01_traits.md` | 3309 | candidate | fail | error: equality constraints are not yet supported in `where` clauses<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/10_category_theory_and_rust.md` | 124 | candidate | fail | error[E0382]: use of moved value: `c`<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/10_category_theory_and_rust.md` | 357 | candidate | fail | error[E0562]: `impl Trait` is not allowed in the return type of `Fn` trait bounds<br>error[E0562]: `impl Trait` is not allowed in the return type of `Fn` trait bounds<br>error: aborting due to 2 previous errors |
| `concept/04_formal/11_computational_models/13_session_types_and_rust_channels.md` | 223 | candidate | fail | error[E0425]: cannot find type `Sender` in this scope<br>error[E0425]: cannot find type `Receiver` in this scope<br>error: aborting due to 2 previous errors; 2 warnings emitted |
| `concept/04_formal/11_computational_models/13_session_types_and_rust_channels.md` | 339 | candidate | fail | error[E0425]: cannot find type `Sender` in this scope<br>error[E0425]: cannot find type `Sender` in this scope<br>error[E0425]: cannot find type `Sender` in this scope<br>error: aborting due to 3 previous errors; 2 warnings emitted |
| `concept/04_formal/11_computational_models/14_effect_handlers_and_rust_limited_effects.md` | 326 | candidate | fail | error[E0515]: cannot return value referencing temporary value<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/17_aeneas_verification_pipeline.md` | 105 | candidate | fail | error[E0425]: cannot find value `v` in this scope<br>error: aborting due to 1 previous error |
| `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/02_cqrs_event_sourcing.md` | 141 | candidate | fail | error[E0425]: cannot find type `HashMap` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 144 | candidate | fail | error[E0425]: cannot find type `Duration` in this scope<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 467 | candidate | fail | error[E0425]: cannot find type `HashMap` in this scope<br>error[E0425]: cannot find type `HashMap` in this scope<br>error[E0425]: cannot find type `HashMap` in this scope<br>error: aborting due to 3 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 646 | candidate | fail | error[E0425]: cannot find type `Config` in this scope<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 675 | candidate | fail | error: `self` parameter is only allowed in associated functions<br>error[E0425]: cannot find type `Duration` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md` | 290 | candidate | fail | error[E0152]: found duplicate lang item `panic_impl`<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md` | 755 | candidate | fail | error[E0152]: found duplicate lang item `panic_impl`<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 163 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 189 | candidate | fail | error[E0405]: cannot find trait `OutputPin` in this scope<br>error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 373 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 416 | candidate | fail | error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error[E0220]: associated type `Error` not found for `Self`<br>error |
| `concept/06_ecosystem/05_systems_and_embedded/42_interrupts_and_concurrency_on_bare_metal.md` | 207 | candidate | fail | error[E0425]: cannot find value `RCC` in this scope<br>error[E0425]: cannot find value `GPIOA` in this scope<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/43_rust_safety_critical_systems.md` | 587 | candidate | fail | error: extern blocks must be unsafe<br>error[E0425]: cannot find type `DriverError` in this scope<br>error[E0433]: cannot find type `DriverError` in this scope<br>error: aborting due to 3 previous errors |
| `concept/06_ecosystem/05_systems_and_embedded/46_rtos_and_scheduling_in_rust.md` | 330 | candidate | fail | error[E0255]: the name `Future` is defined multiple times<br>error: aborting due to 1 previous error; 1 warning emitted |
