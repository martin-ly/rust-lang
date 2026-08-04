# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2955 |
| compile_fail（验证确实失败） | 1089 |
| should_panic（验证编译通过） | 1 |
| 伪代码/占位跳过 | 15 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 27 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 33 |
| 需依赖未测(未知 crate) | 92 |
| 依赖块(workspace 依赖,可测) | 234 |
| 无依赖编译候选 | 2783 |
| **合计** | **7264** |

## 实测统计

- 实测块: 1390
- candidate: pass=297 fail=3
- compile_fail: ok=1089 unexpected_pass=0 wrong_code=0
- should_panic: pass=1 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 3**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/01_foundation/06_strings_and_text/02_strings_and_encoding.md` | 929 | candidate | fail | error[E0658]: use of unstable library feature `strip_circumfix`<br>error[E0658]: use of unstable library feature `strip_circumfix`<br>error: aborting due to 2 previous errors |
| `concept/06_ecosystem/03_design_patterns/44_configuration_management_patterns.md` | 413 | candidate | fail | error: environment variable `CARGO_PKG_VERSION` not defined at compile time<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 340 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
