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

- 实测块: 1307
- candidate: pass=199 fail=1
- compile_fail: ok=1101 unexpected_pass=1 wrong_code=0
- should_panic: pass=5 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 2**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/06_ecosystem/05_systems_and_embedded/41_embedded_hal_and_mmio.md` | 163 | candidate | fail | error[E0405]: cannot find trait `ErrorType` in this scope<br>error: aborting due to 1 previous error |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 125 | compile_fail | cf_unexpected_pass | compile_fail 块编译通过（标注腐烂或编译器已修复该诊断） |
