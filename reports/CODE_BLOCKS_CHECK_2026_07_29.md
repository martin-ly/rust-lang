# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2173 |
| compile_fail（验证确实失败） | 915 |
| 伪代码/占位跳过 | 14 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 10 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 21 |
| 需依赖未测(未知 crate) | 86 |
| 依赖块(workspace 依赖,可测) | 185 |
| 无依赖编译候选 | 2138 |
| **合计** | **5577** |

## 实测统计

- 实测块: 1215
- candidate: pass=299 fail=1
- compile_fail: ok=913 unexpected_pass=1 wrong_code=1
- should_panic: pass=0 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 3**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md` | 563 | candidate | fail | error[E0284]: type annotations needed<br>error: aborting due to 1 previous error |
| `concept/04_formal/11_computational_models/04_mathematical_functions_of_computation.md` | 335 | compile_fail | cf_wrong_code | error[E0631]: type mismatch in closure arguments<br>error: aborting due to 2 previous errors |
| `concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md` | 149 | compile_fail | cf_unexpected_pass | compile_fail 块编译通过（标注腐烂或编译器已修复该诊断） |
