# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2992 |
| compile_fail（验证确实失败） | 1101 |
| should_panic（验证编译通过） | 4 |
| 伪代码/占位跳过 | 15 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 29 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 33 |
| 需依赖未测(未知 crate) | 92 |
| 依赖块(workspace 依赖,可测) | 235 |
| 无依赖编译候选 | 2880 |
| **合计** | **7416** |

## 实测统计

- 实测块: 1305
- candidate: pass=200 fail=0
- compile_fail: ok=1098 unexpected_pass=3 wrong_code=0
- should_panic: pass=4 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 3**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md` | 3159 | compile_fail | cf_unexpected_pass | compile_fail 块编译通过（标注腐烂或编译器已修复该诊断） |
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 125 | compile_fail | cf_unexpected_pass | compile_fail 块编译通过（标注腐烂或编译器已修复该诊断） |
| `concept/06_ecosystem/14_enterprise_architecture/11_event_driven_and_cqrs_patterns.md` | 580 | compile_fail | cf_unexpected_pass | compile_fail 块编译通过（标注腐烂或编译器已修复该诊断） |
