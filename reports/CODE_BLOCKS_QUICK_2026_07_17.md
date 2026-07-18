# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2038 |
| compile_fail（验证确实失败） | 892 |
| 伪代码/占位跳过 | 12 |
| nightly-only(#![feature]) | 34 |
| no_std/no_main | 10 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 21 |
| 需依赖未测(未知 crate) | 85 |
| 依赖块(workspace 依赖,可测) | 176 |
| 无依赖编译候选 | 2020 |
| **合计** | **5288** |

## 实测统计

- 实测块: 1192
- candidate: pass=300 fail=0
- compile_fail: ok=892 unexpected_pass=0 wrong_code=0
- should_panic: pass=0 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 0**
