# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2623 |
| compile_fail（验证确实失败） | 1045 |
| 伪代码/占位跳过 | 15 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 10 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 31 |
| 需依赖未测(未知 crate) | 90 |
| 依赖块(workspace 依赖,可测) | 230 |
| 无依赖编译候选 | 2500 |
| **合计** | **6579** |

## 实测统计

- 实测块: 3775
- candidate: pass=2500 fail=0
- compile_fail: ok=1045 unexpected_pass=0 wrong_code=0
- should_panic: pass=0 fail=0
- dep: pass=205 fail=0 untested(无 rmeta)=25
- timeout: 0
- **应过但失败/标注腐烂合计: 0**

