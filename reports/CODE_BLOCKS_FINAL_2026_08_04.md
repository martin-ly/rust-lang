# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 2999 |
| compile_fail（验证确实失败） | 1100 |
| should_panic（验证编译通过） | 5 |
| 伪代码/占位跳过 | 15 |
| nightly-only(#![feature]) | 35 |
| no_std/no_main | 29 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 33 |
| 需依赖未测(未知 crate) | 92 |
| 依赖块(workspace 依赖,可测) | 235 |
| 无依赖编译候选 | 2881 |
| **合计** | **7424** |

## 实测统计

- 实测块: 1205
- candidate: pass=100 fail=0
- compile_fail: ok=1100 unexpected_pass=0 wrong_code=0
- should_panic: pass=5 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 0**
