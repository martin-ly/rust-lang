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

- 实测块: 1405
- candidate: pass=299 fail=1
- compile_fail: ok=1100 unexpected_pass=0 wrong_code=0
- should_panic: pass=5 fail=0
- dep: pass=0 fail=0 untested(无 rmeta)=0
- timeout: 0
- **应过但失败/标注腐烂合计: 1**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/06_ecosystem/03_design_patterns/47_rust_design_and_architecture_patterns_semantic_atlas.md` | 935 | candidate | fail | error[E0425]: cannot find type `Error` in this scope<br>error[E0433]: cannot find module or crate `lexer` in this scope<br>error[E0433]: cannot find module or crate `parser` in this scope<br>error[E0433]: cannot find module or crate `codegen` in this scope<br>error: aborting due to 4 previous errors; 1 warning  |
