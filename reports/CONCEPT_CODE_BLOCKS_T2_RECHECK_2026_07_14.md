# concept/ 代码块编译实测报告

## 分类统计

| 分类 | 数量 |
|---|---:|
| 标注跳过(ignore/no_run) | 1984 |
| compile_fail（验证确实失败） | 816 |
| 伪代码/占位跳过 | 11 |
| nightly-only(#![feature]) | 18 |
| no_std/no_main | 10 |
| 依赖环境不可用(嵌入式/wasm/验证工具) | 19 |
| 需依赖未测(未知 crate) | 85 |
| 依赖块(workspace 依赖,可测) | 175 |
| 无依赖编译候选 | 1876 |
| **合计** | **4994** |

## 实测统计

- 实测块: 2867
- candidate: pass=1876 fail=0
- compile_fail: ok=815 unexpected_pass=1 wrong_code=0
- should_panic: pass=0 fail=0
- dep: pass=149 fail=0 untested(无 rmeta)=26
- timeout: 0
- **应过但失败/标注腐烂合计: 1**

## 失败/腐烂清单

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/06_ecosystem/01_cargo/20_cargo_manifest_targets.md` | 187 | compile_fail | cf_unexpected_pass | compile_fail 块编译通过（标注腐烂或编译器已修复该诊断） |
