

## 📊 目录

- [代码分析（Code Analysis）索引](#代码分析code-analysis索引)
  - [目的](#目的)
  - [工具](#工具)
  - [常用命令](#常用命令)
  - [相关条目](#相关条目)
  - [导航](#导航)


# 代码分析（Code Analysis）索引

## 目的

- 统一静态/动态分析工具入口，支撑质量与安全保障。

## 工具

- 静态：`clippy`、`cargo udeps`、`cargo deny`
- 符号/动态：`miri`、sanitizers（`asan/tsan/lsan`）
- 安全：`cargo audit`、`cargo geiger`

## 常用命令

```bash
cargo clippy -- -D warnings
cargo udeps
cargo deny check
```

## 相关条目

- 形式化工具：[`../05_formal/00_index.md`](../05_formal/00_index.md)
- 调试：[`../09_debugging/00_index.md`](../09_debugging/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
