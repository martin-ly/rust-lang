

## 📊 目录

- [目的](#目的)
- [范畴](#范畴)
- [常用命令](#常用命令)
- [相关条目](#相关条目)
- [导航](#导航)


# 测试框架（Testing Frameworks）索引

## 目的

- 整理单元/集成/属性/端到端测试框架与惯用法。

## 范畴

- Rust 内建：`#[test]`、`cargo test`、工作区选择
- 属性测试：`proptest`、`quickcheck`
- 端到端：`cucumber`/`godog` 风格（如适配）
- 基准：`criterion`

## 常用命令

```bash
cargo test -p <crate>
cargo test -- --ignored
```

## 相关条目

- 构建工具：[`../03_build_tools/00_index.md`](../03_build_tools/00_index.md)
- 模糊测试：[`../04_fuzz/00_index.md`](../04_fuzz/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
