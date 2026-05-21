# 实践项目 05: 文本统计工具

> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 2小时

---

## 项目目标
> **[来源: Rust Official Docs]**

创建一个类似wc的文本统计工具。

---

## 功能需求
> **[来源: Rust Official Docs]**

- [ ] 统计行数、单词数、字符数
- [ ] 统计词频
- [ ] 查找最长行
- [ ] 支持多个文件

---

## 学习要点
> **[来源: Rust Official Docs]**

### 迭代器处理

```rust
fn count_words(text: &str) -> usize {
    text.split_whitespace().count()
}

fn count_lines(text: &str) -> usize {
    text.lines().count()
}
```

---

## 参考实现

完整参考实现位于: `examples/text-statistics/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)


---

- [README](./README.md)
