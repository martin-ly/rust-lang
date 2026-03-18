# 实践项目 05: 文本统计工具

> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 2小时

---

## 项目目标

创建一个类似wc的文本统计工具。

---

## 功能需求

- [ ] 统计行数、单词数、字符数
- [ ] 统计词频
- [ ] 查找最长行
- [ ] 支持多个文件

---

## 学习要点

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
