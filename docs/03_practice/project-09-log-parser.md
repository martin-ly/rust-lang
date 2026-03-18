# 实践项目 09: 日志分析器

> **难度**: ⭐⭐ 进阶级
> **所需知识**: c01-c06
> **预计时间**: 4-5小时

---

## 项目目标

创建高性能的日志分析工具。

---

## 功能需求

- [ ] 流式处理大文件
- [ ] 统计请求量
- [ ] 查找错误模式
- [ ] 生成报告

---

## 学习要点

### 流式处理

```rust
use std::io::{BufRead, BufReader};
use std::fs::File;

fn process_log_file(path: &str) -> std::io::Result<()> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    for line in reader.lines() {
        let line = line?;
        process_line(&line);
    }
    Ok(())
}
```

---

## 参考实现

完整参考实现位于: `examples/log-parser/`
