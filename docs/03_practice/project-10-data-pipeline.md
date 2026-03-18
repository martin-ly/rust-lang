# 实践项目 10: 数据处理管道

> **难度**: ⭐⭐ 进阶级
> **所需知识**: c04-c06
> **预计时间**: 5-6小时

---

## 项目目标

创建类似Unix管道的数据处理系统。

---

## 功能需求

- [ ] 链式处理器
- [ ] 过滤器
- [ ] 转换器
- [ ] 并行处理

---

## 学习要点

### 管道模式

```rust
trait Processor {
    fn process(&self, input: Vec<u8>) -> Vec<u8>;
}

struct Pipeline {
    stages: Vec<Box<dyn Processor>>,
}

impl Pipeline {
    fn run(&self, input: Vec<u8>) -> Vec<u8> {
        self.stages.iter().fold(input, |acc, stage| {
            stage.process(acc)
        })
    }
}
```

---

## 参考实现

完整参考实现位于: `examples/data-pipeline/`
