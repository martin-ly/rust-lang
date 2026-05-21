# 实践项目 08: 内存缓存系统

> **难度**: ⭐⭐ 进阶级
> **所需知识**: c05 (并发)
> **预计时间**: 4-5小时

---

## 项目目标
> **[来源: Rust Official Docs]**

创建一个线程安全的内存缓存系统。

---

## 功能需求
> **[来源: Rust Official Docs]**

- [ ] 键值存储
- [ ] TTL过期
- [ ] LRU淘汰
- [ ] 并发安全

---

## 学习要点
> **[来源: Rust Official Docs]**

### 并发安全缓存

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

struct Cache {
    data: Arc<RwLock<HashMap<String, String>>>,
}

impl Cache {
    fn get(&self, key: &str) -> Option<String> {
        self.data.read().unwrap().get(key).cloned()
    }

    fn set(&self, key: String, value: String) {
        self.data.write().unwrap().insert(key, value);
    }
}
```

---

## 参考实现

完整参考实现位于: `examples/cache-system/`
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
