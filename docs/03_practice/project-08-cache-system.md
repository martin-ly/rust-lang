# 实践项目 08: 内存缓存系统

> **难度**: ⭐⭐ 进阶级
> **所需知识**: c05 (并发)
> **预计时间**: 4-5小时

---

## 项目目标

创建一个线程安全的内存缓存系统。

---

## 功能需求

- [ ] 键值存储
- [ ] TTL过期
- [ ] LRU淘汰
- [ ] 并发安全

---

## 学习要点

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
