# 缓存

> **核心库**: moka, cached, mini-redis  
> **适用场景**: 内存缓存、LRU缓存、分布式缓存

---

## 📋 核心库

| 库 | 类型 | 特点 | 推荐度 |
|-----|------|------|--------|
| **moka** | 内存缓存 | 高性能 | ⭐⭐⭐⭐⭐ |
| **cached** | 宏驱动 | 易用 | ⭐⭐⭐⭐ |

---

## 🚀 moka

```rust
use moka::future::Cache;

#[tokio::main]
async fn main() {
    let cache: Cache<String, String> = Cache::builder()
        .max_capacity(10_000)
        .build();
    
    cache.insert("key".to_string(), "value".to_string()).await;
    
    let value = cache.get(&"key".to_string()).await;
    println!("{:?}", value);
}
```

---

## 📦 cached

```rust
use cached::proc_macro::cached;

#[cached]
fn fib(n: u64) -> u64 {
    if n <= 1 { n } else { fib(n-1) + fib(n-2) }
}

fn main() {
    println!("{}", fib(40));
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
