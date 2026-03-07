# Singleton Pattern in Rust

> **设计模式**: 创建型模式
> **难度**: 🟡 中等
> **应用场景**: 全局唯一实例管理

---

## 概念

单例模式确保一个类只有一个实例，并提供一个全局访问点。在 Rust 中，由于所有权系统的存在，单例模式的实现与其他语言有所不同。

---

## Rust 实现方式

### 方式一: `std::sync::OnceLock` (推荐)

Rust 1.70+ 标准库提供的线程安全单例：

```rust
use std::sync::OnceLock;

pub struct Config {
    pub database_url: String,
    pub max_connections: u32,
}

impl Config {
    fn new() -> Self {
        Self {
            database_url: std::env::var("DATABASE_URL")
                .unwrap_or_else(|_| "postgres://localhost".to_string()),
            max_connections: 10,
        }
    }
}

// 全局单例
static CONFIG: OnceLock<Config> = OnceLock::new();

pub fn get_config() -> &'static Config {
    CONFIG.get_or_init(Config::new)
}

// 使用示例
fn main() {
    let config1 = get_config();
    let config2 = get_config();

    assert!(std::ptr::eq(config1, config2)); // 同一实例
    println!("Database URL: {}", config1.database_url);
}
```

### 方式二: `lazy_static` (传统方式)

```rust
use lazy_static::lazy_static;
use std::sync::Mutex;

lazy_static! {
    static ref COUNTER: Mutex<u64> = Mutex::new(0);
}

pub fn increment() -> u64 {
    let mut counter = COUNTER.lock().unwrap();
    *counter += 1;
    *counter
}
```

### 方式三: 线程安全的单例结构体

```rust
use std::sync::{Arc, Mutex, OnceLock};

pub struct DatabasePool {
    connections: Vec<Connection>,
}

impl DatabasePool {
    fn new() -> Self {
        Self {
            connections: (0..10).map(|_| Connection::new()).collect(),
        }
    }
}

pub struct Connection;

impl Connection {
    fn new() -> Self {
        Connection
    }
}

// 全局单例
static POOL: OnceLock<Mutex<DatabasePool>> = OnceLock::new();

pub fn get_pool() -> &'static Mutex<DatabasePool> {
    POOL.get_or_init(|| Mutex::new(DatabasePool::new()))
}

pub fn with_connection<F, R>(f: F) -> R
where
    F: FnOnce(&mut Connection) -> R,
{
    let mut pool = get_pool().lock().unwrap();
    f(&mut pool.connections[0])
}
```

---

## 形式化分析

### 不变量 (Invariant)

```
∀t: 全局范围内 ∥{instance}∥ = 1
```

### 线程安全性证明

```
Theorem SINGLETON_THREAD_SAFE:
  ∀t1, t2: thread,
  get_instance()@t1 = get_instance()@t2 ⟹
  returns same memory location

Proof:
  1. OnceLock::get_or_init 使用底层原子操作
  2. 初始化 happens-before 任何读取
  3. 由 std::sync::Once 保证仅执行一次
  ∴ 线程安全
```

---

## 对比: Rust vs 其他语言

| 特性 | Rust | Java | C++ |
|------|------|------|-----|
| 线程安全 | ✅ 编译期保证 | ⚠️ 需 synchronized | ⚠️ 需手动处理 |
| 延迟初始化 | ✅ OnceLock | ⚠️ 复杂 | ✅ C++11静态变量 |
| 性能 | 零成本抽象 | 有锁开销 | 依赖实现 |

---

## 最佳实践

1. **优先使用 `OnceLock`** - 标准库支持，无需外部依赖
2. **避免全局可变状态** - 考虑使用 `RwLock` 或消息传递
3. **测试友好** - 提供重置机制用于测试

```rust
#[cfg(test)]
impl Config {
    pub fn reset_for_testing() {
        // 测试时重新初始化
        unsafe { CONFIG.take() };
    }
}
```

---

## 相关模式

- **Factory**: 单例工厂
- **Builder**: 构建复杂单例
