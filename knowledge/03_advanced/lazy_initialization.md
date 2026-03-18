# 延迟初始化 (Lazy Initialization)

> **版本**: Rust 1.94.0
> **特性**: `LazyCell`, `LazyLock`
> **权威来源**: [Rust RFC](https://rust-lang.github.io/rfcs/2788-lazy-cell.html), [PLDI 2025 Tree Borrows](https://pldi25.sigplan.org/)

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 使用 `LazyCell` 进行单线程延迟初始化
- [ ] 使用 `LazyLock` 进行线程安全延迟初始化
- [ ] 理解内部可变性模式
- [ ] 在实际场景中应用延迟初始化

## 📋 先决条件

- 理解所有权和借用
- 了解 `RefCell` 和内部可变性
- 了解 `Mutex` 和线程安全

## 🧠 核心概念

### 1. 为什么需要延迟初始化？

延迟初始化允许你在第一次访问时才计算值，适用于：

- 初始化开销大的资源
- 循环依赖的场景
- 全局配置的按需加载

### 2. LazyCell - 单线程延迟初始化

`LazyCell` 提供单线程环境下的延迟初始化，线程不安全但性能更高。

#### 2.1 基础用法

```rust
use std::cell::LazyCell;

fn main() {
    // 使用闭包定义初始化逻辑
    let lazy_value: LazyCell<String> = LazyCell::new(|| {
        println!("Initializing...");
        "Hello, Lazy!".to_string()
    });

    // 第一次访问时初始化
    println!("{}", *lazy_value); // 打印 "Initializing..." 然后 "Hello, Lazy!"

    // 后续访问直接使用已初始化的值
    println!("{}", *lazy_value); // 只打印 "Hello, Lazy!"
}
```

#### 2.2 实际应用：配置文件缓存

```rust
use std::cell::LazyCell;
use std::collections::HashMap;

struct AppConfig {
    settings: LazyCell<HashMap<String, String>>,
}

impl AppConfig {
    fn new() -> Self {
        Self {
            settings: LazyCell::new(|| {
                println!("Loading configuration...");
                let mut map = HashMap::new();
                map.insert("database_url".to_string(),
                    std::env::var("DATABASE_URL").unwrap_or_default());
                map.insert("api_key".to_string(),
                    std::env::var("API_KEY").unwrap_or_default());
                map
            }),
        }
    }

    fn get(&self, key: &str) -> Option<&String> {
        self.settings.get(key)
    }
}

fn main() {
    let config = AppConfig::new();

    // 第一次访问时加载配置
    println!("DB URL: {:?}", config.get("database_url"));

    // 后续访问使用缓存
    println!("API Key: {:?}", config.get("api_key"));
}
```

#### 2.3 实际应用：昂贵计算缓存

```rust
use std::cell::LazyCell;

struct DataProcessor {
    // 预编译的正则表达式
    pattern: LazyCell<regex::Regex>,
    // 预计算的查找表
    lookup_table: LazyCell<Vec<u32>>,
}

impl DataProcessor {
    fn new() -> Self {
        Self {
            pattern: LazyCell::new(|| {
                regex::Regex::new(r"\d{4}-\d{2}-\d{2}").unwrap()
            }),
            lookup_table: LazyCell::new(|| {
                (0..1000).map(|i| i * i).collect()
            }),
        }
    }

    fn process(&self, input: &str) -> Vec<String> {
        self.pattern
            .find_iter(input)
            .map(|m| m.as_str().to_string())
            .collect()
    }
}
```

### 3. LazyLock - 线程安全延迟初始化

`LazyLock` 提供线程安全的延迟初始化，使用 `std::sync::OnceLock` 实现。

#### 3.1 基础用法

```rust
use std::sync::LazyLock;

// 全局静态变量
static GLOBAL_CONFIG: LazyLock<Vec<String>> = LazyLock::new(|| {
    println!("Initializing global config...");
    vec!["config1".to_string(), "config2".to_string()]
});

fn main() {
    // 多线程安全访问
    std::thread::spawn(|| {
        println!("Thread 1: {:?}", *GLOBAL_CONFIG);
    });

    std::thread::spawn(|| {
        println!("Thread 2: {:?}", *GLOBAL_CONFIG);
    });

    // 主线程也访问
    println!("Main: {:?}", *GLOBAL_CONFIG);
}
```

#### 3.2 实际应用：数据库连接池

```rust
use std::sync::LazyLock;
use std::collections::HashMap;

// 线程安全的数据库连接池
static DB_POOL: LazyLock<HashMap<String, String>> = LazyLock::new(|| {
    println!("Initializing database pool...");
    let mut pool = HashMap::new();
    pool.insert("primary".to_string(), "postgres://localhost/db".to_string());
    pool.insert("replica".to_string(), "postgres://replica/db".to_string());
    pool
});

fn get_connection(name: &str) -> Option<&String> {
    DB_POOL.get(name)
}

fn main() {
    // 多个线程并发访问
    let handles: Vec<_> = (0..10)
        .map(|i| {
            std::thread::spawn(move || {
                let conn = get_connection("primary");
                println!("Thread {}: {:?}", i, conn);
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
```

#### 3.3 实际应用：HTTP 客户端

```rust
use std::sync::LazyLock;

// 全局 HTTP 客户端（复用连接）
static HTTP_CLIENT: LazyLock<reqwest::Client> = LazyLock::new(|| {
    reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(30))
        .pool_max_idle_per_host(10)
        .build()
        .expect("Failed to create HTTP client")
});

async fn fetch_data(url: &str) -> Result<String, reqwest::Error> {
    HTTP_CLIENT
        .get(url)
        .send()
        .await?
        .text()
        .await
}
```

### 4. LazyCell vs LazyLock 对比

| 特性 | `LazyCell<T>` | `LazyLock<T>` |
|------|--------------|---------------|
| 线程安全 | ❌ 否 | ✅ 是 |
| 性能 | 更高（无锁） | 稍低（使用锁） |
| 使用场景 | 单线程 | 多线程/全局变量 |
| 内部实现 | `RefCell` | `OnceLock` |
| 适用类型 | `!Sync` 类型 | `Sync` 类型 |

### 5. 与 OnceLock 的关系

`LazyLock` 是 `OnceLock` 的延迟初始化包装：

```rust
// 使用 OnceLock（手动检查）
static VALUE: OnceLock<String> = OnceLock::new();

fn get_value() -> &'static String {
    VALUE.get_or_init(|| {
        "expensive computation".to_string()
    })
}

// 使用 LazyLock（自动延迟）
static VALUE: LazyLock<String> = LazyLock::new(|| {
    "expensive computation".to_string()
});

// 直接解引用使用
fn use_value() {
    println!("{}", *VALUE);
}
```

## 💻 综合示例

### 示例：模块级缓存系统

```rust
use std::cell::LazyCell;
use std::sync::LazyLock;
use std::collections::HashMap;
use std::sync::RwLock;

// 模块私有缓存（单线程）
mod cache {
    use super::*;

    // 静态配置（线程安全，只读）
    pub static CONFIG: LazyLock<HashMap<String, String>> =
        LazyLock::new(|| {
            let mut map = HashMap::new();
            map.insert("version".to_string(), "1.0".to_string());
            map.insert("env".to_string(), "production".to_string());
            map
        });

    // 运行时缓存（线程安全，读写）
    pub static RUNTIME_CACHE: LazyLock<RwLock<HashMap<String, String>>> =
        LazyLock::new(|| RwLock::new(HashMap::new()));
}

// 请求级缓存（单线程）
struct RequestContext {
    user_data: LazyCell<UserData>,
    permissions: LazyCell<Vec<String>>,
}

struct UserData {
    id: u64,
    name: String,
}

impl RequestContext {
    fn new(user_id: u64) -> Self {
        Self {
            user_data: LazyCell::new(move || {
                println!("Loading user {} from database...", user_id);
                UserData {
                    id: user_id,
                    name: format!("User_{}", user_id),
                }
            }),
            permissions: LazyCell::new(|| {
                println!("Loading permissions...");
                vec!["read".to_string(), "write".to_string()]
            }),
        }
    }

    fn get_user(&self) -> &UserData {
        &*self.user_data
    }
}

fn main() {
    // 访问全局配置
    println!("Version: {:?}", cache::CONFIG.get("version"));

    // 修改运行时缓存
    {
        let mut cache = cache::RUNTIME_CACHE.write().unwrap();
        cache.insert("key".to_string(), "value".to_string());
    }

    // 创建请求上下文
    let ctx = RequestContext::new(42);
    println!("User: {}", ctx.get_user().name);
}
```

## ⚠️ 常见陷阱

| 错误 | 原因 | 解决方案 |
|------|------|----------|
| 在 `LazyLock` 中存储 `!Sync` 类型 | `LazyLock` 要求 `T: Sync` | 使用 `Mutex` 包装或使用 `LazyCell` |
| 初始化闭包 panic | 初始化失败后无法重试 | 确保初始化逻辑健壮 |
| 循环依赖 | `A` 初始化依赖 `B`，`B` 依赖 `A` | 重构代码，打破循环 |
| 闭包捕获环境导致生命周期问题 | 闭包生命周期不足 | 使用 `'static` 数据或重构 |

## 🎮 练习

### 练习 1：单例模式

使用 `LazyLock` 实现线程安全的单例配置管理器。

### 练习 2：缓存装饰器

创建一个宏或函数包装器，使用 `LazyCell` 缓存函数结果。

<details>
<summary>参考答案</summary>

```rust
use std::cell::LazyCell;
use std::collections::HashMap;
use std::hash::Hash;

struct Memoize<F, K, V> {
    func: F,
    cache: LazyCell<RefCell<HashMap<K, V>>>,
}

impl<F, K, V> Memoize<F, K, V>
where
    F: Fn(&K) -> V,
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn new(func: F) -> Self {
        Self {
            func,
            cache: LazyCell::new(|| RefCell::new(HashMap::new())),
        }
    }

    fn get(&self, key: &K) -> V {
        let mut cache = self.cache.borrow_mut();
        cache.entry(key.clone())
            .or_insert_with(|| (self.func)(key))
            .clone()
    }
}

fn expensive_computation(n: &u32) -> u32 {
    println!("Computing for {}...", n);
    std::thread::sleep(std::time::Duration::from_millis(100));
    n * n
}

fn main() {
    let memo = Memoize::new(expensive_computation);

    println!("{}", memo.get(&5)); // 计算
    println!("{}", memo.get(&5)); // 从缓存读取
}
```

</details>

## 📖 延伸阅读

- [RFC 2788: Lazy Cell](https://rust-lang.github.io/rfcs/2788-lazy-cell.html)
- [std::cell::LazyCell](https://doc.rust-lang.org/std/cell/struct.LazyCell.html)
- [std::sync::LazyLock](https://doc.rust-lang.org/std/sync/struct.LazyLock.html)

## ✅ 自我检测

1. `LazyCell` 和 `LazyLock` 的主要区别是什么？
2. 什么时候应该使用 `LazyLock` 而不是 `OnceLock`？
3. 延迟初始化可能带来什么问题？

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
