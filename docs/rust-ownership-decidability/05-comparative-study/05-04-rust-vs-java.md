# Rust vs Java: 内存管理与并发模型对比

> **对比维度**: 内存安全、类型系统、并发模型、性能特征  
> **目标读者**: 有 Java 背景想了解 Rust 的开发者

---

## 目录

1. [内存管理对比](#1-内存管理对比)
2. [类型系统](#2-类型系统)
3. [并发模型](#3-并发模型)
4. [性能特征](#4-性能特征)
5. [生态系统](#5-生态系统)
6. [迁移指南](#6-迁移指南)

---

## 1. 内存管理对比

### 1.1 核心差异

| 特性 | Java | Rust |
|:---|:---|:---|
| **内存管理** | 垃圾回收 (GC) | 所有权系统 |
| **内存安全** | GC + 运行时检查 | 编译时保证 |
| **空值处理** | NullPointerException | Option<T> 类型 |
| **资源管理** | try-with-resources | RAII + Drop trait |

### 1.2 代码对比：资源管理

```java
// Java: try-with-resources
public void processFile(String path) throws IOException {
    try (BufferedReader reader = new BufferedReader(new FileReader(path))) {
        String line;
        while ((line = reader.readLine()) != null) {
            System.out.println(line);
        }
    } // 自动关闭
}
```

```rust
// Rust: RAII + 所有权
use std::fs::File;
use std::io::{BufRead, BufReader};

pub fn process_file(path: &str) -> std::io::Result<()> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    
    for line in reader.lines() {
        println!("{}", line?);
    }
    // file 在这里自动关闭（Drop）
    Ok(())
}
```

### 1.3 空值安全

```java
// Java: 运行时可能 NullPointerException
public String getName(User user) {
    return user.getProfile().getName(); // 可能 NPE
}

// Java 8+: Optional
public Optional<String> getNameSafe(User user) {
    return Optional.ofNullable(user)
        .map(User::getProfile)
        .map(Profile::getName);
}
```

```rust
// Rust: 编译时强制处理
pub fn get_name(user: &User) -> Option<&str> {
    user.profile.as_ref()?.name.as_deref()
}

// 或使用 match 显式处理
pub fn get_name_explicit(user: &User) -> &str {
    match &user.profile {
        Some(profile) => match &profile.name {
            Some(name) => name,
            None => "Unknown",
        },
        None => "Unknown",
    }
}
```

---

## 2. 类型系统

### 2.1 泛型对比

```java
// Java: 类型擦除，运行时丢失类型信息
public class Box<T> {
    private T value;
    public Box(T value) { this.value = value; }
    public T get() { return value; }
}

// 运行时：Box<String> 和 Box<Integer> 都是 Box
```

```rust
// Rust: 单态化，零成本抽象
pub struct Box<T> {
    value: T,
}

impl<T> Box<T> {
    pub fn new(value: T) -> Self {
        Self { value }
    }
    pub fn get(&self) -> &T {
        &self.value
    }
}

// 编译后为每种类型生成专门代码：Box<String>, Box<i32>
```

### 2.2 Trait vs Interface

```java
// Java: Interface
public interface Drawable {
    void draw();
    default void describe() {
        System.out.println("A drawable object");
    }
}

public class Circle implements Drawable {
    @Override
    public void draw() { /* ... */ }
}
```

```rust
// Rust: Trait
pub trait Drawable {
    fn draw(&self);
    fn describe(&self) {
        println!("A drawable object");
    }
}

pub struct Circle { /* ... */ }

impl Drawable for Circle {
    fn draw(&self) { /* ... */ }
}
```

**关键差异**: Rust trait 可以为现有类型实现（孤儿规则限制），Java interface 实现必须在类定义中。

### 2.3 代数数据类型

```java
// Java: 使用类层次结构
public abstract class Result<T, E> {
    public static class Ok<T, E> extends Result<T, E> {
        public final T value;
        public Ok(T value) { this.value = value; }
    }
    public static class Err<T, E> extends Result<T, E> {
        public final E error;
        public Err(E error) { this.error = error; }
    }
}
```

```rust
// Rust: 枚举直接支持
pub enum Result<T, E> {
    Ok(T),
    Err(E),
}

// 模式匹配
match result {
    Ok(value) => println!("Success: {}", value),
    Err(e) => println!("Error: {}", e),
}
```

---

## 3. 并发模型

### 3.1 线程安全对比

| 特性 | Java | Rust |
|:---|:---|:---|
| **线程创建** | `new Thread()` / ExecutorService | `std::thread::spawn` |
| **线程安全** | synchronized / volatile | Send + Sync trait |
| **数据共享** | 共享内存 + 锁 | 所有权转移或借用 |
| **消息传递** | BlockingQueue | Channel (std::sync::mpsc) |

### 3.2 线程安全代码对比

```java
// Java: 同步块
public class Counter {
    private int count = 0;
    private final Object lock = new Object();
    
    public void increment() {
        synchronized (lock) {
            count++;
        }
    }
    
    public int get() {
        synchronized (lock) {
            return count;
        }
    }
}
```

```rust
// Rust: 类型系统保证
use std::sync::{Arc, Mutex};

pub struct Counter {
    count: Mutex<i32>,
}

impl Counter {
    pub fn new() -> Self {
        Self { count: Mutex::new(0) }
    }
    
    pub fn increment(&self) {
        let mut count = self.count.lock().unwrap();
        *count += 1;
    }
    
    pub fn get(&self) -> i32 {
        *self.count.lock().unwrap()
    }
}

// 编译时检查：Counter 是 Send + Sync，可以跨线程共享
// Arc<Counter> 自动实现 Send + Sync
```

### 3.3 异步编程

```java
// Java: CompletableFuture
CompletableFuture<String> future = CompletableFuture
    .supplyAsync(() -> fetchData())
    .thenApply(data -> process(data))
    .thenCompose(result -> save(result));

String result = future.join();
```

```rust
// Rust: async/await
async fn workflow() -> Result<String, Error> {
    let data = fetch_data().await?;
    let result = process(data).await?;
    save(result).await
}

// 运行时执行
let result = tokio::runtime::Runtime::new()
    .unwrap()
    .block_on(workflow());
```

---

## 4. 性能特征

### 4.1 运行时开销对比

| 指标 | Java | Rust |
|:---|:---|:---|
| **启动时间** | 较慢 (JVM 启动) | 极快 (原生代码) |
| **内存占用** | 较大 (JVM + GC) | 较小 (无运行时) |
| **峰值性能** | 高 (JIT 优化) | 高 (LLVM 优化) |
| **可预测性** | GC 暂停 | 无暂停 |

### 4.2 零成本抽象

```java
// Java: 抽象有运行时成本
List<Integer> numbers = Arrays.asList(1, 2, 3, 4, 5);
int sum = numbers.stream()
    .filter(n -> n % 2 == 0)
    .mapToInt(Integer::intValue)
    .sum();
// Stream API 有对象装箱和方法调用开销
```

```rust
// Rust: 零成本抽象
let numbers = vec![1, 2, 3, 4, 5];
let sum: i32 = numbers
    .iter()
    .filter(|&&n| n % 2 == 0)
    .sum();
// 编译为与手写循环等价的机器码
```

---

## 5. 生态系统

### 5.1 包管理对比

| 特性 | Maven/Gradle | Cargo |
|:---|:---|:---|
| **配置文件** | pom.xml / build.gradle | Cargo.toml |
| **依赖解析** | 传递依赖 | 语义版本 + 锁文件 |
| **构建脚本** | 插件系统 | build.rs |
| **测试** | JUnit / TestNG | 内置测试框架 |

```toml
# Cargo.toml
[package]
name = "my-project"
version = "0.1.0"
edition = "2021"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1", features = ["full"] }

[dev-dependencies]
mockall = "0.12"
```

### 5.2 框架生态

| 领域 | Java | Rust |
|:---|:---|:---|
| Web | Spring Boot | Axum, Actix-web |
| ORM | Hibernate | Diesel, SeaORM |
| 序列化 | Jackson | Serde |
| 日志 | Log4j/SLF4J | Tracing, log |
| 测试 | JUnit | 内置 + tokio-test |

---

## 6. 迁移指南

### 6.1 常见模式映射

| Java 模式 | Rust 等价 |
|:---|:---|
| `class` | `struct` + `impl` |
| `interface` | `trait` |
| `extends` | trait 实现 |
| `final` | 默认不可变，或标记 `mut` |
| `static final` | `const` 或 `static` |
| `Optional<T>` | `Option<T>` |
| `Stream<T>` | `Iterator` |
| `CompletableFuture` | `async`/`await` |
| `synchronized` | `Mutex`, `RwLock` |

### 6.2 学习路径建议

```
Java 开发者学习 Rust:

Week 1: 所有权与借用
- 理解所有权转移
- 借用规则
- 生命周期基础

Week 2: 类型系统
- enum vs sealed class
- Option/Result vs Optional
- Trait vs Interface

Week 3: 错误处理
- Result<T, E> vs Exception
- ? 操作符
- panic vs RuntimeException

Week 4: 并发
- Send/Sync 标记
- Channel vs BlockingQueue
- async/await vs CompletableFuture
```

---

## 总结

| 维度 | Java 优势 | Rust 优势 |
|:---|:---|:---|
| **学习曲线** | 平缓，生态成熟 | 陡峭但回报高 |
| **运行时** | 跨平台 (JVM) | 高性能，小体积 |
| **内存安全** | GC 简化管理 | 编译时零成本保证 |
| **并发** | 成熟库生态 | 编译时数据竞争防护 |
| **领域** | 企业级应用 | 系统编程，嵌入式 |

**选择建议**:
- 企业级 Web 应用、大数据处理 → Java
- 系统编程、嵌入式、高性能服务 → Rust

---

*文档版本: 1.0.0*
