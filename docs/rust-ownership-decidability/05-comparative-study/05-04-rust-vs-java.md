# Rust vs Java: 内存管理、类型系统与并发模型深度对比

> **对比维度**: 内存安全、类型系统、并发模型、性能特征、运行时特性
> **目标读者**: 有 Java 背景想了解 Rust 的开发者，技术决策者
> **文档版本**: 2.0.0 (L2+ 深度)

---

## 目录

- [Rust vs Java: 内存管理、类型系统与并发模型深度对比](#rust-vs-java-内存管理类型系统与并发模型深度对比)
  - [目录](#目录)
  - [1. 执行摘要](#1-执行摘要)
  - [2. 语言设计哲学对比](#2-语言设计哲学对比)
    - [2.1 设计目标](#21-设计目标)
    - [2.2 执行模型](#22-执行模型)
  - [3. 内存管理对比](#3-内存管理对比)
    - [3.1 所有权 vs 垃圾回收](#31-所有权-vs-垃圾回收)
    - [3.2 内存安全保证](#32-内存安全保证)
    - [3.3 资源管理对比](#33-资源管理对比)
    - [3.4 内存布局与缓存](#34-内存布局与缓存)
  - [4. 类型系统对比](#4-类型系统对比)
    - [4.1 类型系统概览](#41-类型系统概览)
    - [4.2 泛型实现对比](#42-泛型实现对比)
    - [4.3 Trait vs Interface](#43-trait-vs-interface)
    - [4.4 代数数据类型](#44-代数数据类型)
    - [4.5 空值安全](#45-空值安全)
  - [5. 并发模型对比](#5-并发模型对比)
    - [5.1 线程模型对比](#51-线程模型对比)
    - [5.2 内存模型对比](#52-内存模型对比)
    - [5.3 数据竞争防护](#53-数据竞争防护)
    - [5.4 异步编程对比](#54-异步编程对比)
  - [6. 错误处理对比](#6-错误处理对比)
    - [6.1 异常 vs Result](#61-异常-vs-result)
    - [6.2 错误传播](#62-错误传播)
  - [7. 性能特征对比](#7-性能特征对比)
    - [7.1 运行时开销](#71-运行时开销)
    - [7.2 启动性能](#72-启动性能)
    - [7.3 零成本抽象](#73-零成本抽象)
  - [8. 代码示例对比](#8-代码示例对比)
    - [8.1 集合操作](#81-集合操作)
    - [8.2 文件处理](#82-文件处理)
    - [8.3 并发计数器](#83-并发计数器)
    - [8.4 REST API 服务](#84-rest-api-服务)
  - [9. 生态系统对比](#9-生态系统对比)
    - [9.1 构建工具](#91-构建工具)
    - [9.2 框架生态](#92-框架生态)
    - [9.3 部署运维](#93-部署运维)
  - [10. 适用场景分析](#10-适用场景分析)
  - [11. 迁移指南](#11-迁移指南)
    - [Java → Rust 思维转换](#java--rust-思维转换)
  - [总结](#总结)
  - [参考文献](#参考文献)

---

## 1. 执行摘要

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Rust vs Java 核心对比                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  维度                  Rust                        Java                      │
│  ──────────────────────────────────────────────────────────────────────    │
│                                                                             │
│  执行模型              原生编译 (AOT)            JVM 字节码 + JIT            │
│                       直接运行机器码             需要 JVM 运行时            │
│                                                                             │
│  内存管理              所有权系统                  垃圾回收 (GC)             │
│                       编译期确定                 运行时自动                 │
│                       无 GC 暂停                GC 调优复杂                 │
│                                                                             │
│  内存安全              编译期保证                  GC + 运行时检查           │
│                       零成本保证                 有运行时开销               │
│                                                                             │
│  类型系统              单态化泛型                  类型擦除                  │
│                       零成本抽象                 装箱/拆箱开销              │
│                                                                             │
│  并发安全              Send/Sync 编译期           synchronized/volatile      │
│                       数据竞争编译期阻止          运行时检测                │
│                                                                             │
│  启动时间              < 1 ms                    数百 ms ~ 数秒             │
│  内存占用              MB 级别                   数十 MB ~ 数百 MB          │
│  峰值性能              高                         高 (JIT 预热后)            │
│                                                                             │
│  适用场景                                                                  │
│  ├── Rust: 系统编程、嵌入式、实时系统、CLI 工具、WebAssembly                │
│  └── Java: 企业应用、大数据、Android、长期运行的服务端应用                   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. 语言设计哲学对比

### 2.1 设计目标

| 维度 | Rust | Java |
|-----|------|------|
| **首要目标** | 安全 + 性能 | 可移植性 + 生产力 |
| **抽象成本** | 零成本 | 运行时成本 |
| **内存管理** | 编译期确定 | 运行时管理 |
| **平台依赖** | 编译到目标平台 | 依赖 JVM |
| **向后兼容** | 严格 (Edition 系统) | 非常严格 |

**Rust 设计哲学:**

```rust
// Rust: 编译器做尽可能多工作
// 编译期检查确保运行时安全

fn safe_operations() -> Result<(), Box<dyn std::error::Error>> {
    // 所有权系统确保：
    // 1. 无空指针解引用
    // 2. 无悬垂引用
    // 3. 无数据竞争
    // 4. 无缓冲区溢出

    let data = std::fs::read_to_string("file.txt")?;
    let lines: Vec<&str> = data.lines().collect();

    for line in &lines {
        process(line)?;
    }

    Ok(())
}  // 所有资源自动释放

fn process(line: &str) -> Result<(), std::io::Error> {
    // 处理逻辑
    Ok(())
}
```

**Java 设计哲学:**

```java
// Java: 运行时做工作，开发期简单
// WORA (Write Once, Run Anywhere)

public void safeOperations() throws IOException {
    // JVM 提供：
    // 1. 字节码验证
    // 2. 边界检查
    // 3. 空指针检查 (运行时)
    // 4. 垃圾回收

    List<String> lines = Files.readAllLines(Path.of("file.txt"));

    for (String line : lines) {
        process(line);
    }

    // lines 在 GC 时回收
}

private void process(String line) {
    // 处理逻辑
}
```

### 2.2 执行模型

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                         执行模型对比                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Rust 执行流程                                                               │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐   ┌─────────────┐  │
│  │   源代码      │ → │   编译器      │ → │   LLVM        │ → │  机器码      │  │
│  │  (.rs)       │   │  (类型检查)   │   │  (优化)       │   │  (二进制)    │  │
│  └──────────────┘   └──────────────┘   └──────────────┘   └─────────────┘  │
│                              ↑                                              │
│                        借用检查器在此工作                                   │
│                                                                             │
│  运行时：直接执行，无 VM 开销                                               │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  Java 执行流程                                                               │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐   ┌─────────────┐  │
│  │   源代码      │ → │   编译器      │ → │   字节码      │ → │   JVM        │  │
│  │  (.java)     │   │  (javac)     │   │  (.class)    │   │              │  │
│  └──────────────┘   └──────────────┘   └──────────────┘   └─────────────┘  │
│                                                               │             │
│                                                               ▼             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  JVM 运行时                                                          │   │
│  │   ├─ 类加载器                                                        │   │
│  │   ├─ 字节码验证器                                                    │   │
│  │   ├─ 解释器 / JIT 编译器                                             │   │
│  │   ├─ 垃圾回收器                                                      │   │
│  │   └─ 内存管理                                                        │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. 内存管理对比

### 3.1 所有权 vs 垃圾回收

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                       内存管理模型深度对比                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Rust 所有权系统                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                     │   │
│  │  栈内存：自动管理，函数返回时释放                                       │   │
│  │  堆内存：所有权跟踪，所有者离开作用域时释放                              │   │
│  │                                                                     │   │
│  │  fn process() {                                                     │   │
│  │      let s = String::from("hello");  // 堆分配                        │   │
│  │      let t = s;                      // 所有权转移                   │   │
│  │      // s 不再可用                                                   │   │
│  │      use(t);                         // 使用 t                       │   │
│  │  }  // t 在这里 drop，堆内存释放                                       │   │
│  │                                                                     │   │
│  │  特点：                                                             │   │
│  │   ✓ 编译期确定内存释放时机                                            │   │
│  │   ✓ 无运行时 GC 开销                                                  │   │
│  │   ✓ 可预测的内存使用                                                  │   │
│  │   ✗ 学习曲线陡峭                                                      │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Java 垃圾回收                                                               │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                     │   │
│  │  堆内存：GC 自动管理                                                  │   │
│  │  对象存活判定：可达性分析                                             │   │
│  │                                                                     │   │
│  │  void process() {                                                   │   │
│  │      String s = new String("hello");  // 堆分配                      │   │
│  │      String t = s;                    // 引用复制                    │   │
│  │      // s 和 t 都可用                                                │   │
│  │      use(t);                                                        │   │
│  │  }  // s 和 t 离开作用域，但对象不一定立即回收                          │   │
│  │                                                                     │   │
│  │  特点：                                                             │   │
│  │   ✓ 程序员无需管理内存                                                │   │
│  │   ✓ 简化开发                                                          │   │
│  │   ✗ GC 暂停 (STW)                                                     │   │
│  │   ✗ 内存开销较大                                                      │   │
│  │   ✗ 调优复杂                                                          │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 内存安全保证

| 安全问题 | Rust (编译期) | Java (运行时) |
|---------|--------------|---------------|
| **NullPointerException** | ❌ 编译错误 (Option) | ⚠️ 运行时抛出 |
| **悬垂指针** | ❌ 编译错误 | ✅ GC 防止 |
| **Use-after-free** | ❌ 编译错误 | ✅ GC 防止 |
| **缓冲区溢出** | ✅ 边界检查 | ✅ 数组边界检查 |
| **数据竞争** | ❌ 编译错误 (Send/Sync) | ⚠️ 运行时检测 |
| **内存泄漏** | ⚠️ 可能 (循环引用) | ⚠️ 可能 (对象引用) |
| **整数溢出** | ✅ Debug panic / Release wrap | ❌ 静默回绕 |

**Java 空指针问题:**

```java
public class NullPointerExample {
    public String getName(User user) {
        // 运行时可能 NullPointerException
        return user.getProfile().getName();
    }

    // 需要显式检查
    public String getNameSafe(User user) {
        if (user == null || user.getProfile() == null) {
            return "Unknown";
        }
        return user.getProfile().getName();
    }

    // Java 8+ Optional
    public Optional<String> getNameOptional(User user) {
        return Optional.ofNullable(user)
            .map(User::getProfile)
            .map(Profile::getName);
    }
}
```

**Rust 空值安全:**

```rust
pub struct User {
    profile: Option<Profile>,
}

pub struct Profile {
    name: Option<String>,
}

impl User {
    // 返回 Option，强制调用者处理
    pub fn get_name(&self) -> Option<&str> {
        self.profile.as_ref()?.name.as_deref()
    }

    // 提供默认值
    pub fn get_name_or_default(&self) -> &str {
        self.get_name().unwrap_or("Unknown")
    }
}

// 使用
fn use_user(user: &User) {
    // 编译错误！必须处理 None
    // let name = user.get_name();
    // println!("{}", name);  // 错误

    // 正确方式
    match user.get_name() {
        Some(name) => println!("Name: {}", name),
        None => println!("No name"),
    }

    // 或使用默认值
    println!("Name: {}", user.get_name_or_default());
}
```

### 3.3 资源管理对比

**Java try-with-resources:**

```java
import java.io.*;
import java.sql.*;

public class ResourceManagement {

    public void processFile(String path) throws IOException {
        // try-with-resources 自动关闭
        try (BufferedReader reader = new BufferedReader(new FileReader(path));
             BufferedWriter writer = new BufferedWriter(new FileWriter("output.txt"))) {

            String line;
            while ((line = reader.readLine()) != null) {
                writer.write(line.toUpperCase());
                writer.newLine();
            }

        } // 自动调用 close()
    }

    public void databaseOperation() throws SQLException {
        try (Connection conn = DriverManager.getConnection("jdbc:mysql://localhost/test");
             PreparedStatement stmt = conn.prepareStatement("SELECT * FROM users");
             ResultSet rs = stmt.executeQuery()) {

            while (rs.next()) {
                System.out.println(rs.getString("name"));
            }
        }
    }
}
```

**Rust RAII:**

```rust
use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};

pub fn process_file(path: &str) -> io::Result<()> {
    let input = File::open(path)?;
    let output = File::create("output.txt")?;

    let reader = BufReader::new(input);
    let mut writer = BufWriter::new(output);

    for line in reader.lines() {
        let line = line?;
        writeln!(writer, "{}", line.to_uppercase())?;
    }

    // 所有资源在这里自动 drop (逆序)
    // 1. writer flush 并关闭
    // 2. reader 关闭
    // 3. output 关闭
    // 4. input 关闭
    Ok(())
}

// 自定义 RAII
tempfile::TempDir

pub fn temp_operations() -> io::Result<()> {
    let temp_dir = tempfile::tempdir()?;

    let file_path = temp_dir.path().join("temp.txt");
    std::fs::write(&file_path, "temporary data")?;

    // 使用临时文件
    let content = std::fs::read_to_string(&file_path)?;
    println!("{}", content);

    Ok(())  // temp_dir 在这里自动删除
}
```

### 3.4 内存布局与缓存

**Java 内存布局:**

```java
// Java 对象头开销
// Object header: 12 bytes (64-bit JVM, compressed oops)
// Array header: 16 bytes

public class MemoryLayout {
    // 对象布局 (假设 64-bit JVM):
    // [Object Header: 12 bytes]
    // [int x: 4 bytes]
    // [int y: 4 bytes]
    // [reference to name: 4 bytes]
    // [padding: 4 bytes]  // 对齐到 8 字节
    // Total: 32 bytes (不包括 String 对象)

    private int x;
    private int y;
    private String name;

    // 数组布局:
    // [Array Header: 16 bytes]
    // [length: 4 bytes]
    // [padding: 4 bytes]
    // [elements...]
}

// 缓存不友好：对象数组是引用数组
Object[] objects = new Object[1000];  // 每个元素是指针
```

**Rust 内存布局控制:**

```rust
// Rust 可以精确控制内存布局

// 默认布局 (可能与 C 不同)
struct Point {
    x: i32,  // 4 bytes
    y: i32,  // 4 bytes
}
// Total: 8 bytes, 无填充

// C 兼容布局
#[repr(C)]
struct CPoint {
    x: i32,
    y: i32,
}

// 无填充布局
#[repr(packed)]
struct Packed {
    a: u8,   // 1 byte
    b: u32,  // 4 bytes (通常填充 3 bytes)
}
// Total: 5 bytes, 无填充

// 缓存友好：数组直接存储值
let points: [Point; 1000] = [Point { x: 0, y: 0 }; 1000];
// 连续内存：points[0] 和 points[1] 相邻

// 零大小类型
struct ZeroSized;
assert_eq!(std::mem::size_of::<ZeroSized>(), 0);
```

---

## 4. 类型系统对比

### 4.1 类型系统概览

| 特性 | Rust | Java |
|-----|------|------|
| **类型检查** | 编译期，严格 | 编译期 + 运行时 |
| **类型推断** | 强 (Hindley-Milner) | 局部 (var) |
| **泛型** | 单态化 | 类型擦除 |
| **协变/逆变** | 生命周期相关 | 通配符 |
| **类型别名** | type | 无 (interface 模拟) |

### 4.2 泛型实现对比

**Java 类型擦除:**

```java
// Java 泛型在运行时被擦除
public class GenericExample {

    // 编译后：public static void print(Object item)
    public static <T> void print(T item) {
        System.out.println(item);
    }

    // 运行时无法区分
    public static void main(String[] args) {
        List<String> strings = new ArrayList<>();
        List<Integer> integers = new ArrayList<>();

        // 运行时两者都是 ArrayList
        System.out.println(strings.getClass() == integers.getClass());  // true

        // 无法获取泛型参数类型
        // strings.getClass().getGenericSuperclass() 可以获取声明信息
    }
}

// 基本类型装箱
public void boxing() {
    List<Integer> list = new ArrayList<>();
    list.add(42);  // 自动装箱: Integer.valueOf(42)

    int value = list.get(0);  // 自动拆箱

    // Stream 也有装箱开销
    List<Integer> numbers = Arrays.asList(1, 2, 3, 4, 5);
    int sum = numbers.stream()
        .filter(n -> n % 2 == 0)
        .mapToInt(Integer::intValue)  // 需要转换避免装箱
        .sum();
}
```

**Rust 单态化:**

```rust
// Rust 泛型为每个类型生成专门代码

// 为 i32 生成一份代码
fn process_i32(x: i32) -> i32 {
    x * 2
}

// 为 f64 生成一份代码
fn process_f64(x: f64) -> f64 {
    x * 2.0
}

// 泛型版本 - 编译时单态化
fn process<T: std::ops::Mul<Output = T> + From<i32>>(x: T) -> T {
    x * T::from(2)
}

// 使用
fn use_generic() {
    let a = process(5i32);      // 编译为 process_i32
    let b = process(5.0f64);    // 编译为 process_f64
    let c = process(5u8);       // 编译为 process_u8

    // 基本类型无装箱
    let numbers = vec![1, 2, 3, 4, 5];
    let sum: i32 = numbers
        .iter()
        .filter(|&&n| n % 2 == 0)
        .sum();  // 无装箱
}
```

### 4.3 Trait vs Interface

| 特性 | Rust Trait | Java Interface |
|-----|-----------|---------------|
| **实现方式** | 显式 impl | 类声明 implements |
| **默认方法** | 支持 | Java 8+ 支持 |
| **关联类型** | 支持 | 不支持 |
| **静态方法** | 支持 | 支持 |
| **扩展性** | 孤儿规则限制 | 无限制 |

**Java Interface:**

```java
// 接口定义
public interface Drawable {
    void draw();

    // 默认实现 (Java 8+)
    default void describe() {
        System.out.println("A drawable object");
    }

    // 静态方法
    static void printInfo() {
        System.out.println("Drawable interface");
    }
}

// 类实现接口
public class Circle implements Drawable {
    @Override
    public void draw() {
        System.out.println("Drawing circle");
    }
}

// 接口组合
public interface Shape extends Drawable, Comparable<Shape> {
    double area();
}
```

**Rust Trait:**

```rust
// Trait 定义
pub trait Drawable {
    fn draw(&self);

    // 默认实现
    fn describe(&self) {
        println!("A drawable object");
    }
}

// 为类型实现 trait
pub struct Circle;

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle");
    }
}

// Trait 组合
pub trait Shape: Drawable + PartialOrd {
    fn area(&self) -> f64;
}

// 关联类型
pub trait Iterator {
    type Item;  // 关联类型

    fn next(&mut self) -> Option<Self::Item>;
}

// 为外部类型实现 trait (孤儿规则)
// 可以在当前 crate 为外部类型实现外部 trait
impl Drawable for String {
    fn draw(&self) {
        println!("Drawing: {}", self);
    }
}
```

### 4.4 代数数据类型

**Java 类层次结构:**

```java
// Java 模拟 ADT (繁琐)
public abstract class Result<T, E> {

    public static class Ok<T, E> extends Result<T, E> {
        public final T value;
        public Ok(T value) { this.value = value; }

        public T unwrap() { return value; }
    }

    public static class Err<T, E> extends Result<T, E> {
        public final E error;
        public Err(E error) { this.error = error; }

        public E unwrapErr() { return error; }
    }

    public boolean isOk() { return this instanceof Ok; }
    public boolean isErr() { return this instanceof Err; }
}

// 使用
Result<String, Exception> result = fetchData();
if (result.isOk()) {
    String data = ((Result.Ok<String, Exception>) result).value;
    System.out.println(data);
} else {
    Exception err = ((Result.Err<String, Exception>) result).error;
    err.printStackTrace();
}

// Java 17+ Sealed Classes 改进
public sealed interface Shape
    permits Circle, Rectangle, Square {
    double area();
}

public record Circle(double radius) implements Shape {
    public double area() { return Math.PI * radius * radius; }
}
```

**Rust Enum (真正的 ADT):**

```rust
// Rust 原生支持 ADT
pub enum Result<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> Result<T, E> {
    pub fn is_ok(&self) -> bool {
        matches!(self, Result::Ok(_))
    }

    pub fn unwrap(self) -> T {
        match self {
            Result::Ok(t) => t,
            Result::Err(_) => panic!("called `Result::unwrap()` on an `Err` value"),
        }
    }
}

// 使用
fn use_result() {
    let result = fetch_data();

    // 模式匹配
    match result {
        Ok(data) => println!("Data: {}", data),
        Err(e) => eprintln!("Error: {}", e),
    }

    // if let
    if let Ok(data) = result {
        println!("Data: {}", data);
    }
}

// 枚举变体可以包含数据
pub enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

// 使用
fn process_message(msg: Message) {
    match msg {
        Message::Quit => println!("Quitting"),
        Message::Move { x, y } => println!("Moving to ({}, {})", x, y),
        Message::Write(text) => println!("Writing: {}", text),
        Message::ChangeColor(r, g, b) => println!("Color: rgb({}, {}, {})", r, g, b),
    }
}
```

### 4.5 空值安全

**Java Optional:**

```java
import java.util.Optional;

public class OptionalExample {

    public Optional<String> findUserName(int id) {
        if (id > 0) {
            return Optional.of("User" + id);
        }
        return Optional.empty();
    }

    public void process() {
        Optional<String> nameOpt = findUserName(1);

        // 方式1: ifPresent
        nameOpt.ifPresent(name -> System.out.println(name));

        // 方式2: orElse
        String name = nameOpt.orElse("Unknown");

        // 方式3: orElseThrow
        String name2 = nameOpt.orElseThrow(() -> new RuntimeException("Not found"));

        // 方式4: map
        Optional<Integer> lengthOpt = nameOpt.map(String::length);

        // 问题：Optional 可以被赋值为 null！
        Optional<String> bad = null;  // 编译通过！
    }
}
```

**Rust Option:**

```rust
pub fn find_user_name(id: i32) -> Option<String> {
    if id > 0 {
        Some(format!("User{}", id))
    } else {
        None
    }
}

pub fn process() {
    let name_opt = find_user_name(1);

    // 方式1: if let
    if let Some(name) = &name_opt {
        println!("{}", name);
    }

    // 方式2: unwrap_or
    let name = name_opt.as_deref().unwrap_or("Unknown");

    // 方式3: expect
    let name = name_opt.as_ref().expect("Not found");

    // 方式4: map
    let length_opt = name_opt.as_ref().map(|s| s.len());

    // Option<T> 不能是 null！
    // let bad: Option<String> = null;  // 编译错误！
}
```

---

## 5. 并发模型对比

### 5.1 线程模型对比

| 特性 | Rust OS 线程 | Java 线程 |
|-----|-------------|-----------|
| **线程类型** | OS 线程 | OS 线程 (JVM 包装) |
| **栈大小** | ~1-8 MB | ~1 MB (可配置) |
| **创建方式** | thread::spawn | new Thread() / 线程池 |
| **线程池** | 第三方库 | ExecutorService |
| **绿色线程** | async/await | Virtual Threads (Project Loom) |

**Java 线程:**

```java
import java.util.concurrent.*;

public class JavaConcurrency {

    // 方式1: 直接创建线程
    public void directThread() {
        Thread thread = new Thread(() -> {
            System.out.println("Running in: " + Thread.currentThread().getName());
        });
        thread.start();
    }

    // 方式2: 线程池
    public void threadPool() throws Exception {
        ExecutorService executor = Executors.newFixedThreadPool(4);

        Future<Integer> future = executor.submit(() -> {
            return 42;
        });

        Integer result = future.get();  // 阻塞

        executor.shutdown();
    }

    // 方式3: CompletableFuture (异步)
    public void asyncOperations() {
        CompletableFuture.supplyAsync(() -> fetchData())
            .thenApply(data -> process(data))
            .thenAccept(result -> save(result))
            .exceptionally(ex -> {
                ex.printStackTrace();
                return null;
            });
    }

    // Java 21+ Virtual Threads
    public void virtualThreads() {
        try (var executor = Executors.newVirtualThreadPerTaskExecutor()) {
            for (int i = 0; i < 100000; i++) {
                executor.submit(() -> {
                    Thread.sleep(Duration.ofSeconds(1));
                    return "done";
                });
            }
        }
    }
}
```

**Rust 线程:**

```rust
use std::thread;
use std::sync::mpsc;
use std::time::Duration;

// 方式1: 直接创建线程
pub fn direct_thread() {
    let handle = thread::spawn(|| {
        println!("Running in: {:?}", thread::current().id());
    });
    handle.join().unwrap();
}

// 方式2: 线程池 (使用 rayon)
use rayon::ThreadPoolBuilder;

pub fn thread_pool() {
    let pool = ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();

    pool.install(|| {
        let result = parallel_computation();
        println!("{}", result);
    });
}

// 方式3: async/await
use tokio;

#[tokio::main]
pub async fn async_operations() {
    let result = tokio::spawn(async {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    }).await.unwrap();

    println!("{}", result);
}

// 方式4: rayon 数据并行
fn parallel_computation() -> i32 {
    (0..1000000)
        .into_par_iter()
        .map(|x| x * x)
        .sum()
}
```

### 5.2 内存模型对比

| 特性 | Rust | Java |
|-----|------|------|
| **内存顺序** | Ordering enum | happens-before |
| **原子操作** | std::sync::atomic | java.util.concurrent.atomic |
| **volatile** | Atomic* / Mutex | volatile 关键字 |
| **内存屏障** | 显式 | 隐式 (synchronized) |

**Java 内存模型:**

```java
import java.util.concurrent.atomic.*;

public class JavaMemoryModel {

    // volatile: 可见性，不保证原子性
    private volatile boolean flag = false;

    // Atomic: 原子性 + 可见性
    private AtomicInteger counter = new AtomicInteger(0);

    public void volatileExample() {
        // 线程A
        new Thread(() -> {
            flag = true;  // 写入 volatile
        }).start();

        // 线程B
        new Thread(() -> {
            while (!flag) {  // 读取 volatile
                // 等待
            }
            System.out.println("Flag is true!");
        }).start();
    }

    public void atomicExample() {
        // 原子操作
        int newValue = counter.incrementAndGet();

        // CAS 操作
        boolean success = counter.compareAndSet(0, 1);
    }

    // synchronized 内存屏障
    public synchronized void synchronizedMethod() {
        // 进入时：获取锁，刷新工作内存
        // 退出时：释放锁，刷新主内存
    }
}
```

**Rust 内存模型:**

```rust
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::Arc;
use std::thread;

pub fn atomic_example() {
    let flag = Arc::new(AtomicBool::new(false));
    let counter = Arc::new(AtomicI32::new(0));

    let flag_clone = Arc::clone(&flag);
    let handle1 = thread::spawn(move || {
        flag_clone.store(true, Ordering::Release);  // 释放语义
    });

    let flag_clone = Arc::clone(&flag);
    let handle2 = thread::spawn(move || {
        while !flag_clone.load(Ordering::Acquire) {  // 获取语义
            thread::yield_now();
        }
        println!("Flag is true!");
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}

pub fn memory_orderings() {
    let atomic = AtomicI32::new(0);

    // Relaxed: 无顺序保证，仅原子性
    atomic.fetch_add(1, Ordering::Relaxed);

    // Acquire/Release: 同步点
    atomic.store(1, Ordering::Release);
    let _ = atomic.load(Ordering::Acquire);

    // SeqCst: 顺序一致性
    atomic.store(1, Ordering::SeqCst);
    let _ = atomic.load(Ordering::SeqCst);
}
```

### 5.3 数据竞争防护

**Java 数据竞争 (编译通过，运行时问题):**

```java
public class DataRaceExample {
    private int counter = 0;

    public void unsafeIncrement() {
        // 数据竞争！非原子操作
        counter++;  // 读-改-写
    }

    // 安全方式1: synchronized
    public synchronized void safeIncrement() {
        counter++;
    }

    // 安全方式2: AtomicInteger
    private AtomicInteger atomicCounter = new AtomicInteger(0);

    public void atomicIncrement() {
        atomicCounter.incrementAndGet();
    }

    // 安全方式3: ReentrantLock
    private final ReentrantLock lock = new ReentrantLock();

    public void lockedIncrement() {
        lock.lock();
        try {
            counter++;
        } finally {
            lock.unlock();
        }
    }
}
```

**Rust 数据竞争防护 (编译期阻止):**

```rust
use std::sync::{Arc, Mutex};
use std::thread;

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
}

pub fn compile_time_safety() {
    let counter = Arc::new(Counter::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.increment();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("{}", *counter.count.lock().unwrap());  // 10000
}

// 编译期阻止可变共享
pub fn prevented_at_compile_time() {
    let mut data = vec![1, 2, 3];

    // 编译错误！不能同时有多个可变引用
    // let handle1 = thread::spawn(|| {
    //     data.push(4);
    // });
    // let handle2 = thread::spawn(|| {
    //     data.push(5);
    // });

    // 必须使用 Mutex
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    // ...
}
```

### 5.4 异步编程对比

**Java CompletableFuture:**

```java
import java.util.concurrent.*;

public class AsyncJava {

    public void asyncExample() {
        ExecutorService executor = Executors.newFixedThreadPool(4);

        CompletableFuture<String> future = CompletableFuture
            .supplyAsync(() -> fetchUser(1), executor)
            .thenApply(user -> fetchOrders(user))
            .thenCompose(orders -> calculateTotal(orders))
            .exceptionally(ex -> {
                System.err.println("Error: " + ex);
                return "0";
            });

        String result = future.join();
    }

    // Java 21+ Virtual Threads
    public void virtualThreadAsync() {
        try (var scope = new StructuredTaskScope.ShutdownOnFailure()) {
            Future<String> user = scope.fork(() -> fetchUser(1));
            Future<String> orders = scope.fork(() -> fetchOrders("user"));

            scope.join();
            scope.throwIfFailed();

            System.out.println(user.resultNow());
            System.out.println(orders.resultNow());
        }
    }
}
```

**Rust async/await:**

```rust
use tokio;

pub async fn async_example() {
    let result = fetch_user(1)
        .await
        .map(|user| fetch_orders(&user))
        .and_then(|orders| calculate_total(&orders))
        .await;

    match result {
        Ok(total) => println!("Total: {}", total),
        Err(e) => eprintln!("Error: {}", e),
    }
}

// 并发执行
pub async fn concurrent_fetch() {
    let user_future = fetch_user(1);
    let orders_future = fetch_orders("user");

    let (user, orders) = tokio::join!(user_future, orders_future);

    println!("User: {:?}, Orders: {:?}", user, orders);
}

// 超时处理
use tokio::time::{timeout, Duration};

pub async fn with_timeout() {
    let result = timeout(
        Duration::from_secs(5),
        fetch_user(1)
    ).await;

    match result {
        Ok(user) => println!("User: {:?}", user),
        Err(_) => println!("Timeout!"),
    }
}
```

---

## 6. 错误处理对比

### 6.1 异常 vs Result

| 特性 | Java Exception | Rust Result |
|-----|---------------|-------------|
| **检查型异常** | 有 (checked) | 无 (Result 强制处理) |
| **运行时异常** | 有 (unchecked) | panic |
| **传播方式** | throw/throws | ? 操作符 |
| **类型安全** | 部分 | 完全 |
| **性能** | 有开销 (栈展开) | 无开销 |

**Java 异常:**

```java
// 检查型异常
public void readFile(String path) throws IOException {
    Files.readString(Path.of(path));
}

// 运行时异常
public void unsafeOperation() {
    throw new IllegalArgumentException("Invalid input");
}

// try-catch-finally
public void handleException() {
    try {
        readFile("data.txt");
    } catch (IOException e) {
        // 处理异常
        logger.error("Failed to read", e);
    } catch (Exception e) {
        // 捕获其他异常
    } finally {
        // 清理资源
    }
}

// try-with-resources
public void tryWithResources() throws IOException {
    try (var reader = Files.newBufferedReader(Path.of("file.txt"))) {
        reader.readLine();
    }  // 自动关闭
}
```

**Rust Result:**

```rust
use std::fs;
use std::io;

// Result 类型
pub fn read_file(path: &str) -> Result<String, io::Error> {
    fs::read_to_string(path)
}

// panic (类似运行时异常)
pub fn unsafe_operation() {
    panic!("Invalid input");
}

// 错误处理
pub fn handle_error() {
    match read_file("data.txt") {
        Ok(content) => println!("{}", content),
        Err(e) => eprintln!("Failed to read: {}", e),
    }
}

// ? 操作符传播
pub fn read_and_process() -> Result<(), Box<dyn std::error::Error>> {
    let content = read_file("data.txt")?;
    process(&content)?;
    Ok(())
}

// thiserror 简化错误定义
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("Invalid input: {0}")]
    InvalidInput(String),
}
```

### 6.2 错误传播

**Java:**

```java
public void operationA() throws CustomException {
    try {
        operationB();
    } catch (IOException e) {
        throw new CustomException("Failed in A", e);
    }
}

public void operationB() throws IOException {
    operationC();
}

public void operationC() throws IOException {
    Files.readString(Path.of("file.txt"));
}
```

**Rust:**

```rust
use anyhow::{Context, Result};

pub fn operation_a() -> Result<()> {
    operation_b().context("Failed in A")?;
    Ok(())
}

pub fn operation_b() -> Result<()> {
    operation_c()?;
    Ok(())
}

pub fn operation_c() -> Result<()> {
    std::fs::read_to_string("file.txt")?;
    Ok(())
}
```

---

## 7. 性能特征对比

### 7.1 运行时开销

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                         运行时开销对比                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  组件              Rust                     Java                             │
│  ─────────────────────────────────────────────────────────────────────      │
│                                                                             │
│  运行时库          无 / 极小 (~100KB)       JVM (~100MB)                     │
│  垃圾回收          无                        并发标记清除/G1/ZGC              │
│  JIT 编译          无                        HotSpot C1/C2                    │
│  字节码验证        无                        类加载时                         │
│  反射              编译期 (有限)             运行时 (完整)                    │
│                                                                             │
│  总开销：Rust << Java                                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 7.2 启动性能

| 指标 | Rust | Java |
|-----|------|------|
| **冷启动时间** | < 1 ms | 100 ms - 数秒 |
| **内存占用 (空)** | ~1 MB | ~50 MB |
| **内存占用 (服务)** | ~5-20 MB | ~200-500 MB |
| **容器镜像** | ~5 MB (scratch) | ~100+ MB (JRE) |

### 7.3 零成本抽象

**Java Stream 开销:**

```java
import java.util.List;

public class StreamOverhead {

    public int sumWithStream(List<Integer> numbers) {
        // 有装箱和虚调用开销
        return numbers.stream()
            .filter(n -> n % 2 == 0)
            .mapToInt(Integer::intValue)  // 拆箱
            .sum();
    }

    // 手动循环更快
    public int sumManual(List<Integer> numbers) {
        int sum = 0;
        for (int n : numbers) {
            if (n % 2 == 0) {
                sum += n;
            }
        }
        return sum;
    }
}
```

**Rust 迭代器零开销:**

```rust
pub fn sum_with_iterator(numbers: &[i32]) -> i32 {
    // 编译为与手写循环等价的机器码
    numbers
        .iter()
        .filter(|&&n| n % 2 == 0)
        .sum()
}

// 等价的手写循环
pub fn sum_manual(numbers: &[i32]) -> i32 {
    let mut sum = 0;
    for &n in numbers {
        if n % 2 == 0 {
            sum += n;
        }
    }
    sum
}

// 编译后两者相同 (godbolt.org 验证)
```

---

## 8. 代码示例对比

### 8.1 集合操作

**Java:**

```java
import java.util.*;
import java.util.stream.*;

public class CollectionOperations {

    public List<String> process(List<String> input) {
        return input.stream()
            .filter(s -> s.length() > 3)
            .map(String::toUpperCase)
            .distinct()
            .sorted()
            .collect(Collectors.toList());
    }

    public Map<String, Integer> groupByLength(List<String> input) {
        return input.stream()
            .collect(Collectors.groupingBy(
                String::length,
                Collectors.counting()
            ))
            .entrySet().stream()
            .collect(Collectors.toMap(
                Map.Entry::getKey,
                e -> e.getValue().intValue()
            ));
    }
}
```

**Rust:**

```rust
use std::collections::HashMap;

pub fn process(input: Vec<String>) -> Vec<String> {
    input
        .into_iter()
        .filter(|s| s.len() > 3)
        .map(|s| s.to_uppercase())
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect::<Vec<_>>()
}

pub fn group_by_length(input: &[String]) -> HashMap<usize, usize> {
    input
        .iter()
        .fold(HashMap::new(), |mut acc, s| {
            *acc.entry(s.len()).or_insert(0) += 1;
            acc
        })
}

// 使用 itertools 更简洁
use itertools::Itertools;

pub fn process_with_itertools(input: Vec<String>) -> Vec<String> {
    input
        .into_iter()
        .filter(|s| s.len() > 3)
        .map(|s| s.to_uppercase())
        .unique()
        .sorted()
        .collect()
}
```

### 8.2 文件处理

**Java:**

```java
import java.nio.file.*;
import java.util.*;
import java.io.*;

public class FileProcessing {

    public Map<String, Integer> wordCount(String path) throws IOException {
        Map<String, Integer> counts = new HashMap<>();

        try (BufferedReader reader = Files.newBufferedReader(Path.of(path))) {
            String line;
            while ((line = reader.readLine()) != null) {
                for (String word : line.split("\\s+")) {
                    counts.merge(word.toLowerCase(), 1, Integer::sum);
                }
            }
        }

        return counts;
    }
}
```

**Rust:**

```rust
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

pub fn word_count<P: AsRef<Path>>(path: P) -> io::Result<HashMap<String, i32>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    let mut counts = HashMap::new();

    for line in reader.lines() {
        let line = line?;
        for word in line.split_whitespace() {
            *counts.entry(word.to_lowercase()).or_insert(0) += 1;
        }
    }

    Ok(counts)
}

// 函数式风格
pub fn word_count_functional<P: AsRef<Path>>(path: P) -> io::Result<HashMap<String, i32>> {
    let content = std::fs::read_to_string(path)?;

    let counts = content
        .split_whitespace()
        .map(|w| w.to_lowercase())
        .fold(HashMap::new(), |mut acc, word| {
            *acc.entry(word).or_insert(0) += 1;
            acc
        });

    Ok(counts)
}
```

### 8.3 并发计数器

**Java:**

```java
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

public class ConcurrentCounter {

    // 方式1: AtomicInteger
    private AtomicInteger atomicCounter = new AtomicInteger(0);

    public void incrementAtomic() {
        atomicCounter.incrementAndGet();
    }

    // 方式2: LongAdder (高并发优化)
    private LongAdder adder = new LongAdder();

    public void incrementAdder() {
        adder.increment();
    }

    // 方式3: synchronized
    private int syncCounter = 0;

    public synchronized void incrementSync() {
        syncCounter++;
    }

    // 使用示例
    public void demo() throws Exception {
        ExecutorService executor = Executors.newFixedThreadPool(10);

        for (int i = 0; i < 1000; i++) {
            executor.submit(this::incrementAtomic);
        }

        executor.shutdown();
        executor.awaitTermination(1, TimeUnit.MINUTES);

        System.out.println(atomicCounter.get());
    }
}
```

**Rust:**

```rust
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

// 方式1: Atomic
pub struct AtomicCounter {
    value: AtomicI32,
}

impl AtomicCounter {
    pub fn new() -> Self {
        Self { value: AtomicI32::new(0) }
    }

    pub fn increment(&self) {
        self.value.fetch_add(1, Ordering::Relaxed);
    }

    pub fn get(&self) -> i32 {
        self.value.load(Ordering::Relaxed)
    }
}

// 方式2: Mutex
pub struct MutexCounter {
    value: Mutex<i32>,
}

impl MutexCounter {
    pub fn new() -> Self {
        Self { value: Mutex::new(0) }
    }

    pub fn increment(&self) {
        let mut v = self.value.lock().unwrap();
        *v += 1;
    }
}

// 使用示例
pub fn demo() {
    let counter = Arc::new(AtomicCounter::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                c.increment();
            }
        });
        handles.push(handle);
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("{}", counter.get());
}
```

### 8.4 REST API 服务

**Java (Spring Boot):**

```java
import org.springframework.web.bind.annotation.*;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

@SpringBootApplication
@RestController
@RequestMapping("/api")
public class Application {

    @GetMapping("/users/{id}")
    public User getUser(@PathVariable Long id) {
        return new User(id, "User" + id);
    }

    @PostMapping("/users")
    public User createUser(@RequestBody User user) {
        return user;
    }

    public static void main(String[] args) {
        SpringApplication.run(Application.class, args);
    }
}

record User(Long id, String name) {}
```

**Rust (Axum):**

```rust
use axum::{
    routing::{get, post},
    Json, Router,
    extract::Path,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
}

async fn get_user(Path(id): Path<u64>) -> Json<User> {
    Json(User { id, name: format!("User{}", id) })
}

async fn create_user(Json(user): Json<User>) -> (StatusCode, Json<User>) {
    (StatusCode::CREATED, Json(user))
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/api/users/:id", get(get_user))
        .route("/api/users", post(create_user));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

---

## 9. 生态系统对比

### 9.1 构建工具

| 特性 | Cargo (Rust) | Maven/Gradle (Java) |
|-----|-------------|---------------------|
| **配置** | Cargo.toml | pom.xml / build.gradle |
| **依赖管理** | 语义版本 + 锁文件 | 传递依赖 |
| **编译** | 内置 | 需要插件 |
| **测试** | 内置 | 需要 JUnit |
| **文档** | 内置 (rustdoc) | 需要插件 |
| **发布** | cargo publish | mvn deploy |

### 9.2 框架生态

| 领域 | Java | Rust |
|-----|------|------|
| Web | Spring Boot, Quarkus | Axum, Actix-web |
| ORM | Hibernate, MyBatis | Diesel, SeaORM |
| 序列化 | Jackson, Gson | Serde |
| 日志 | Log4j, SLF4J | Tracing, log |
| 测试 | JUnit, TestNG | 内置 + tokio-test |
| HTTP 客户端 | OkHttp, WebClient | reqwest |

### 9.3 部署运维

| 方面 | Rust | Java |
|-----|------|------|
| **二进制** | 原生可执行文件 | JAR/WAR + JRE |
| **容器镜像** | ~5 MB | ~100+ MB |
| **启动时间** | 毫秒 | 秒级 |
| **内存占用** | 低 | 高 |
| **可移植性** | 需交叉编译 | 字节码跨平台 |

---

## 10. 适用场景分析

| 场景 | 推荐 | 理由 |
|-----|------|------|
| 企业级 Web 应用 | Java | Spring 生态成熟 |
| 微服务/云原生 | 两者皆可 | 各有优势 |
| 系统编程 | Rust | 安全 + 性能 |
| 嵌入式/IoT | Rust | no_std 支持 |
| 大数据处理 | Java | Hadoop/Spark 生态 |
| CLI 工具 | Rust | 快速启动，小体积 |
| Android 开发 | Java/Kotlin | 原生支持 |
| 实时系统 | Rust | 无 GC 暂停 |

---

## 11. 迁移指南

### Java → Rust 思维转换

```
┌─────────────────────────────────────────────────────────────────┐
│                    思维模式转换                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Java 思维                   →    Rust 思维                      │
│  ─────────────────────────────────────────────────────────      │
│                                                                 │
│  垃圾回收                   →    所有权系统                      │
│  null                       →    Option<T>                     │
│  Exception                  →    Result<T, E>                  │
│  interface                  →    trait                         │
│  synchronized               →    Mutex / RwLock                │
│  Stream API                 →    Iterator                      │
│  CompletableFuture          →    async/await                   │
│  instanceof                 →    match / if let                │
│  final                      →    默认不可变                    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 总结

| 维度 | Java | Rust |
|:---|:---|:---|
| **执行模型** | JVM + JIT | 原生 AOT |
| **内存管理** | GC | 所有权 |
| **内存安全** | GC + 运行时 | 编译期保证 |
| **启动性能** | 慢 | 快 |
| **运行时开销** | 高 | 极低 |
| **类型系统** | 擦除泛型 | 单态化 |
| **并发安全** | 运行时检测 | 编译期保证 |
| **生态成熟度** | 极高 | 快速成长 |

**选择建议:**

- 长期运行服务端应用 → **Java**
- 系统编程、CLI 工具、嵌入式 → **Rust**
- 两者都是优秀的现代语言，根据具体场景选择

---

## 参考文献

1. Gosling, J., et al. (2005). *The Java Language Specification*.
2. Klabnik, S., & Nichols, C. (2023). *The Rust Programming Language*.
3. Oracle JVM Documentation. <https://docs.oracle.com/javase/>
4. Rust Performance Book. <https://nnethercote.github.io/perf-book/>
5. Java Memory Model Specification.
6. Various benchmark reports: TechEmpower, benchmarks-game.

---

*文档版本: 2.0.0 (L2+ 深度)*
*最后更新: 2026-03-07*
*维护者: Rust Comparative Study Team*
