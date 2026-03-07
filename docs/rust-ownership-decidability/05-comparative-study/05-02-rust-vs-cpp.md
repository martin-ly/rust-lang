# Rust vs C++ 深度对比

> **对比维度**: 内存安全、性能、并发、生态
> **难度**: 🟡 中等
> **目标读者**: 有 C++ 背景学习 Rust 的开发者

---

## 目录

- [Rust vs C++ 深度对比](#rust-vs-c-深度对比)
  - [目录](#目录)
  - [1. 内存安全对比](#1-内存安全对比)
    - [核心差异](#核心差异)
    - [示例: 悬垂指针](#示例-悬垂指针)
  - [2. 所有权系统对比](#2-所有权系统对比)
    - [C++ RAII vs Rust Ownership](#c-raii-vs-rust-ownership)
  - [3. 并发模型对比](#3-并发模型对比)
    - [线程安全](#线程安全)
    - [Send/Sync vs C++](#sendsync-vs-c)
  - [4. 性能对比](#4-性能对比)
    - [零成本抽象](#零成本抽象)
    - [实际性能](#实际性能)
  - [5. 抽象机制对比](#5-抽象机制对比)
    - [模板 vs 泛型](#模板-vs-泛型)
    - [Trait vs 抽象类/概念](#trait-vs-抽象类概念)
  - [6. 代码对比](#6-代码对比)
    - [错误处理](#错误处理)
    - [智能指针](#智能指针)
  - [7. 迁移指南](#7-迁移指南)
    - [C++ → Rust 思维转换](#c--rust-思维转换)
    - [工具链映射](#工具链映射)

---

## 1. 内存安全对比

### 核心差异

| 方面 | Rust | C++ |
|-----|------|-----|
| **内存安全保证** | 编译期保证 | 程序员责任 |
| **空指针** | 编译期阻止 (Option) | 运行时崩溃 |
| **use-after-free** | 编译期阻止 | UBSAN/ASan 检测 |
| **buffer overflow** | 编译期检查 | 运行时保护 (部分) |
| **数据竞争** | 编译期阻止 (Send/Sync) | TSan 检测 |

### 示例: 悬垂指针

```cpp
// C++ - 运行时问题
std::string* get_string() {
    std::string s = "hello";
    return &s;  // 返回局部变量地址!
}

int main() {
    std::string* p = get_string();
    std::cout << *p;  // UB! 悬垂指针
}
```

```rust
// Rust - 编译期阻止
fn get_string() -> &String {
    let s = String::from("hello");
    &s  // 编译错误: 返回局部变量引用
}
```

---

## 2. 所有权系统对比

### C++ RAII vs Rust Ownership

```cpp
// C++ RAII
class File {
    FILE* handle;
public:
    File(const char* path) : handle(fopen(path, "r")) {}
    ~File() { if (handle) fclose(handle); }

    // 移动语义
    File(File&& other) : handle(other.handle) {
        other.handle = nullptr;
    }

    // 禁止拷贝
    File(const File&) = delete;
    File& operator=(const File&) = delete;
};
```

```rust
// Rust 所有权
pub struct File {
    handle: std::fs::File,
}

impl File {
    pub fn new(path: &str) -> Result<Self, Error> {
        Ok(Self {
            handle: std::fs::File::open(path)?,
        })
    }
}

// Drop 自动实现
// Clone/Copy 需要显式实现
```

**对比**:

- C++: 约定 + 工具辅助
- Rust: 编译器强制执行

---

## 3. 并发模型对比

### 线程安全

```cpp
// C++ - 程序员责任
std::vector<int> shared_data;
std::mutex mtx;

void thread_func() {
    std::lock_guard<std::mutex> lock(mtx);
    shared_data.push_back(42);  // 忘记加锁 = 数据竞争
}
```

```rust
// Rust - 类型系统保证
use std::sync::{Arc, Mutex};

let shared_data = Arc::new(Mutex::new(Vec::new()));

std::thread::spawn(move || {
    let mut data = shared_data.lock().unwrap();
    data.push(42);  // 编译期保证安全
});
```

### Send/Sync vs C++

| Rust | C++ 等价 |
|-----|---------|
| `Send` | 可跨线程移动 (通常安全) |
| `Sync` | 线程安全 (类似 `std::atomic` 或加锁) |

---

## 4. 性能对比

### 零成本抽象

两者都支持零成本抽象，但 Rust 的更安全：

```cpp
// C++ 迭代器 (可能越界)
std::vector<int> v = {1, 2, 3};
for (auto it = v.begin(); it != v.end(); ++it) {
    *it;  // 不安全
}
```

```rust
// Rust 迭代器 (安全)
let v = vec![1, 2, 3];
for x in &v {  // 借用检查确保安全
    println!("{}", x);
}
```

### 实际性能

| 场景 | Rust | C++ | 备注 |
|-----|------|-----|------|
| 原始计算 | 相同 | 相同 | LLVM 后端 |
| 字符串处理 | 相同 | 相同 | SSO 优化 |
| 动态分发 | 相同 | 相同 | vtable |
| 编译时间 | 较慢 | 较快 | 借用检查 |

---

## 5. 抽象机制对比

### 模板 vs 泛型

```cpp
// C++ 模板
template<typename T>
T add(T a, T b) {
    return a + b;  // 错误在实例化时发现
}
```

```rust
// Rust 泛型 + Trait Bounds
fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b  // 错误在定义时发现
}
```

### Trait vs 抽象类/概念

| 特性 | Rust Trait | C++ 概念 (C++20) |
|-----|-----------|-----------------|
| 静态分发 | 单态化 | 模板实例化 |
| 动态分发 | Trait 对象 | 虚函数 |
| 关联类型 | 支持 | 支持 |
| 默认实现 | 支持 | 支持 |

---

## 6. 代码对比

### 错误处理

```cpp
// C++ 异常
std::ifstream file("data.txt");
if (!file) {
    throw std::runtime_error("Cannot open file");
}
```

```rust
// Rust Result
let file = std::fs::File::open("data.txt")
    .map_err(|e| format!("Cannot open file: {}", e))?;
```

### 智能指针

| Rust | C++ | 用途 |
|-----|-----|------|
| `Box<T>` | `std::unique_ptr<T>` | 唯一所有权 |
| `Rc<T>` | `std::shared_ptr<T>` | 共享所有权 (单线程) |
| `Arc<T>` | `std::shared_ptr<T>` | 共享所有权 (多线程) |
| `RefCell<T>` | 无直接等价 | 运行时借用检查 |
| `Mutex<T>` | `std::mutex` | 互斥锁 |

---

## 7. 迁移指南

### C++ → Rust 思维转换

```
1. 从手动内存管理 → 编译器管理
2. 从注释约定 → 类型系统保证
3. 从异常 → Result/Option
4. 从模板元编程 → 过程宏
5. 从 Boost → crates.io
```

### 工具链映射

| C++ | Rust |
|-----|------|
| CMake | Cargo |
| Conan/vcpkg | crates.io |
| clang-format | rustfmt |
| clang-tidy | Clippy |
| Valgrind | Miri |
| AddressSanitizer | 内置/ASan |

---

*文档版本: 1.0.0*
