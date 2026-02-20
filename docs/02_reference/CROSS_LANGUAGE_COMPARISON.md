# Rust 与 C++/Go/Python 跨语言对比

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 技术选型、迁移参考、概念对标

---

## 目录

- [Rust 与 C++/Go/Python 跨语言对比](#rust-与-cgopython-跨语言对比)
  - [目录](#目录)
  - [内存管理](#内存管理)
  - [并发模型](#并发模型)
  - [错误处理](#错误处理)
  - [类型系统](#类型系统)
  - [生态与工具链](#生态与工具链)
  - [相关文档](#相关文档)

---

## 内存管理

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 模型 | 所有权 + 借用 | 手动/智能指针/RAII | GC | GC |
| 安全 | 编译期保证 | 依赖程序员 | 运行时 GC | 运行时 GC |
| 零成本 | 是 | 可选 | 否 | 否 |
| 学习曲线 | 高 | 高 | 低 | 低 |

### 内存管理代码对比示例

**场景：创建一个字符串并传递给函数**

```rust
// Rust: 所有权自动转移
fn main() {
    let s = String::from("hello");
    process_string(s);      // s 的所有权转移到函数
    // println!("{}", s);   // 编译错误！s 已被移动
}

fn process_string(s: String) {
    println!("{}", s);
} // s 在这里自动释放
```

```cpp
// C++: 使用智能指针
#include <memory>
#include <iostream>

void process_string(std::unique_ptr<std::string> s) {
    std::cout << *s << std::endl;
} // s 在这里自动释放

int main() {
    auto s = std::make_unique<std::string>("hello");
    process_string(std::move(s));  // 显式转移所有权
    // std::cout << *s;             // 运行时错误！s 已空
    return 0;
}
```

```go
// Go: GC 自动管理
package main

import "fmt"

func processString(s string) {
    fmt.Println(s)
}

func main() {
    s := "hello"
    processString(s)  // 值拷贝（字符串是引用类型）
    fmt.Println(s)    // 仍然可用
}
```

```python
# Python: GC 自动管理
def process_string(s):
    print(s)

s = "hello"
process_string(s)  # 引用传递
print(s)           # 仍然可用
```

### 内存管理形式化对比

| 语言 | 形式化模型 | 安全保证 | 形式化证明 |
| :--- | :--- | :--- | :--- |
| **Rust** | 线性类型 + 分离逻辑 | 编译期 | [所有权唯一性定理](../research_notes/formal_methods/ownership_model.md#定理-2-所有权唯一性)、[内存安全定理](../research_notes/formal_methods/ownership_model.md#定理-3-内存安全框架) |
| **C++** | 无统一形式化 | 运行时/程序员 | 无官方形式化证明 |
| **Go** | 标记-清除 GC | 运行时 | GC 正确性证明 |
| **Python** | 引用计数 + GC | 运行时 | 无官方形式化证明 |

**Rust 形式化定义**:
- 所有权规则: $\forall v. \text{唯一拥有者}(v)$ ([规则 1](../research_notes/formal_methods/ownership_model.md#规则-1-所有权唯一性))
- 移动语义: $\text{move}(x, y) \rightarrow \Omega(x) = \text{Moved} \land \Omega(y) = \text{Owned}$ ([规则 2](../research_notes/formal_methods/ownership_model.md#规则-2-移动语义))

---

## 并发模型

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 线程 | std::thread | std::thread | goroutine | threading |
| 异步 | async/await | 库（如 asio） | go/chan | asyncio |
| 数据竞争 | 编译期禁止 | 需手动同步 | 通道优先 | GIL 限制 |
| 推荐 | 所有权 + Send/Sync | 各显其能 | CSP/goroutine | 多进程/asyncio |

### 并发代码对比示例

**场景：两个线程同时增加一个计数器**

```rust
// Rust: 编译期保证数据竞争自由
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..2 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("结果: {}", *counter.lock().unwrap());
}
```

```cpp
// C++: 需要手动同步
#include <mutex>
#include <thread>
#include <iostream>

int counter = 0;
std::mutex mtx;

void increment() {
    std::lock_guard<std::mutex> lock(mtx);
    ++counter;
}

int main() {
    std::thread t1(increment);
    std::thread t2(increment);
    t1.join();
    t2.join();
    std::cout << "结果: " << counter << std::endl;
    return 0;
}
```

```go
// Go: 使用 channel 通信
go func() {
    counter := 0
    done := make(chan bool)
    
    for i := 0; i < 2; i++ {
        go func() {
            counter++  // 数据竞争！需要互斥
            done <- true
        }()
    }
    
    for i := 0; i < 2; i++ {
        <-done
    }
    println("结果:", counter)
}()
```

```python
# Python: GIL 限制真正的并行
import threading

counter = 0
lock = threading.Lock()

def increment():
    global counter
    with lock:
        counter += 1

t1 = threading.Thread(target=increment)
t2 = threading.Thread(target=increment)
t1.start()
t2.start()
t1.join()
t2.join()
print(f"结果: {counter}")
```

### 并发模型形式化对比

| 语言 | 并发安全机制 | 数据竞争检测 | 形式化保证 |
| :--- | :--- | :--- | :--- |
| **Rust** | Send/Sync Trait | 编译期 | [数据竞争自由定理](../research_notes/formal_methods/borrow_checker_proof.md#定理-1-数据竞争自由) |
| **C++** | 手动同步 | 运行时工具 (TSan) | 无编译期保证 |
| **Go** | Channel + Mutex | 运行时工具 (race detector) | 无编译期保证 |
| **Python** | GIL + 手动锁 | 运行时工具 | GIL 保证解释器状态安全 |

**Rust 形式化定义**:
- Send Trait: 跨线程转移所有权 ([Def SEND1](../research_notes/formal_methods/send_sync_formalization.md#defs-send1send-sync1sendsync-形式化))
- Sync Trait: 跨线程共享引用 ([Def SYNC1](../research_notes/formal_methods/send_sync_formalization.md#defs-send1send-sync1sendsync-形式化))
- 数据竞争自由: $\text{DataRaceFree}(P)$ ([定理 1](../research_notes/formal_methods/borrow_checker_proof.md#定理-1-数据竞争自由))

---

## 错误处理

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 机制 | Result/Option | 异常/error_code | error 返回值 | 异常 |
| 必须处理 | 是（编译期） | 否 | 习惯性 | 否 |
| 传播 | ? 操作符 | throw/catch | if err | raise |

---

## 类型系统

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 类型 | 静态强类型 | 静态强类型 | 静态（少泛型） | 动态 |
| 泛型 | 单态化 | 模板 | 1.18+ 泛型 | 不适用 |
| 推断 | 强 | 有 | 有 | 无 |

---

## 生态与工具链

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 包管理 | Cargo | vcpkg/conan | go mod | pip |
| 构建 | cargo build | CMake/MSBuild | go build | 无统一 |
| 文档 | rustdoc | Doxygen | godoc | Sphinx |

---

## 相关文档

- [多维概念矩阵](./MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)
- [应用分析视图](./APPLICATIONS_ANALYSIS_VIEW.md)
