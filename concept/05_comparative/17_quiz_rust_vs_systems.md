> **内容分级**: [综述级]

# 测验：Rust vs 系统编程语言（L5 试点扩展）

> **受众**: [进阶]
> **内容分级**: [综述级]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**:
> [Rust vs C++ — Rust Book](https://doc.rust-lang.org/nomicon/) ·
> [Rust vs Go — Official Comparisons](https://go.dev/doc/) ·
> [The C Programming Language — K&R]
>
> **前置概念**:
> [Rust vs C++](./01_rust_vs_cpp.md) ·
> [Rust vs Go](./03_rust_vs_go.md)

---

> **Bloom 层级**: 分析 → 评价
> **定位**: L5 嵌入式互动测验——通过代码对比验证 Rust 与 C/C++/Go 在内存安全、并发模型、错误处理等维度的核心差异。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、内存安全对比

### Q1. 以下 C 代码有什么问题？Rust 如何防止同样的问题？

```c
// C 代码
char* greet() {
    char msg[] = "Hello";
    return msg;  // 返回局部变量地址！
}

int main() {
    char* s = greet();
    printf("%s\n", s);
    return 0;
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：C 代码有**悬垂指针（dangling pointer）**——`msg` 是局部数组，函数返回后栈帧被销毁，`s` 指向无效内存。

**Rust 的等效代码**：

```rust
fn greet() -> String {
    let msg = String::from("Hello");
    msg // 移动所有权，安全返回
}

fn main() {
    let s = greet();
    println!("{}", s); // ✅ 安全
}
```

**若尝试返回引用**：

```rust
fn greet() -> &str {
    let msg = String::from("Hello");
    &msg // ❌ 编译错误！返回局部变量的引用
}
```

错误信息：`cannot return reference to local variable msg`

**对比**：

| 方面 | C | Rust |
|:---|:---|:---|
| 局部变量返回 | 允许（UB） | 引用禁止，值必须转移所有权 |
| 检测时机 | 运行期 segfault（或更糟） | 编译期拒绝 |
| 修复成本 | 调试困难 | 编译器直接指出问题 |

**知识点**：Rust 的所有权系统在编译期消除了整类 C 语言内存错误。返回局部变量引用是最常见的 C bug 之一，在 Rust 中完全不可能。[→ Rust vs C++ 详解](./01_rust_vs_cpp.md)

</details>

---

### Q2. 以下 Go 代码有什么问题？Rust 如何处理同样的场景？

```go
// Go 代码
func main() {
    var ptr *int
    *ptr = 42  // 解引用 nil 指针！
    fmt.Println(*ptr)
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：Go 代码会 **panic**（运行时崩溃）：`runtime error: invalid memory address or nil pointer dereference`。

**Rust 的等效代码**：

```rust
fn main() {
    let ptr: *const i32 = std::ptr::null();
    unsafe {
        println!("{}", *ptr); // ❌ 运行期 segfault（unsafe 允许）
    }
}
```

**但 Rust 的 safe 代码中**：

```rust
fn main() {
    let maybe: Option<&i32> = None;
    println!("{}", maybe.unwrap()); // ❌ 运行期 panic！
    // 或更安全：
    if let Some(val) = maybe {
        println!("{}", val);
    }
}
```

**对比**：

| 方面 | Go | Rust |
|:---|:---|:---|
| nil 指针 | 语言内置，运行期 panic | safe Rust 无 nil；`Option<T>` 显式处理缺失 |
| 解引用 Optional | N/A（无此概念） | `unwrap()` panic；`if let`/`match` 安全处理 |
| 默认安全 | 运行期检查 | 编译期强制处理所有情况 |

**核心差异**：Go 的 `nil` 是**十亿美元错误**（C.A.R. Hoare）的现代延续。Rust 通过 `Option<T>` 将"可能缺失"显式编码到类型系统中。[→ Rust vs Go 详解](./03_rust_vs_go.md)

</details>

---

## 二、并发模型对比

### Q3. 以下 C++ 代码存在什么数据竞争？Rust 如何防止？

```cpp
// C++ 代码
#include <thread>
#include <iostream>

int counter = 0;

void increment() {
    for (int i = 0; i < 100000; ++i) {
        ++counter;  // 数据竞争！
    }
}

int main() {
    std::thread t1(increment);
    std::thread t2(increment);
    t1.join(); t2.join();
    std::cout << counter << std::endl;  // 可能 < 200000
    return 0;
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：C++ 代码有**数据竞争（data race）**——两个线程无同步地修改同一内存位置。结果是未定义行为（UB），`counter` 可能小于 200000。

**Rust 的等效代码**：

```rust
use std::thread;

fn main() {
    let mut counter = 0;

    let handle1 = thread::spawn(|| {
        for _ in 0..100000 {
            counter += 1; // ❌ 编译错误！
        }
    });

    let handle2 = thread::spawn(|| {
        for _ in 0..100000 {
            counter += 1; // ❌ 编译错误！
        }
    });
}
```

错误信息：`cannot borrow `counter` as mutable more than once at a time`

**Rust 的正确写法**：

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..2 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            for _ in 0..100000 {
                *counter.lock().unwrap() += 1;
            }
        }));
    }

    for h in handles { h.join().unwrap(); }
    println!("{}", *counter.lock().unwrap()); // 200000
}
```

**对比**：

| 方面 | C++ | Rust |
|:---|:---|:---|
| 数据竞争 | 允许（UB） | 编译期阻止 |
| 同步原语 | 手动选择（mutex、atomic） | `Mutex`、`RwLock` 与所有权系统集成 |
| 检测 | ThreadSanitizer（运行时） | 编译器借用检查（编译期） |
| 性能开销 | 零（若代码正确） | 零（检查在编译期完成） |

**知识点**：Rust 的"无畏并发"不是口号——编译器通过 `Send`/`Sync` trait 和借用检查器在编译期阻止所有数据竞争。[→ 并发模型详解](../03_advanced/01_concurrency.md)

</details>

---

### Q4. 以下 Go 代码的 goroutine 泄漏风险是什么？Rust 的 async/await 如何避免？

```go
// Go 代码
func main() {
    ch := make(chan int)
    go func() {
        ch <- 42  // 若无人接收，goroutine 永远阻塞！
    }()
    // 忘记接收 ch
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：Go 代码中，若 `main` 在 goroutine 发送前结束，goroutine 可能永远阻塞（goroutine 泄漏）。Go 的 channel 在**运行时**检测死锁，但只能在程序完全死锁时 panic，无法检测部分泄漏。

**Rust 的等效代码**：

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(1);

    tokio::spawn(async move {
        tx.send(42).await.unwrap(); // 异步发送
    });

    // 必须 await 接收，否则编译器警告未使用变量
    let val = rx.recv().await.unwrap();
    println!("{}", val);
}
```

**Rust 的优势**：

1. **所有权追踪**：`tx` 的生命周期与任务绑定，若 `tx` 被 drop 而 `rx` 仍在等待，`recv()` 返回 `None`
2. **编译期检查**：Rust 要求显式处理 `Result`，不能"忘记"处理通道
3. **结构化并发**：`tokio::select!` 和作用域确保任务在控制流结束时完成

**对比**：

| 方面 | Go goroutine | Rust async task |
|:---|:---|:---|
| 创建成本 | ~2 KB 栈 | ~几百字节 |
| 泄漏检测 | 运行期（有限） | 编译期 + 所有权 drop |
| 取消机制 | 通过 context 手动传递 | 内置 `AbortHandle` |
| 调试 | goroutine dump | `tokio-console` 运行时检查 |

**知识点**：Rust 的所有权系统为并发原语提供了编译期保证，而 Go 依赖运行时检测和程序员纪律。[→ Rust vs Go 详解](./03_rust_vs_go.md)

</details>

---

## 三、错误处理对比

### Q5. 以下 C 代码的错误处理有什么问题？Rust 的 `Result` 如何改进？

```c
// C 代码
FILE* f = fopen("data.txt", "r");
if (f == NULL) {
    // 错误处理... 但经常被忽略！
}
char buf[100];
fgets(buf, 100, f);  // 若 f 为 NULL，UB！
fclose(f);
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：C 代码的问题：

1. **错误检查可选**：程序员可以（也经常）忘记检查 `fopen` 返回值
2. **错误传播繁琐**：每个调用都需要手动检查，导致深层嵌套
3. **资源泄漏风险**：若中间出错，`fclose` 可能不被调用

**Rust 的等效代码**：

```rust
use std::fs::File;
use std::io::{self, BufRead, BufReader};

fn read_file() -> io::Result<String> {
    let file = File::open("data.txt")?; // 若失败，自动返回 Err
    let mut reader = BufReader::new(file);
    let mut line = String::new();
    reader.read_line(&mut line)?;       // 若失败，自动返回 Err
    Ok(line)
}

fn main() {
    match read_file() {
        Ok(content) => println!("{}", content),
        Err(e) => eprintln!("Error: {e}"),
    }
}
```

**Rust 的改进**：

| 方面 | C | Rust |
|:---|:---|:---|
| 错误值 | 通过返回值/全局 errno | `Result<T, E>` 显式类型 |
| 忽略错误 | 容易 | 编译器警告未使用的 `Result` |
| 错误传播 | 手动 `if (err) return err` | `?` 运算符自动传播 |
| 资源释放 | 手动（易泄漏） | RAII：`File` 在作用域结束自动关闭 |

**知识点**：Rust 的 `Result` 类型将错误处理从"约定"提升为"类型系统强制"。`?` 运算符消除了 Go 的 `if err != nil` 冗余和 C 的嵌套错误检查。[→ 错误处理详解](../01_foundation/10_error_handling_basics.md)

</details>

---

## 四、抽象与零成本

### Q6. 以下 C++ 模板和 Rust 泛型的输出是否相同？零成本抽象的含义是什么？

```cpp
// C++
template<typename T>
T add(T a, T b) { return a + b; }

// Rust
fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：两者功能相同，但实现机制不同。

**编译方式对比**：

| 方面 | C++ 模板 | Rust 泛型 |
|:---|:---|:---|
| 类型检查 | 实例化时（可能导致后期错误） | 定义时（早期错误检测） |
| 单态化 | 是（每种类型生成一份代码） | 是 |
| 二进制体积 | 可能膨胀（重复代码） | 可能膨胀，但 LTO 可优化 |
| 错误信息 | 复杂（模板实例化堆栈） | 清晰（trait bound 失败） |
| 特化 | 完整支持 | `min_specialization`（不稳定） |

**零成本抽象的含义**：

> "你不需要为使用的抽象付出代价。"

```rust
fn add_i32(a: i32, b: i32) -> i32 { a + b }
fn add_generic<T: Add>(a: T, b: T) -> T { a + b }

// 编译后，add_generic::<i32> 和 add_i32 生成完全相同的机器码
```

**对比其他语言**：

| 语言 | 泛型实现 | 运行时开销 |
|:---|:---|:---:|
| C++ | 模板单态化 | 无 |
| Rust | 单态化 | 无 |
| Java | 类型擦除（Object） | 装箱/拆箱 |
| Go | 接口（interface{}） | 类型断言、间接调用 |
| C# | 运行时泛型 | 少量（JIT 优化后接近零） |

**知识点**：Rust 的零成本抽象意味着你可以使用高阶概念（迭代器、闭包、泛型）而不牺牲性能——编译器生成的代码与手写底层代码一样高效。[→ 零成本抽象详解](../03_advanced/08_zero_cost_abstractions.md)

</details>

---

## 五、综合对比

### Q7. 以下代码在 C、C++、Go、Rust 中的行为对比。

场景：创建一个包含 100 万个整数的数组，求和。

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

**C**：
```c
int* arr = malloc(1000000 * sizeof(int));
// 未初始化内存！arr[0] 可能是任意值
// 忘记 free → 内存泄漏
```

**C++**：
```cpp
std::vector<int> arr(1000000); // 零初始化
int sum = std::accumulate(arr.begin(), arr.end(), 0);
// 安全，但有堆分配开销
```

**Go**：
```go
arr := make([]int, 1000000) // 零初始化
sum := 0
for _, v := range arr { sum += v }
// 安全，但切片是堆分配的，GC 管理
```

**Rust**：
```rust
let arr = vec![0; 1_000_000]; // 零初始化，堆分配
let sum: i64 = arr.iter().map(|&x| x as i64).sum();
// 或零成本迭代器链：
let sum: i64 = (0..1_000_000).map(|x| x as i64).sum();
```

**对比总结**：

| 维度 | C | C++ | Go | Rust |
|:---|:---|:---|:---|:---|
| 安全性 | ❌ 手动管理 | ⚠️ 可能不安全 | ✅ GC 安全 | ✅ 编译期安全 |
| 性能 | ✅ 最高 | ✅ 高 | ⚠️ GC 开销 | ✅ 接近 C++ |
| 初始化 | ❌ 手动 | ✅ 自动 | ✅ 自动 | ✅ 自动 |
| 内存释放 | ❌ 手动 | ✅ RAII | ✅ GC | ✅ RAII |
| 溢出检查 | ❌ 无 | ❌ 无 | ❌ 无 | ✅ debug 模式 panic |

**知识点**：Rust 在安全性上接近 Go（自动内存管理、边界检查），在性能上接近 C++（零成本抽象、无 GC）。这是 Rust 独特定位的来源。[→ Rust vs C++ 详解](./01_rust_vs_cpp.md)

</details>

---

### Q8. 以下场景最适合哪种语言？为什么？

场景：开发一个需要直接操作硬件寄存器的嵌入式操作系统内核。

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

| 语言 | 适合度 | 原因 |
|:---|:---:|:---|
| C | ✅ 传统选择 | 成熟生态，所有嵌入式工具链支持 |
| C++ | ⚠️ 可用 | 复杂特性在裸机环境受限，RTTI/异常通常禁用 |
| Go | ❌ 不适合 | 需要运行时（GC、goroutine 调度器），无法裸机运行 |
| **Rust** | ✅ **最佳选择** | 内存安全 + 零成本 + 无运行时；Rust for Linux 项目验证 |

**Rust 的嵌入式优势**：

```rust
#![no_std]  // 不使用标准库（无堆分配器）
#![no_main]

use core::ptr;

const GPIO_BASE: *mut u32 = 0x4002_0000 as *mut u32;

#[no_mangle]
pub extern "C" fn _start() {
    unsafe {
        // 直接操作硬件寄存器
        ptr::write_volatile(GPIO_BASE.offset(0), 0x1);
    }
}
```

**Rust for Linux**：

- 截至 2026 年，Rust for Linux 仅剩 2 个不稳定特性待稳定化
- Debian 14 预计采用 Rust 作为内核开发语言之一
- Ferrocene 提供 ASIL B/SIL 2 认证工具链

**知识点**：Rust 正在从"系统编程语言"向"所有层次编程语言"扩展，从嵌入式到 Web 都有成熟的生态。[→ Rust for Linux 详解](../06_ecosystem/19_rust_for_linux.md)

</details>

---

### Q9. 以下代码在 Rust 和 C++ 中的生命周期管理对比。

**C++（智能指针）**：
```cpp
std::shared_ptr<int> p1 = std::make_shared<int>(42);
std::shared_ptr<int> p2 = p1;  // 引用计数 +1
// p1, p2 离开作用域 → 引用计数归零 → 内存释放
```

**Rust**：
```rust
let p1 = Rc::new(42);
let p2 = Rc::clone(&p1);  // 引用计数 +1
// p1, p2 离开作用域 → 引用计数归零 → 内存释放
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：两者行为相似，但 Rust 有额外的编译期保证。

**关键差异**：

| 方面 | C++ `shared_ptr` | Rust `Rc` |
|:---|:---|:---|
| 循环引用 | 导致内存泄漏 | 同样泄漏（需 `Weak` 解决） |
| 线程安全 | `shared_ptr` 本身线程安全（原子计数） | `Rc` 非线程安全；`Arc` 才是 |
| 自定义删除器 | 支持 | 通过 `Drop` trait |
| 运行时检查 | 无 | `Rc` 单线程限制在编译期强制执行 |

**Rust 的编译期优势**：

```rust
let p = Rc::new(42);
std::thread::spawn(move || {
    println!("{}", *p); // ❌ 编译错误！
});
```

C++ 的 `shared_ptr` 允许这样做（因为原子引用计数是线程安全的），但 Rust 的 `Rc` 在编译期阻止——迫使你在多线程场景使用 `Arc`。

**性能对比**：

- `std::shared_ptr`：通常两次堆分配（控制块 + 数据）
- `Rc<T>` / `Arc<T>`：一次堆分配（Rust 使用 `Box` 布局优化）

**知识点**：Rust 的智能指针设计在功能上接近 C++，但通过类型系统（`Send`/`Sync`）在编译期排除了整类并发错误。[→ 内存管理详解](../02_intermediate/03_memory_management.md)

</details>

---

### Q10. 以下代码在 Rust、Go、C++ 中的错误处理哲学对比。

场景：读取配置文件并解析为整数。

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

**C**：
```c
FILE* f = fopen("config.txt", "r");
if (!f) { perror("open"); return -1; }
char buf[100];
if (!fgets(buf, 100, f)) { fclose(f); return -1; }
int val = atoi(buf);  // 错误时返回 0，无法区分"0"和错误
fclose(f);
```

**C++**：
```cpp
try {
    std::ifstream f("config.txt");
    int val;
    f >> val;  // 错误时设置 failbit，不抛异常
    if (f.fail()) throw std::runtime_error("parse error");
} catch (const std::exception& e) {
    std::cerr << e.what() << std::endl;
}
```

**Go**：
```go
func readConfig() (int, error) {
    data, err := os.ReadFile("config.txt")
    if err != nil { return 0, err }
    val, err := strconv.Atoi(string(data))
    if err != nil { return 0, err }
    return val, nil
}
```

**Rust**：
```rust
fn read_config() -> Result<i32, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string("config.txt")?;
    let val: i32 = content.trim().parse()?;
    Ok(val)
}
```

**哲学对比**：

| 语言 | 哲学 | 优点 | 缺点 |
|:---|:---|:---|:---|
| C | 手动检查 | 零开销 | 易遗漏、易泄漏 |
| C++ | 异常 + 手动 | 灵活 | 异常开销、控制流隐式 |
| Go | 显式错误值 | 简单、明确 | 冗长（if err != nil） |
| Rust | `Result` + `?` | 显式 + 简洁 + 编译期强制 | 学习曲线 |

**知识点**：Rust 的错误处理结合了 Go 的显式和 C++ 的简洁，通过类型系统和 `?` 运算符实现了"显式但不冗长"的理想平衡。[→ 错误处理详解](../01_foundation/10_error_handling_basics.md)

</details>

---

## 六、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 跨语言对比已内化 | 阅读 [Rustonomicon](https://doc.rust-lang.org/nomicon/) 深入 FFI 和兼容层 |
| 7–9/10 | ✅ 核心差异掌握 | 用 Rust 重写一个 C/Go 项目，对比实现差异 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Rust vs C++](./01_rust_vs_cpp.md) · [Rust vs Go](./03_rust_vs_go.md) |
| 0–3/10 | 📚 建议重新开始 | 从 [Ownership](../01_foundation/01_ownership.md) 确认 Rust 核心，再读对比分析 |

---

> **权威来源**: [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [The Rust Programming Language — Ch19](https://doc.rust-lang.org/book/ch19-00-advanced-features.html) · [Rust vs Other Languages — Rust Book](https://doc.rust-lang.org/book/appendix-06-translation.html)
