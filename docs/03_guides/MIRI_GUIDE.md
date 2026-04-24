# Miri 使用指南

> 本文档对应 Rust 生产级工程实践体系阶段三 —— 内存安全检测。
> 参考: [Miri 官方文档](https://github.com/rust-lang/miri)、Microsoft Azure 安全编码规范、AWS Rust SDK 实践。

---

## 1. Miri 是什么？

**Miri**（Mid-level IR Interpreter）是 Rust 的未定义行为（Undefined Behavior, UB）检测工具。它通过解释执行 Rust 的中间表示（MIR）来检测代码中的内存安全问题。

### 为什么需要 Miri？

Rust 的所有权系统在编译期阻止了大多数内存错误，但 `unsafe` 代码块、原始指针操作、类型转换等仍然可能引入 UB：

| 问题类型 | 编译器能否检测 | Miri 能否检测 |
|---------|-------------|-------------|
|  use-after-free | ❌ | ✅ |
|  数据竞争 | ❌ | ✅ |
|  越界访问 | ⚠️ 部分（release 模式不检查） | ✅ |
|  未对齐访问 | ❌ | ✅ |
|  无效枚举值 | ❌ | ✅ |
|  违反 Stacked Borrows/Tree Borrows | ❌ | ✅ |

> **生产级要求**: Microsoft 的 Rust 安全指南和 AWS Rust SDK 均建议在 CI 中对包含 `unsafe` 的 crate 运行 Miri 测试。

---

## 2. 安装和基本使用

### 安装 Miri

```bash
# Miri 需要 Rust nightly 工具链
rustup component add miri --toolchain nightly

# 验证安装
cargo +nightly miri --version
```

### 基本命令

```bash
# 在单个 crate 上运行测试
cargo miri test -p c01_ownership_borrow_scope

# 在整个 workspace 上运行（仅限 Linux CI）
cargo miri test --workspace

# 运行特定测试
cargo miri test -p c10_networks test_name

# 运行二进制文件
cargo miri run -p c10_networks --bin net
```

### Miri 环境变量

| 环境变量 | 说明 | 推荐值 |
|---------|------|-------|
| `MIRIFLAGS` | 传递给 Miri 的选项 | 见下文 |
| `MIRI_BACKTRACE` |  Miri 错误回溯深度 | `1` |
| `RUST_MIN_STACK` | 栈大小（递归深度大时增加） | `8388608` |

---

## 3. Stacked Borrows vs Tree Borrows

### 3.1 Stacked Borrows（SB）

Rust 历史上使用的别名模型，由 Ralf Jung 提出。核心思想：**借用像栈一样工作**。

```rust
// Stacked Borrows 会拒绝此代码（即使它在 LLVM 层面是合法的）
let mut x = 5;
let raw = &mut x as *mut i32;
let _ref = &mut x;      // 新的 &mut 使旧的 raw 指针失效
unsafe { *raw = 10; }   // ❌ UB: 使用已失效的指针
```

**特点**:

- 更严格，能捕获更多潜在问题
- 但某些合法的 C 风格代码会被误判
- 作为基线测试使用，允许失败

### 3.2 Tree Borrows（TB）

Rust 正在过渡的新别名模型。核心思想：**借用像树一样分支**。

```rust
// Tree Borrows 允许此代码（更贴近实际硬件行为）
let mut x = 5;
let raw = &mut x as *mut i32;
let _ref = &mut x;      // 创建新分支
unsafe { *raw = 10; }   // ✅ TB 允许：只要没有真正冲突的使用
```

**特点**:

- 更宽松，减少误报
- 更精确地反映 LLVM/硬件的实际别名规则
- **推荐作为 CI 的主要检测模式**

### 3.3 模型对比

```rust
// 示例: 通过原始指针重新借用
fn reborrow_via_raw() {
    let mut data = [0u8; 8];
    let ptr = data.as_mut_ptr();

    unsafe {
        let a = std::slice::from_raw_parts_mut(ptr, 4);
        let b = std::slice::from_raw_parts_mut(ptr.add(4), 4);
        a[0] = 1;
        b[0] = 2;
    }
}

// SB: 可能需要 -Zmiri-disable-stacked-borrows
// TB: 无需额外标志即可通过
```

### 3.4 Miri 标志配置

```bash
# Tree Borrows（推荐，作为 CI 主要模式）
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-ignore-leaks" cargo miri test

# Stacked Borrows（基线对比）
MIRIFLAGS="-Zmiri-stacked-borrows -Zmiri-ignore-leaks" cargo miri test

# 严格模式（TB + 原始指针标签）
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-tag-raw-pointers -Zmiri-ignore-leaks" cargo miri test

# 禁用隔离（允许文件系统/网络操作，用于测试 IO）
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-disable-isolation" cargo miri test

# 检测数据竞争（需要单线程 Miri）
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-data-race-detector" cargo miri test
```

---

## 4. 10 个 UB 检测示例

### 示例 1: use-after-free（释放后使用）

```rust
// ❌ 错误代码
type BoxedInt = Box<i32>;

fn use_after_free() {
    let ptr: *const i32;
    {
        let boxed = Box::new(42);
        ptr = &*boxed;  // ptr 指向 boxed 的内容
    } // boxed 在这里 drop，内存被释放

    unsafe {
        println!("{}", *ptr); // ❌ UB: use-after-free
    }
}

// ✅ 正确代码
fn safe_access() {
    let boxed = Box::new(42);
    let val = *boxed;  // 先复制值
    drop(boxed);
    println!("{}", val); // ✅ 安全：访问的是复制的值
}
```

**Miri 输出**:

```
error: Undefined Behavior: pointer to alloc1406 was dereferenced after this allocation got freed
```

### 示例 2: 数据竞争

```rust
use std::thread;

// ❌ 错误代码
fn data_race() {
    static mut COUNTER: i32 = 0;

    let t1 = thread::spawn(|| unsafe {
        COUNTER += 1;  // 无同步的写操作
    });
    let t2 = thread::spawn(|| unsafe {
        COUNTER += 1;  // 无同步的写操作
    });

    t1.join().unwrap();
    t2.join().unwrap();
}

// ✅ 正确代码
use std::sync::atomic::{AtomicI32, Ordering};

fn no_data_race() {
    static COUNTER: AtomicI32 = AtomicI32::new(0);

    let t1 = thread::spawn(|| {
        COUNTER.fetch_add(1, Ordering::SeqCst);
    });
    let t2 = thread::spawn(|| {
        COUNTER.fetch_add(1, Ordering::SeqCst);
    });

    t1.join().unwrap();
    t2.join().unwrap();
}
```

**Miri 输出**:

```
error: Undefined Behavior: Data race detected between Read on thread `<unnamed>` and Write on thread `<unnamed>`
```

### 示例 3: 越界访问

```rust
// ❌ 错误代码
fn out_of_bounds() {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();

    unsafe {
        println!("{}", *ptr.add(100)); // ❌ UB: 越界访问
    }
}

// ✅ 正确代码
fn in_bounds() {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();

    unsafe {
        for i in 0..arr.len() {
            println!("{}", *ptr.add(i)); // ✅ 安全：在边界内
        }
    }
}
```

### 示例 4: 未对齐访问

```rust
// ❌ 错误代码
fn unaligned_access() {
    let bytes = [0u8; 8];
    let ptr = bytes.as_ptr() as *const u64;

    unsafe {
        println!("{}", *ptr); // ❌ UB: u64 需要 8 字节对齐
    }
}

// ✅ 正确代码
fn aligned_access() {
    let val: u64 = 42;
    let ptr = &val as *const u64;

    unsafe {
        println!("{}", *ptr); // ✅ 安全：正确对齐
    }
}
```

**Miri 输出**:

```
error: Undefined Behavior: accessing memory with alignment 1, but alignment 8 is required
```

### 示例 5: 无效枚举值

```rust
#[repr(u8)]
enum Color {
    Red = 0,
    Green = 1,
    Blue = 2,
}

// ❌ 错误代码
fn invalid_enum() {
    let raw: u8 = 100; // 不在枚举范围内的值
    let color: Color = unsafe { std::mem::transmute(raw) }; // ❌ UB: 无效枚举值

    match color {
        Color::Red => println!("red"),
        Color::Green => println!("green"),
        Color::Blue => println!("blue"),
    }
}

// ✅ 正确代码
fn valid_enum() {
    let raw: u8 = 1;
    let color = match raw {
        0 => Color::Red,
        1 => Color::Green,
        2 => Color::Blue,
        _ => panic!("invalid color value"),
    };
}
```

### 示例 6: 重叠的 mutable 引用

```rust
// ❌ 错误代码
fn overlapping_mut_refs() {
    let mut data = [1, 2, 3, 4];

    let a = &mut data[..2];
    let b = &mut data[1..3]; // ❌ 编译错误：重叠借用

    a[0] = 10;
    b[0] = 20;
}

// ❌ 通过 unsafe 绕过编译器检查
fn overlapping_via_raw() {
    let mut data = [1, 2, 3, 4];

    let ptr = data.as_mut_ptr();
    let a = unsafe { std::slice::from_raw_parts_mut(ptr, 2) };
    let b = unsafe { std::slice::from_raw_parts_mut(ptr.add(1), 2) }; // ❌ UB: 重叠的 mutable 引用

    a[0] = 10;
    b[0] = 20;
}
```

### 示例 7: 违反引用生命周期规则

```rust
// ❌ 错误代码
fn dangling_reference() -> &'static i32 {
    let local = 42;
    &local // ❌ 编译错误：返回局部变量的引用
}

// ❌ 通过 unsafe 绕过
fn dangling_via_raw() -> &'static i32 {
    let local = 42;
    let ptr = &local as *const i32;
    unsafe { &*ptr } // ❌ UB: 返回指向已释放栈帧的引用
}
```

### 示例 8: 类型混淆（Type Pun）

```rust
// ❌ 错误代码
fn type_pun() {
    let f: f32 = 1.5;
    let bits: u32 = unsafe { std::mem::transmute(f) }; // ⚠️ 通常安全，但需要小心

    // 更危险的场景：不同类型大小不同
    let x: u64 = 0xDEADBEEF;
    let y: u32 = unsafe { std::mem::transmute(x) }; // ❌ UB: 类型大小不匹配
}

// ✅ 正确代码
fn safe_type_conversion() {
    let f: f32 = 1.5;
    let bits = f.to_bits(); // ✅ 安全：使用标准库 API

    let x: u64 = 0xDEADBEEF;
    let y = x as u32; // ✅ 安全：显式截断转换
}
```

### 示例 9: 通过共享引用修改数据

```rust
// ❌ 错误代码
fn modify_via_shared_ref() {
    let x = Box::new(42);
    let shared = &x;
    let raw = &*x as *const i32 as *mut i32;

    unsafe {
        *raw = 100; // ❌ UB: 通过共享引用修改数据
    }

    println!("{}", shared);
}

// ✅ 正确代码
fn modify_via_interior_mutability() {
    use std::cell::Cell;

    let x = Cell::new(42);
    x.set(100); // ✅ 安全：Cell 允许内部可变性
    println!("{}", x.get());
}
```

### 示例 10: 未初始化的内存读取

```rust
// ❌ 错误代码
fn read_uninit() {
    let x: i32;
    println!("{}", x); // ❌ 编译错误：使用未初始化变量
}

// ❌ 通过 MaybeUninit 错误使用
fn read_uninit_unsafe() {
    use std::mem::{self, MaybeUninit};

    let x: MaybeUninit<i32> = MaybeUninit::uninit();
    let val = unsafe { x.assume_init() }; // ❌ UB: 读取未初始化的值
    println!("{}", val);
}

// ✅ 正确代码
fn safe_init() {
    let mut x = MaybeUninit::<i32>::uninit();

    unsafe {
        x.as_mut_ptr().write(42); // 先写入
        let val = x.assume_init(); // ✅ 安全：已初始化
        println!("{}", val);
    }
}
```

---

## 5. CI 集成

> ⚠️ **重要限制**: Miri 仅在 Linux 上完整支持。Windows 和 macOS 支持有限，不推荐在 CI 中使用。

### GitHub Actions 配置

参见 `.github/workflows/miri.yml`，本项目已配置：

```yaml
# 核心配置摘要
jobs:
  miri-tree-borrows:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
        with:
          components: miri, rust-src
      - run: cargo miri setup
      - run: cargo miri test --workspace --all-features
        env:
          MIRIFLAGS: "-Zmiri-tree-borrows -Zmiri-ignore-leaks"
```

### 按 crate 配置不同标志

```yaml
strategy:
  matrix:
    crate:
      - c01_ownership_borrow_scope
      - c05_threads
      - c10_networks
    include:
      - crate: c05_threads
        flags: "-Zmiri-tree-borrows -Zmiri-disable-isolation"
      - crate: c10_networks
        flags: "-Zmiri-tree-borrows -Zmiri-disable-isolation"
```

### 本地开发工作流

```bash
# 提交前快速检查（ Tree Borrows）
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test -p YOUR_CRATE

# 全面检查（所有模式）
./scripts/run_miri_tests.sh  # 如果有此脚本
```

---

## 6. 常见问题与解决方案

### Q: Miri 运行太慢怎么办？

A:

- 仅对包含 `unsafe` 的 crate 运行 Miri
- 使用 `--release` 不会加速 Miri（它解释执行 MIR）
- 在 CI 中分片运行（按 crate 并行）

### Q: Miri 报告了 "unsupported operation"？

A: 某些系统调用 Miri 不支持：

- 使用 `-Zmiri-disable-isolation` 允许部分系统调用
- 对于网络操作，考虑使用 mock

### Q: 我的代码在 Miri 中报错但在实际运行正常？

A:

- Stacked Borrows 可能有误报，尝试 Tree Borrows
- 但大多数 Miri 报错都代表真实的 UB，即使当前未触发崩溃

### Q: 如何处理 Miri 中的内存泄漏报告？

A:

- 使用 `-Zmiri-ignore-leaks` 忽略泄漏（推荐用于测试）
- 或使用 `-Zmiri-disable-leak-backtraces` 减少输出噪音

---

## 7. 参考资源

- [Miri 官方 README](https://github.com/rust-lang/miri)
- [Tree Borrows 论文](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)
- [Rustonomicon - 未定义行为](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)
- [Microsoft Rust 安全指南](https://docs.microsoft.com/en-us/windows/dev-environment/rust/rust-hardening)
- [AWS Rust SDK 开发规范](https://github.com/awslabs/aws-sdk-rust/blob/main/CONTRIBUTING.md)
