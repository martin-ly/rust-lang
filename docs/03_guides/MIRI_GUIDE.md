# Miri 使用指南：检测 Rust 未定义行为（UB）

> **工具**: Miri（Rust 的解释型 UB 检测器）
> **适用版本**: Rust nightly（`rustup component add miri`）
> **权威来源**: [rustc-dev-guide Miri 章节](https://rustc-dev-guide.rust-lang.org/miri.html) | [Miri README](https://github.com/rust-lang/miri)

---

## 📑 目录
>
- [Miri 使用指南：检测 Rust 未定义行为（UB）](#miri-使用指南检测-rust-未定义行为ub)
  - [📑 目录](#-目录)
  - [一、什么是 Miri？](#一什么是-miri)
    - [Miri vs 其他工具](#miri-vs-其他工具)
  - [二、安装与基础使用](#二安装与基础使用)
    - [2.1 安装 Miri](#21-安装-miri)
    - [2.2 运行测试](#22-运行测试)
    - [2.3 常用环境变量](#23-常用环境变量)
  - [三、十大 UB 检测示例](#三十大-ub-检测示例)
    - [示例 1：使用未初始化内存](#示例-1使用未初始化内存)
    - [示例 2：违反可变借用唯一性（Stacked Borrows）](#示例-2违反可变借用唯一性stacked-borrows)
    - [示例 3：通过共享引用修改数据（内部可变性违规）](#示例-3通过共享引用修改数据内部可变性违规)
    - [示例 4：悬空指针解引用](#示例-4悬空指针解引用)
    - [示例 5：对齐违规](#示例-5对齐违规)
    - [示例 6：越界指针算术（即使不解引用也是 UB）](#示例-6越界指针算术即使不解引用也是-ub)
    - [示例 7：无效枚举判别式](#示例-7无效枚举判别式)
    - [示例 8：双重释放](#示例-8双重释放)
    - [示例 9：数据竞争（实验性检测）](#示例-9数据竞争实验性检测)
    - [示例 10：Strict Provenance 违规（指针\<-\>整数转换）](#示例-10strict-provenance-违规指针-整数转换)
  - [四、Stacked Borrows vs Tree Borrows](#四stacked-borrows-vs-tree-borrows)
    - [何时使用 Tree Borrows？](#何时使用-tree-borrows)
  - [五、在 CI 中集成 Miri](#五在-ci-中集成-miri)
  - [六、常见陷阱与解决方案](#六常见陷阱与解决方案)
  - [七、学习路径建议](#七学习路径建议)
  - [相关概念](#相关概念)

## 一、什么是 Miri？
>
> **[来源: Rust Official Docs]**

Miri 是 Rust 的一个**解释器**，它运行 Rust 的中间表示（MIR）并在执行过程中检测**未定义行为（Undefined Behavior, UB）**。与 Valgrind、ASan 等工具不同，Miri 专注于 Rust 特有的内存模型问题：

- **违反借用规则**（Stacked Borrows / Tree Borrows）
- **使用未初始化内存**
- **数据竞争**（实验性支持）
- **对齐违规**
- **越界指针算术**
- **无效枚举判别式**
- **双重释放 / 使用-after-free**

### Miri vs 其他工具
>
> **[来源: Rust Official Docs]**

| 工具 | 检测目标 | Rust 特异性 | 运行时开销 |
|------|----------|-------------|------------|
| **Miri** | UB（借用规则、未初始化、对齐等） | ⭐⭐⭐ 极高 | 极慢（解释执行） |
| **AddressSanitizer (ASan)** | 内存错误（越界、use-after-free） | ⭐ 低 | 中等（2-3x） |
| **ThreadSanitizer (TSan)** | 数据竞争 | ⭐ 低 | 高（5-15x） |
| **Valgrind (Memcheck)** | 内存错误 | ⭐ 低 | 极慢（10-50x） |
| **loom** | 并发执行路径探索 | ⭐⭐ 高 | 指数级 |

---

## 二、安装与基础使用
>
> **[来源: Rust Official Docs]**

### 2.1 安装 Miri
>
> **[来源: Rust Official Docs]**

```bash
# 需要 nightly 工具链
rustup toolchain install nightly
rustup component add miri --toolchain nightly

# 设置 nightly 为默认（可选）
rustup default nightly
```

### 2.2 运行测试
>
> **[来源: Rust Official Docs]**

```bash
# 运行当前 crate 的所有测试（通过 Miri 解释器）
cargo miri test

# 运行特定测试
cargo miri test test_name

# 运行示例
cargo miri run --example example_name

# 运行二进制
cargo miri run --bin bin_name
```

### 2.3 常用环境变量
>
> **[来源: Rust Official Docs]**

```bash
# 启用数据竞争检测（实验性，可能误报）
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test

# 禁用隔离（允许文件系统、环境变量访问）
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test

# 使用 Tree Borrows 代替 Stacked Borrows（更 permissive，推荐）
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 设置预emption 频率（并发测试）
MIRIFLAGS="-Zmiri-preemption-rate=0.1" cargo miri test

# 检查内存泄漏
cargo miri test
```

---

## 三、十大 UB 检测示例
>
> **[来源: Rust Official Docs]**

### 示例 1：使用未初始化内存
>
> **[来源: Rust Official Docs]**

```rust
// ❌ 错误代码
fn use_uninit() -> i32 {
    let x: i32;
    unsafe { x } // UB: 读取未初始化值
}

// ✅ 正确代码
fn use_init() -> i32 {
    let x: i32 = 0;
    x
}
```

**Miri 报错**：

```
error: Undefined Behavior: interpreting allocation ... as i32,
but the data is uninitialized
```

### 示例 2：违反可变借用唯一性（Stacked Borrows）
>
> **[来源: Rust Official Docs]**

```rust
// ❌ 错误代码
fn mutable_alias() {
    let mut x = 5;
    let r1 = &mut x;
    let r2 = &mut x; // 与 r1 同时存在！
    unsafe {
        println!("{}", *r1); // UB: r1 已被 r2 失效
    }
}

// ✅ 正确代码
fn no_alias() {
    let mut x = 5;
    {
        let r1 = &mut x;
        *r1 += 1;
    }
    let r2 = &mut x;
    *r2 += 1;
}
```

**Miri 报错**（Stacked Borrows 模式）：

```
error: Undefined Behavior: no item granting read access ...
```

### 示例 3：通过共享引用修改数据（内部可变性违规）
>
> **[来源: Rust Official Docs]**

```rust
// ❌ 错误代码
fn modify_via_shared() {
    let x = 42;
    let r = &x;
    unsafe {
        *(r as *const i32 as *mut i32) = 0; // UB!
    }
}

// ✅ 正确代码：使用 Cell/RefCell/Atomic
fn modify_with_interior_mutability() {
    use std::cell::Cell;
    let x = Cell::new(42);
    x.set(0); // ✅ 合法
}
```

### 示例 4：悬空指针解引用
>
> **[来源: Rust Official Docs]**

```rust
// ❌ 错误代码
fn dangling_pointer() {
    let ptr: *const i32;
    {
        let x = 42;
        ptr = &x;
    } // x 在此处 drop
    unsafe {
        println!("{}", *ptr); // UB: 悬空指针
    }
}

// ✅ 正确代码
fn valid_pointer() {
    let x = Box::new(42);
    let ptr: *const i32 = &*x;
    unsafe {
        println!("{}", *ptr); // ✅ x 仍然存活
    }
}
```

### 示例 5：对齐违规

```rust
// ❌ 错误代码
fn misaligned_access() {
    let bytes = [0u8; 8];
    let ptr = bytes.as_ptr().offset(1);
    let _val: &u64 = unsafe { &*(ptr as *const u64) }; // UB: 未对齐
}

// ✅ 正确代码
fn aligned_access() {
    let val: u64 = 0;
    let ptr = &val as *const u64;
    unsafe {
        let _ref: &u64 = &*ptr; // ✅ 对齐
    }
}
```

### 示例 6：越界指针算术（即使不解引用也是 UB）

```rust
// ❌ 错误代码
fn out_of_bounds_ptr() {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();
    let _bad = unsafe { ptr.offset(5) }; // UB: 超出 allocated object 范围
}

// ✅ 正确代码
fn in_bounds_ptr() {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();
    let _ok = unsafe { ptr.offset(2) }; // ✅ 在范围内
    let _one_past = unsafe { ptr.offset(3) }; // ✅ 允许指向最后一个元素之后
}
```

### 示例 7：无效枚举判别式

```rust
#[repr(u8)]
enum Color { Red = 1, Green = 2, Blue = 3 }

// ❌ 错误代码
fn invalid_discriminant() {
    let raw: u8 = 99;
    let _color: Color = unsafe { std::mem::transmute(raw) }; // UB: 99 不是有效判别式
}

// ✅ 正确代码
fn valid_discriminant() {
    let raw: u8 = 2;
    let color: Color = unsafe { std::mem::transmute(raw) }; // ✅ Green = 2
}
```

### 示例 8：双重释放

```rust
// ❌ 错误代码
fn double_free() {
    let ptr = Box::into_raw(Box::new(42));
    unsafe {
        drop(Box::from_raw(ptr));
        drop(Box::from_raw(ptr)); // UB: 双重释放
    }
}

// ✅ 正确代码
fn single_free() {
    let ptr = Box::into_raw(Box::new(42));
    unsafe {
        drop(Box::from_raw(ptr)); // ✅ 仅释放一次
    }
}
```

### 示例 9：数据竞争（实验性检测）

```rust
// ❌ 错误代码
fn data_race() {
    use std::thread;
    let mut x = 0;
    let ptr = &mut x as *mut i32;

    thread::spawn(move || unsafe {
        *ptr = 1; // 线程 A 写
    });

    unsafe {
        *ptr = 2; // 线程 B 写（主线程）
    }
}

// ✅ 正确代码
fn no_data_race() {
    use std::sync::atomic::{AtomicI32, Ordering};
    let x = AtomicI32::new(0);

    std::thread::scope(|s| {
        s.spawn(|| x.store(1, Ordering::Relaxed));
        s.spawn(|| x.store(2, Ordering::Relaxed));
    });
}
```

### 示例 10：Strict Provenance 违规（指针<->整数转换）

```rust
// ❌ 错误代码（在启用 strict provenance 时）
fn ptr_int_roundtrip() {
    let x = 42;
    let ptr: *const i32 = &x;
    let addr = ptr as usize;
    let _restored: *const i32 = addr as *const i32; // 语义模糊
}

// ✅ 正确代码（使用 with_exposed_provenance / expose_provenance）
fn proper_ptr_provenance() {
    let x = 42;
    let ptr: *const i32 = &x;
    let addr = ptr.expose_provenance();
    let _restored: *const i32 = std::ptr::with_exposed_provenance(addr);
}
```

---

## 四、Stacked Borrows vs Tree Borrows

Rust 有两种内存别名模型：

| 模型 | 特点 | Miri 启动方式 |
|------|------|---------------|
| **Stacked Borrows** | 更严格， legacy 默认模型 | `cargo miri test`（默认） |
| **Tree Borrows** | 更宽松，更符合实际代码直觉 | `MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test` |

### 何时使用 Tree Borrows？

- 代码使用复杂的自引用结构
- 需要与 C/FFI 代码交互的指针
- Stacked Borrows 产生看似"不合理"的误报时

**注意**: Tree Borrows 是 Rust 内存模型的未来方向（PLDI 2025 论文），建议新项目优先使用。

---

## 五、在 CI 中集成 Miri

```yaml
# .github/workflows/miri.yml
name: Miri

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install Miri
        run: |
          rustup toolchain install nightly
          rustup component add miri --toolchain nightly
          rustup override set nightly
      - name: Run Miri tests
        run: cargo miri test
        env:
          MIRIFLAGS: -Zmiri-tree-borrows -Zmiri-disable-isolation
```

---

## 六、常见陷阱与解决方案

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| Miri 运行极慢 | 解释执行 | 仅对 `unsafe` 模块和并发测试运行 Miri |
| 文件系统访问报错 | Miri 默认隔离 | `MIRIFLAGS="-Zmiri-disable-isolation"` |
| 时间相关测试失败 | Miri 模拟时间 | 使用 `std::time::Instant` 而非系统时间 |
| FFI/C 代码报错 | Miri 不理解 C 代码 | 用 `-Zmiri-disable-isolation` 或跳过 FFI 测试 |
| Stacked Borrows 误报 | 过于严格的别名分析 | 切换到 Tree Borrows |

---

## 七、学习路径建议

1. **入门**：对现有 `unsafe` 代码运行 `cargo miri test`
2. **进阶**：理解 Stacked Borrows / Tree Borrows 输出信息
3. **深入**：阅读 [Rustonomicon](https://doc.rust-lang.org/nomicon/) 中的内存模型章节
4. **专家**：阅读 [PLDI 2025 Tree Borrows 论文](https://pldi25.sigplan.org/)

---

> **总结**: Miri 是 Rust `unsafe` 代码的"守门人"。任何包含 `unsafe` 块的 crate 都应该在 CI 中运行 Miri 测试。记住：**Miri 通过不等于没有 Bug，但 Miri 报错一定意味着 UB**。

---

> **权威来源**: [rustc-dev-guide Miri 章节](https://rustc-dev-guide.rust-lang.org/miri.html), [Miri README](https://github.com/rust-lang/miri), [PLDI 2025 Tree Borrows](https://pldi25.sigplan.org/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Miri 官方文档来源标注、PLDI 2025 Tree Borrows 学术引用 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念

- [上级目录](../README.md)
