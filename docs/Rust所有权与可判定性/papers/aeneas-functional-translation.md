# Aeneas: 功能翻译视角的Rust验证

> Aeneas: Rust Verification by Functional Translation (Ho & Protzenko, ICFP 2022/2024)

---

## 1. 概述

### 核心思想

Aeneas将**Rust翻译成纯函数式语言**，利用所有权信息消除指针和内存，实现**零开销的形式化验证**。

```text
Rust程序
    ↓
LLBC (Low-Level Borrow Calculus) 中间表示
    ↓
功能翻译
    ↓
纯函数式程序 (F*, Coq, HOL4, Lean)
    ↓
定理证明器验证
```

---

## 2. LLBC: 低级借用演算

### 2.1 设计哲学

LLBC是**基于值的语义**，没有内存/地址概念：

```rust
// Rust
let mut x = 5;
let r = &mut x;
*r = 6;

// LLBC（概念性）
let x = 5;
let (x, r) = borrow_mut(x);  // x被"借用"，返回新x和借用标记
let x = write(r, 6);          // 通过借用写入，返回新x
```

### 2.2 关键特性

| 特性 | 说明 |
|------|------|
| 无内存 | 只有值，没有堆/栈概念 |
| 无指针 | 借用通过标记表示 |
| 可变状态 | 通过状态传递实现 |
| 贷款跟踪 | 编译期跟踪借用关系 |

---

## 3. 功能翻译

### 3.1 翻译示例

```rust
// Rust
fn increment(x: &mut u32) {
    *x += 1;
}

fn main() {
    let mut n = 5;
    increment(&mut n);
    assert!(n == 6);
}
```

```ocaml
(* 翻译到F* *)
let increment (x: u32) : u32 =
    x + 1

let main () : unit =
    let n = 5 in
    let n = increment n in
    assert (n = 6)
```

### 3.2 翻译规则

| Rust | 翻译后 |
|------|--------|
| `&x` | 值传递（Copy） |
| `&mut x` | 状态传递（新值） |
| `*r = v` | 函数返回新值 |
| `Box<T>` | 直接展开为T |

---

## 4. 借用检查实现

### 4.1 符号执行

Aeneas使用**符号执行**实现借用检查：

```text
符号状态：变量 → 符号值

执行步骤：
1. 跟踪每个变量的所有权状态
2. 验证借用规则
3. 检测冲突使用
```

### 4.2 与rustc的关系

```text
Rust源码
    ↓
rustc前端（HIR/MIR）
    ↓
Aeneas解析MIR
    ↓
LLBC表示
    ↓
符号执行验证
```

**关键发现：**

- Aeneas的符号执行与rustc借用检查等价
- 证明了借用检查的正确性

---

## 5. 后端支持

### 5.1 多后端输出

Aeneas支持翻译成：

- **F***: 主要目标，支持SMT自动化
- **Coq**: 交互式证明
- **HOL4**: 高阶逻辑
- **Lean**: 新兴证明助手

### 5.2 验证能力

```rust
// Rust函数
#[requires(n >= 0)]
#[ensures(result == n * (n + 1) / 2)]
fn sum(n: u32) -> u32 {
    if n == 0 { 0 } else { n + sum(n - 1) }
}
```

```fstar
(* F*翻译 *)
let rec sum (n: u32) : u32 =
    if n = 0 then 0 else n + sum (n - 1)

// 自动证明前置/后置条件
```

---

## 6. 理论基础

### 6.1 模拟关系

Aeneas证明了：

```text
LLBC#（符号执行） ≈ LLBC（实际语义）

即：符号执行正确实现了借用检查
```

### 6.2 功能翻译正确性

```text
Rust程序  →  功能程序
   ↓              ↓
安全        等价的安全
```

---

## 7. 实际应用

### 7.1 验证案例

Aeneas已验证：

- 基础数据结构（List, Tree）
- 查找算法（二分查找）
- 排序算法（归并排序）
- 加密原语

### 7.2 与Prusti比较

| 特性 | Aeneas | Prusti |
|------|--------|--------|
| 方法 | 功能翻译 | 分离逻辑 |
| 后端 | F*/Coq/HOL4/Lean | Viper |
| 自动化 | 高（F*+SMT） | 中等 |
| 覆盖 | 安全Rust | 安全Rust |
| 独特优势 | 无内存模型 | 工业级验证器 |

---

## 8. 总结

Aeneas的贡献：

1. **LLBC**: 无内存的中间表示
2. **功能翻译**: 消除指针，简化验证
3. **借用检查证明**: 符号执行实现验证
4. **多后端**: 支持多种证明助手

**意义**：为Rust验证提供了新的技术路径，特别适合函数式编程背景的验证者。

---

*Aeneas代表了Rust形式化验证的新方向：通过所有权信息，将命令式程序翻译成纯函数式程序，利用成熟的函数式验证技术。*
