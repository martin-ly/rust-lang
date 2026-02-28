# 常量求值规则形式化

> **文档状态**: ✅ 完整  
> **理论级别**: L2 - 形式化数学  
> **适用范围**: Rust const 语义

---

## 1. 常量上下文分类

### Def CONST-CTX1（常量上下文）

以下位置构成**常量上下文** (Const Context)：

$$
\text{ConstCtx} ::= \text{const } x: T = e \mid \text{static } x: T = e \mid [T; e] \mid \text{enum } E \{ A = e \} \mid \text{const fn } f() \{ e \}
$$

| 上下文类型 | 示例 | 说明 |
|-----------|------|------|
| `const` 项 | `const X: u32 = 42;` | 编译期常量 |
| `static` 项 | `static X: u32 = 42;` | 全局静态变量初始化 |
| 数组长度 | `[u32; 10]` | 编译期确定的数组大小 |
| 枚举判别式 | `enum E { A = 1 }` | 枚举变体值 |
| `const fn` 体 | `const fn f() -> u32 { 42 }` | 常量函数体 |

---

## 2. const fn 语义

### Def CONST-FN1（const fn 允许操作）

在 const fn 中允许的操作集合：

$$
\text{ConstOp} ::= \text{算术} \mid \text{逻辑} \mid \text{控制流} \mid \text{不可变借用} \mid \text{const 调用}
$$

```rust
// ✅ 允许的操作
const fn allowed_operations(x: i32) -> i32 {
    // 算术运算
    let a = x + 1;
    let b = x * 2;
    
    // 控制流
    if a > 0 {
        a
    } else {
        b
    }
    
    // 匹配
    match x {
        0 => 1,
        n => n + 1,
    }
    
    // 不可变借用
    let r = &x;
    *r
}
```

### Def CONST-FN2（const fn 禁止操作）

$$
\text{NonConstOp} ::= \text{I/O} \mid \text{堆分配} \mid \text{可变静态} \mid \text{非 const 调用}
$$

```rust
// ❌ 禁止的操作
const fn forbidden_operations() {
    // I/O
    println!("hello");      // ❌ 不允许
    
    // 堆分配
    let v = vec![1, 2, 3];  // ❌ 不允许
    
    // 可变静态
    static mut X: i32 = 0;
    X = 1;                  // ❌ 不允许
    
    // 非 const 调用
    std::time::now();       // ❌ 不允许
}
```

---

## 3. MIR 常量求值

### Def MIR-EVAL1（MIR 常量求值器）

MIR 常量求值是编译期解释器，执行以下步骤：

1. **翻译**: Rust AST → MIR
2. **解释**: 逐步执行 MIR 指令
3. **限制**: 检测无限循环/过大内存使用
4. **结果**: 产生常量值或编译错误

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  Rust 代码   │ --> │    MIR      │ --> │  常量值      │
│  (const ctx) │     │  (中间表示)  │     │  或错误      │
└─────────────┘     └─────────────┘     └─────────────┘
                              │
                              v
                       ┌─────────────┐
                       │  MIR 解释器  │
                       │ • 算术运算   │
                       │ • 内存操作   │
                       │ • 调用解析   │
                       └─────────────┘
```

### Thm EVAL-BOUND1（求值限制定理）

常量求值受以下限制约束：

$$
\begin{aligned}
&\text{循环迭代} \leq 10^6 \\
&\text{递归深度} \leq 1024 \\
&\text{内存分配} \leq \text{平台限制}
\end{aligned}
$$

超过任一限制将导致编译错误。

---

## 4. 常量泛型求值

### Def CONST-GEN1（常量泛型形式化）

常量泛型参数 $N$ 的类型：

$$
\text{ConstParam} ::= \text{const } N: \text{IntegerType}
$$

**类型规则**:

$$
\frac{\Gamma \vdash N: \text{u32} \quad \text{Eval}_c(N) = v}{\Gamma \vdash [T; N]: \text{Array}(T, v)}
$$

### Thm CONST-TY1（常量泛型类型安全）

若 $e$ 在常量上下文中求值为 $v$，则类型 $T[e]$ 良构当且仅当 $v$ 满足 $T$ 的约束：

$$
\frac{\Gamma \vdash e: \text{usize} \quad \text{Eval}_c(e) = v \quad v \geq 0}{\Gamma \vdash [T; e]: \text{WellFormed}}
\quad\text{(T-CONSTARR)}
$$

```rust
// 示例：常量泛型
struct Array<T, const N: usize>([T; N]);

// ✅ 有效
let a: Array<i32, 5> = Array([0; 5]);

// ❌ 编译错误（负值）
let b: Array<i32, -1> = ...;
// error: expected usize, found isize
```

---

## 5. const_eval_select

### Def CONST-SELECT1（条件常量求值）

`const_eval_select` 允许在 const fn 中根据求值上下文选择不同实现：

$$
\text{const\_eval\_select}(\text{at\_const}, \text{at\_runtime}) = 
\begin{cases}
\text{at\_const} & \text{if 在常量上下文} \\
\text{at\_runtime} & \text{否则}
\end{cases}
$$

```rust
#![feature(const_eval_select)]

use std::intrinsics::const_eval_select;

// 常量实现（纯计算）
const fn const_impl(x: i32) -> i32 {
    x + 1
}

// 运行时实现（可以使用运行时特性）
fn runtime_impl(x: i32) -> i32 {
    println!("runtime!");
    x + 1
}

const fn add_one(x: i32) -> i32 {
    const_eval_select((x,), const_impl, runtime_impl)
}

// 常量上下文：使用 const_impl
const RESULT: i32 = add_one(5);

// 运行时上下文：使用 runtime_impl
fn main() {
    let x = add_one(5);  // 打印 "runtime!"
}
```

---

## 6. 形式化总结

### 常量求值判定

$$
\text{ConstEval}(e) = 
\begin{cases}
v & \text{if } e \xrightarrow{\text{MIR}}^{*} v \text{ (终止)} \\
\bot & \text{if } e \text{ 违反限制或发散}
\end{cases}
$$

### 类型系统交互

常量求值与类型系统紧耦合：

1. **数组类型**: `[T; N]` 的 $N$ 必须可求值
2. **常量泛型**: `Foo<N>` 的 $N$ 必须可求值
3. **关联常量**: `<T as Trait>::CONST` 必须可求值

---

**最后更新**: 2026-02-28
