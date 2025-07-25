# Rust Trait系统形式化理论与证明

## 1. 形式化语法与语义

### 1.1 Trait语法（BNF）

```text
<trait> ::= trait <ident> { <item>* }
<impl>  ::= impl <trait> for <type> { <item>* }
<bound> ::= <type>: <trait>
```

### 1.2 Trait Bound与推理

- Trait Bound：类型$T$满足trait$Tr$，记作$T:Tr$。
- 约束传递：若$T:Tr_1$且$Tr_1:Tr_2$，则$T:Tr_2$。

#### 形式化规则

- $\Gamma \vdash T:Tr$ 表示在上下文$\Gamma$下$T$实现$Tr$。
- 推理规则：
  - $\frac{\Gamma \vdash T:Tr_1 \quad \Gamma \vdash Tr_1:Tr_2}{\Gamma \vdash T:Tr_2}$

### 1.3 Trait对象与对象安全

- Trait对象：`dyn Tr`，仅对象安全trait可用作trait对象。
- 对象安全条件：
  - 不含泛型方法
  - 不含`Self: Sized`约束

#### 定理1（对象安全性）
>
> 仅对象安全trait可用于trait对象。

**证明思路**：

- 编译器静态检查trait定义，违反对象安全条件则报错。

### 1.4 自动推导与特化

- Rust支持自动推导（如`Clone`, `Debug`等）
- 特化（specialization）允许为更具体类型提供更优实现。

#### 定理2（自动推导一致性）
>
> 自动推导的trait实现与手动实现不冲突。

**证明思路**：

- 编译器禁止重复实现同一trait。

### 1.5 形式化证明示例

#### 定理3（trait bound一致性）
>
> 若$T:Tr$且$Tr$要求$T:Tr'$, 则$T:Tr'$。

**证明**：

- 由trait定义的bound传递性，类型系统自动推导。

#### 定理4（trait实现唯一性）
>
> 任意具体类型$T$对同一trait$Tr$最多有一个impl。

**证明**：

- Rust禁止孤儿规则（orphan rule）和重复实现。

## 2. 工程案例与伪代码

```rust
trait Display { fn fmt(&self) -> String; }
impl Display for i32 { fn fmt(&self) -> String { self.to_string() } }
fn print<T: Display>(x: T) { println!("{}", x.fmt()); }

// trait对象
fn print_dyn(x: &dyn Display) { println!("{}", x.fmt()); }
```

## 3. 参考文献

- Rust Reference: Traits, Object Safety
- RustBelt, TAPL, PFPL相关章节

---
> 本节为Rust trait系统的理论补充，后续可继续扩展trait合成、负trait、自动推导等高级特性。
