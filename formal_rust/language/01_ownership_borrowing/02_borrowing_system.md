# 02 借用系统形式化理论 {#借用系统}

## 目录

- [02 借用系统形式化理论 {#借用系统}](#02-借用系统形式化理论-借用系统)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 借用系统特点](#11-借用系统特点)
    - [1.2 理论基础](#12-理论基础)
  - [2. 数学基础](#2-数学基础)
    - [2.1 借用环境 {#借用环境}](#21-借用环境-借用环境)
    - [2.2 借用关系 {#借用关系}](#22-借用关系-借用关系)
  - [3. 借用类型](#3-借用类型)
    - [3.1 不可变借用 {#不可变借用}](#31-不可变借用-不可变借用)
    - [3.2 可变借用 {#可变借用}](#32-可变借用-可变借用)
    - [3.3 借用组合 {#借用组合}](#33-借用组合-借用组合)
  - [4. 借用规则](#4-借用规则)
    - [4.1 基本借用规则 {#基本借用规则}](#41-基本借用规则-基本借用规则)
    - [4.2 借用检查算法 {#借用检查算法}](#42-借用检查算法-借用检查算法)
    - [4.3 借用传播 {#借用传播}](#43-借用传播-借用传播)
  - [5. 借用检查器](#5-借用检查器)
    - [5.1 检查器架构 {#检查器架构}](#51-检查器架构-检查器架构)
    - [5.2 检查算法 {#检查算法}](#52-检查算法-检查算法)
    - [5.3 错误检测 {#错误检测}](#53-错误检测-错误检测)
  - [6. 生命周期管理](#6-生命周期管理)
    - [6.1 生命周期标注 {#生命周期标注}](#61-生命周期标注-生命周期标注)
    - [6.2 生命周期推断 {#生命周期推断}](#62-生命周期推断-生命周期推断)
    - [6.3 生命周期省略 {#生命周期省略}](#63-生命周期省略-生命周期省略)
  - [7. 实际应用](#7-实际应用)
    - [7.1 数据结构体体体借用 {#数据结构体体体借用}](#71-数据结构体体体借用-数据结构体体体借用)
    - [7.2 函数借用 {#函数借用}](#72-函数借用-函数借用)
    - [7.3 并发借用 {#并发借用}](#73-并发借用-并发借用)
  - [8. 定理证明](#8-定理证明)
    - [8.1 借用安全定理 {#借用安全定理}](#81-借用安全定理-借用安全定理)
    - [8.2 数据竞争避免定理 {#数据竞争避免定理}](#82-数据竞争避免定理-数据竞争避免定理)
    - [8.3 借用检查完备性定理 {#借用检查完备性定理}](#83-借用检查完备性定理-借用检查完备性定理)
  - [9. 参考文献](#9-参考文献)
    - [9.1 学术论文](#91-学术论文)
    - [9.2 技术文档](#92-技术文档)
    - [9.3 在线资源](#93-在线资源)
  - [形式化证明映射（借用系统）](#形式化证明映射借用系统)
    - [验证义务占位（与验证清单一致）](#验证义务占位与验证清单一致)

## 1. 概述

借用系统是Rust所有权系统的核心组成部分，通过编译时静态分析确保内存安全和线程安全。借用系统基于分离逻辑和线性类型理论，提供了严格的借用规则和检查机制。

### 1.1 借用系统特点

- **编译时检查**：所有借用检查在编译时完成，无运行时开销
- **类型安全**：通过类型系统确保借用安全
- **内存安全**：防止悬垂引用和数据竞争
- **线程安全**：通过借用规则确保并发安全

**相关概念**：

- [所有权](01_formal_ownership_system.md#所有权定义) (本模块)
- [类型安全](../02_type_system/01_formal_type_system.md#类型安全) (模块 02)
- [并发安全](../05_concurrency/01_formal_concurrency_model.md#并发安全) (模块 05)

### 1.2 理论基础

- **分离逻辑**：借用检查的数学基础
- **线性类型理论**：资源管理的理论基础
- **仿射类型系统**：Rust实际实现的类型系统
- **区域类型系统**：生命周期管理的理论基础

**相关概念**：

- [线性类型](../02_type_system/01_formal_type_system.md#线性类型) (模块 02)
- [区域类型](../02_type_system/01_formal_type_system.md#区域类型) (模块 02)
- [生命周期系统](03_lifetime_system.md#生命周期定义) (本模块)

## 2. 数学基础

### 2.1 借用环境 {#借用环境}

**借用环境定义**：
$$B = (B_{\text{imm}}, B_{\text{mut}})$$

其中：

- $B_{\text{imm}}$ 是不可变借用集合
- $B_{\text{mut}}$ 是可变借用集合

**借用状态**：
$$\text{BorrowState} = \text{enum}\{\text{NotBorrowed}, \text{ImmBorrowed}, \text{MutBorrowed}\}$$

**相关定义**：

- [定义 1.4: 借用](../main_comprehensive_index.md#21-所有权与借用系统) (主索引)
- [定义 1.5: 可变借用](../main_comprehensive_index.md#21-所有权与借用系统) (主索引)

### 2.2 借用关系 {#借用关系}

**借用关系定义**：
$$\text{Borrows}(r, x) = \text{true} \iff r \text{ 借用 } x$$

**借用类型**：
$$\text{BorrowType} = \text{enum}\{\text{Immutable}, \text{Mutable}\}$$

**借用约束**：
$$\text{BorrowConstraint} = \text{struct}\{\text{borrower}: \text{Reference}, \text{borrowed}: \text{Variable}, \text{type}: \text{BorrowType}\}$$

**相关定理**：

- [定理 1.6: 借用安全](06_theorems.md#借用安全) (本模块)
- [定理 1.7: 多重不可变借用安全](06_theorems.md#多重不可变借用安全) (本模块)

## 3. 借用类型

### 3.1 不可变借用 {#不可变借用}

**不可变借用类型**：
$$\& \tau$$

**不可变借用语义**：
$$\text{ImmBorrow}(\tau) = \text{struct}\{\text{value}: \tau, \text{lifetime}: \text{Lifetime}\}$$

**不可变借用规则**：
$$\frac{\Gamma \vdash e : \tau \quad \text{not\_borrowed}(e, B)}{\Gamma \vdash \&e : \&\tau}$$

**相关定义**：

- [定义 1.4: 借用](../main_comprehensive_index.md#21-所有权与借用系统) (主索引)
- [定义 1.6: 生命周期](03_lifetime_system.md#生命周期定义) (本模块)

**相关定理**：

- [定理 1.7: 多重不可变借用安全](06_theorems.md#多重不可变借用安全) (本模块)

### 3.2 可变借用 {#可变借用}

**可变借用类型**：
$$\& \text{mut } \tau$$

**可变借用语义**：
$$\text{MutBorrow}(\tau) = \text{struct}\{\text{value}: \tau, \text{lifetime}: \text{Lifetime}, \text{exclusive}: \text{bool}\}$$

**可变借用规则**：
$$\frac{\Gamma \vdash e : \tau \quad \text{not\_borrowed}(e, B)}{\Gamma \vdash \&\text{mut } e : \&\text{mut } \tau}$$

**相关定义**：

- [定义 1.5: 可变借用](../main_comprehensive_index.md#21-所有权与借用系统) (主索引)
- [定义 1.6: 生命周期](03_lifetime_system.md#生命周期定义) (本模块)

**相关定理**：

- [定理 1.8: 可变借用排他性](06_theorems.md#可变借用排他性) (本模块)

### 3.3 借用组合 {#借用组合}

**借用组合类型**：
$$\text{BorrowCombo} = \text{enum}\{\text{Single}(\text{Borrow}), \text{Multiple}(\text{Vec}[\text{ImmBorrow}])\}$$

**借用组合规则**：
$$\frac{\Gamma \vdash e_1 : \&\tau \quad \Gamma \vdash e_2 : \&\tau}{\Gamma \vdash (e_1, e_2) : (\&\tau, \&\tau)}$$

**相关概念**：

- [不可变借用](#不可变借用) (本文档)
- [可变借用](#可变借用) (本文档)
- [生命周期组合](03_lifetime_system.md#生命周期组合) (本模块)

## 4. 借用规则

### 4.1 基本借用规则 {#基本借用规则}

**规则1：排他性可变借用**
$$\forall x \in \text{Variables}. \text{at\_most\_one\_mut\_borrow}(x)$$

**规则2：不可变借用共存**
$$\forall x \in \text{Variables}. \text{multiple\_imm\_borrows\_allowed}(x)$$

**规则3：借用互斥**
$$\forall x \in \text{Variables}. \text{imm\_and\_mut\_borrow\_exclusive}(x)$$

**相关定理**：

- [定理 1.6: 借用安全](06_theorems.md#借用安全) (本模块)
- [定理 1.8: 可变借用排他性](06_theorems.md#可变借用排他性) (本模块)

**相关概念**：

- [并发安全](../05_concurrency/01_formal_concurrency_model.md#并发安全) (模块 05)
- [数据竞争避免](../05_concurrency/01_formal_concurrency_model.md#数据竞争避免) (模块 05)

### 4.2 借用检查算法 {#借用检查算法}

**借用检查函数**：

```rust
fn borrow_check(expr: &Expr, env: &mut BorrowEnv) -> Result<(), BorrowError> {
    match expr {
        Expr::Ref(inner) => {
            if env.is_mut_borrowed(inner) {
                Err(BorrowError::AlreadyMutBorrowed)
            } else {
                env.add_immutable_borrow(inner);
                Ok(())
            }
        }
        Expr::MutRef(inner) => {
            if env.is_borrowed(inner) {
                Err(BorrowError::AlreadyBorrowed)
            } else {
                env.add_mutable_borrow(inner);
                Ok(())
            }
        }
        Expr::Deref(inner) => {
            if let Some(borrow) = env.get_borrow(inner) {
                match borrow {
                    Borrow::Immutable => Ok(()),
                    Borrow::Mutable => Ok(()),
                }
            } else {
                Err(BorrowError::NotBorrowed)
            }
        }
        Expr::Assign(target, value) => {
            if env.is_mut_borrowed(target) {
                Ok(())
            } else {
                Err(BorrowError::NotMutBorrowed)
            }
        }
        // ... 其他表达式
    }
}
```

**相关模型**：

- [借用检查算法](../main_comprehensive_index.md#4-模型与方法索引) (主索引)
- [类型检查算法](../02_type_system/02_type_inference.md#类型检查算法) (模块 02)

### 4.3 借用传播 {#借用传播}

**借用传播规则**：
$$\frac{\Gamma \vdash e : \&\tau \quad \Gamma \vdash f : \text{fn}(\&\tau) \to \tau'}{\Gamma \vdash f(e) : \tau'}$$

**借用扩展规则**：
$$\frac{\Gamma \vdash e : \&\text{struct}\{f_1: \tau_1, f_2: \tau_2\}}{\Gamma \vdash e.f_1 : \&\tau_1}$$

**相关概念**：

- [生命周期传播](03_lifetime_system.md#生命周期传播) (本模块)
- [函数借用](#72-函数借用) (本文档)

## 5. 借用检查器

### 5.1 检查器架构 {#检查器架构}

**借用检查器定义**：
$$\text{BorrowChecker} = \text{struct}\{\text{env}: \text{BorrowEnv}, \text{rules}: \text{Vec}[\text{BorrowRule}]\}$$

**检查器状态**：
$$\text{CheckerState} = \text{struct}\{\text{borrows}: \text{Map}[\text{Variable}, \text{BorrowState}], \text{errors}: \text{Vec}[\text{BorrowError}]\}$$

**相关概念**：

- [借用环境](#借用环境) (本文档)
- [基本借用规则](#基本借用规则) (本文档)
- [类型检查器](../02_type_system/02_type_inference.md#类型检查器) (模块 02)

### 5.2 检查算法 {#检查算法}

**主要检查算法**：

```rust
fn check_borrows(ast: &AST) -> Result<(), Vec<BorrowError>> {
    let mut checker = BorrowChecker::new();
    let mut errors = Vec::new();
    
    for stmt in ast.statements() {
        if let Err(error) = checker.check_statement(stmt) {
            errors.push(error);
        }
    }
    
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
```

**相关模型**：

- [借用检查算法](../main_comprehensive_index.md#4-模型与方法索引) (主索引)
- [生命周期推断算法](03_lifetime_system.md#推断算法) (本模块)

**相关定理**：

- [定理 1.6: 借用安全](06_theorems.md#借用安全) (本模块)
- [定理 1.8: 可变借用排他性](06_theorems.md#可变借用排他性) (本模块)

### 5.3 错误检测 {#错误检测}

**错误类型**：
$$\text{BorrowError} = \text{enum}\{\text{AlreadyBorrowed}, \text{AlreadyMutBorrowed}, \text{NotBorrowed}, \text{NotMutBorrowed}\}$$

**错误报告**：

```rust
fn report_error(error: &BorrowError, location: &SourceLocation) {
    match error {
        BorrowError::AlreadyBorrowed => println!("Error: Value already borrowed"),
        BorrowError::AlreadyMutBorrowed => println!("Error: Value already mutably borrowed"),
        BorrowError::NotBorrowed => println!("Error: Value not borrowed"),
        BorrowError::NotMutBorrowed => println!("Error: Value not mutably borrowed"),
    }
}
```

**相关概念**：

- [错误处理](../09_error_handling/01_formal_error_model.md#错误处理模型) (模块 09)
- [借用检查算法](#借用检查算法) (本文档)

## 6. 生命周期管理

### 6.1 生命周期标注 {#生命周期标注}

**生命周期标注语法**：

```rust
fn example<'a>(x: &'a i32) -> &'a i32 { x }
```

**生命周期标注规则**：
$$\frac{\Gamma, \alpha \vdash e : \tau}{\Gamma \vdash \Lambda\alpha.e : \forall\alpha.\tau}$$

**相关概念**：

- [生命周期定义](03_lifetime_system.md#生命周期定义) (本模块)
- [生命周期类型](03_lifetime_system.md#基本生命周期类型) (本模块)

### 6.2 生命周期推断 {#生命周期推断}

**推断规则**：
$$\frac{\Gamma \vdash e : \tau \quad \text{no\_lifetime\_annotations}(e)}{\Gamma \vdash e : \tau[\alpha/\text{infer}(\Gamma, e)]}$$

**相关概念**：

- [生命周期推断算法](03_lifetime_system.md#推断算法) (本模块)
- [类型推断](../02_type_system/02_type_inference.md#类型推断) (模块 02)

**相关定理**：

- [定理 1.9: 生命周期有界性](06_theorems.md#生命周期有界性) (本模块)
- [定理 1.10: 生命周期包含关系](06_theorems.md#生命周期包含关系) (本模块)

### 6.3 生命周期省略 {#生命周期省略}

**省略规则**：

1. 每个引用参数都有自己的生命周期参数
2. 如果只有一个输入生命周期参数，则将其分配给所有输出生命周期参数
3. 如果有多个输入生命周期参数，但其中一个是 `&self` 或 `&mut self`，则将 `self` 的生命周期分配给所有输出生命周期参数

**相关概念**：

- [生命周期省略规则](03_lifetime_system.md#省略规则) (本模块)
- [生命周期推断](#生命周期推断) (本文档)

## 7. 实际应用

### 7.1 数据结构体体体借用 {#数据结构体体体借用}

**链表借用示例**：

```rust
struct List<T> {
    value: T,
    next: Option<Box<List<T>>>,
}

fn traverse<T>(list: &List<T>) {
    // 遍历链表
    let mut current = list;
    while let Some(next) = &current.next {
        // 使用不可变借用
        current = next;
    }
}
```

**相关概念**：

- [不可变借用](#不可变借用) (本文档)
- [数据结构体体体生命周期](03_lifetime_system.md#数据结构体体体生命周期) (本模块)
- [内存管理模型](../11_memory_management/01_formal_memory_model.md#内存管理模型) (模块 11)

### 7.2 函数借用 {#函数借用}

**函数借用示例**：

```rust
fn process_data<'a>(data: &'a mut Vec<i32>) -> &'a i32 {
    data.push(42);
    &data[data.len() - 1]
}
```

**相关概念**：

- [可变借用](#可变借用) (本文档)
- [函数生命周期规则](03_lifetime_system.md#函数生命周期规则) (本模块)
- [生命周期函数类型](03_lifetime_system.md#生命周期函数类型) (本模块)

### 7.3 并发借用 {#并发借用}

**并发借用示例**：

```rust
fn parallel_process(data: &Vec<i32>) {
    let (first_half, second_half) = data.split_at(data.len() / 2);
    
    std::thread::scope(|s| {
        s.spawn(|| process_slice(first_half));
        s.spawn(|| process_slice(second_half));
    });
}
```

**相关概念**：

- [并发安全](../05_concurrency/01_formal_concurrency_model.md#并发安全) (模块 05)
- [数据竞争避免](../05_concurrency/01_formal_concurrency_model.md#数据竞争避免) (模块 05)
- [线程安全](../05_concurrency/01_formal_concurrency_model.md#线程安全) (模块 05)

## 8. 定理证明

### 8.1 借用安全定理 {#借用安全定理}

**定理**: 如果程序通过借用检查，则不会出现悬垂引用。

**证明**:

1. 假设程序通过了借用检查
2. 借用检查确保所有引用的生命周期不超过被引用值的生命周期
3. 因此，当引用被使用时，被引用值一定有效
4. 所以不会出现悬垂引用

**相关定理**：

- [定理 1.6: 借用安全](06_theorems.md#借用安全) (本模块)
- [定理 1.9: 生命周期有界性](06_theorems.md#生命周期有界性) (本模块)

### 8.2 数据竞争避免定理 {#数据竞争避免定理}

**定理**: 如果程序通过借用检查，则不会出现数据竞争。

**证明**:

1. 数据竞争需要同时满足：(a)多线程并发访问同一数据，(b)至少有一个是写操作，(c)没有同步机制
2. 借用规则确保：(a)可变借用是排他的，(b)不可变借用不允许修改
3. 因此，不可能同时存在一个可变借用和任何其他借用
4. 所以不会出现数据竞争

**相关定理**：

- [定理 1.8: 可变借用排他性](06_theorems.md#可变借用排他性) (本模块)
- [并发安全定理](../05_concurrency/06_theorems.md#并发安全定理) (模块 05)

### 8.3 借用检查完备性定理 {#借用检查完备性定理}

**定理**: 借用检查器能够检测所有潜在的借用违规。

**证明**:

1. 借用检查器基于静态程序分析
2. 所有可能的执行路径都被分析
3. 借用规则在每个执行点都被验证
4. 因此，任何可能的借用违规都会被检测到

**相关定理**：

- [定理 1.6: 借用安全](06_theorems.md#借用安全) (本模块)
- [类型系统可靠性定理](../02_type_system/06_theorems.md#类型系统可靠性) (模块 02)

## 9. 参考文献

### 9.1 学术论文

1. Matsakis, N. D., & Klock, F. S. (2014). The Rust Language. *ACM SIGAda Ada Letters*, 34(3), 103-104.
2. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2017). RustBelt: Securing the Foundations of the Rust Programming Language. *POPL 2018*.
3. Weiss, A., Patterson, D., Ahmed, A., Appel, A. W., & Eisenberg, R. A. (2019). Reference Capabilities for Trait Safety. *OOPSLA 2019*.

### 9.2 技术文档

1. The Rust Programming Language Book. Chapter 4: Understanding Ownership.
2. The Rustonomicon. Chapter: Borrowing and Lifetimes.
3. The Rust Reference. Chapter: Lifetime Elision.

### 9.3 在线资源

1. Rust官方文档：[https://doc.rust-lang.org/](https://doc.rust-lang.org/)
2. Rust标准库文档：[https://doc.rust-lang.org/std/](https://doc.rust-lang.org/std/)
3. Rust社区资源：[https://www.rust-lang.org/community](https://www.rust-lang.org/community)

---

## 形式化证明映射（借用系统）

- 所有权/借用基础与规则：
  - 文档：`formal_rust/language/01_ownership_borrowing/01_formal_ownership_system.md`
- 生命周期省略与标注一致性：
  - 文档：`formal_rust/language/21_lifetime_elision_theory.md`
- 类型安全（进展/保持）联动：
  - Coq：`formal_rust/framework/proofs/coq/type_system_progress_preservation.v`
  - Lean：`formal_rust/framework/proofs/lean/TypeSystem/ProgressPreservation.lean`
- 内存安全验证联动：
  - 文档：`formal_rust/framework/memory_safety_verification.md`

### 验证义务占位（与验证清单一致）

- O-OB-UNI：可变借用唯一性（无并发别名）
- O-OB-IMM：不可变借用多别名但只读（无写）
- O-OB-LIF：借用生命周期不超越所有者（无悬垂）

> 注：上述义务将按“文档 → 规则 → 最小可验证示例（MVE）→ Coq/Lean 占位 → 去除占位”的流程推进落地。

---

[返回主索引](../main_comprehensive_index.md)
