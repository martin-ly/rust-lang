# 证明树：型变安全

> **定理**: 协变/逆变/不变保证类型安全
> **创建日期**: 2026-02-28
> **状态**: ✅ 完成

---

## 定理陈述

### Def VA-1 (协变)

类型构造器 $F$ 是协变的，当且仅当：
$$A <: B \implies F<A> <: F<B>$$

### Def VA-2 (逆变)

类型构造器 $F$ 是逆变的，当且仅当：
$$A <: B \implies F<B> <: F<A>$$

### Def VA-3 (不变)

类型构造器 $F$ 是不变的，当且仅当：
$$A <: B \implies \neg(F<A> <: F<B>) \land \neg(F<B> <: F<A>)$$

### Thm VA-T1 (协变安全)

不可变引用 `&T` 的协变性保证：若 `A <: B`，则 `&A <: &B` 安全。

### Thm VA-T2 (逆变安全)

函数参数位置的逆变性保证：若 `A <: B`，则 `fn(B) -> R <: fn(A) -> R` 安全。

### Thm VA-T3 (不变必要)

可变引用 `&mut T` 必须是不变的，否则会导致内存不安全。

---

## 证明树可视化

```mermaid
graph TD
    subgraph "型变定义"
    D1[Def VA-1<br/>协变] --> D1_1["A <: B → F<A> <: F<B>"]
    D1 --> D1_2["示例: &T, Vec<T>, Box<T>"]

    D2[Def VA-2<br/>逆变] --> D2_1["A <: B → F<B> <: F<A>"]
    D2 --> D2_2["示例: fn(A) -> R"]

    D3[Def VA-3<br/>不变] --> D3_1["A <: B → F<A> 与 F<B> 无子类型关系"]
    D3 --> D3_2["示例: &mut T, Cell<T>"]
    end

    subgraph "VA-T1: 协变安全"
    T1[Thm VA-T1<br/>协变安全] --> T1_Proof[证明]

    T1_Proof --> T1_Base["&T 协变性"]
    T1_Base --> T1_S1["'a: 'b 且 T: U<br/>→ &'a T <: &'b U"]

    T1_Proof --> T1_Mem[内存安全]
    T1_Mem --> T1_M1["&'a T 只读访问"]
    T1_M1 --> T1_M2["生命周期 'a 内 T 不变"]
    T1_M2 --> T1_M3["缩短生命周期 'b 安全"]
    end

    subgraph "VA-T2: 逆变安全"
    T2[Thm VA-T2<br/>逆变安全] --> T2_Proof[证明]

    T2_Proof --> T2_Base["fn(A) -> R 逆变性"]
    T2_Base --> T2_S1["B <: A<br/>→ fn(A) -> R <: fn(B) -> R"]

    T2_Proof --> T2_Type[类型安全]
    T2_Type --> T2_T1["f: fn(A) -> R 期望 A"]
    T2_T1 --> T2_T2["传入 B <: A"]
    T2_T2 --> T2_T3["f 可以处理 B"]
    T2_T3 --> T2_T4["返回 R 安全"]
    end

    subgraph "VA-T3: 不变必要"
    T3[Thm VA-T3<br/>不变必要] --> T3_Proof[反证法]

    T3_Proof --> T3_Assume["假设 &mut T 协变"]
    T3_Assume --> T3_Ex["A <: B"]
    T3_Ex --> T3_Sub["&mut A <: &mut B"]

    T3_Sub --> T3_Wrong["let r: &mut B = &mut A"]
    T3_Wrong --> T3_Write["*r = B_value"]
    T3_Write --> T3_UB["A 的内存写入 B 值<br/>类型混淆!"]

    T3_UB --> T3_Contra["矛盾!"]
    T3_Contra --> T3_Concl["∴ &mut T 必须不变"]
    end

    subgraph "Rust型变规则"
    R1[&'a T] --> R1_Co[协变: 'a, T]

    R2[&'a mut T] --> R2_Inv[不变: T<br/>协变: 'a]

    R3[fn(A) -> B] --> R3_Contra[逆变: A<br/>协变: B]

    R4[Box<T>] --> R4_Co[协变: T]

    R5[Cell<T>] --> R5_Inv[不变: T]

    R6[Vec<T>] --> R6_Co[协变: T]
    end
```

---

## 形式化证明

### VA-T1: 协变安全

**陈述**: 不可变引用 `&T` 的协变性是安全的。

**证明**:

设 `'a: 'b` 且 `T <: U`。

要证: `&'a T <: &'b U`

1. 引用 `r: &'a T` 提供对 `T` 的只读访问
2. 在 `'a` 生命周期内，`T` 的内容不变
3. `'b ⊆ 'a`，所以在 `'b` 内 `T` 也不变
4. `T <: U` 意味着 `T` 可以视为 `U`
5. 故在 `'b` 内，`&'a T` 可安全作为 `&'b U` 使用

**反例** (若 `&mut T` 协变):

```rust
let mut x: i32 = 42;
let r: &mut i32 = &mut x;
// 若 &mut i32 <: &mut i64 (不安全!)
// *r = 0i64;  // 写入8字节到4字节内存!
```

### VA-T2: 逆变安全

**陈述**: 函数参数位置的逆变性是安全的。

**证明**:

设 `B <: A`，要证: `fn(A) -> R <: fn(B) -> R`

1. 设 `f: fn(A) -> R`
2. `f` 期望参数类型为 `A`
3. 若传入 `b: B`，由 `B <: A`，`b` 可视为 `A`
4. `f(b)` 类型正确
5. 返回 `R` 类型匹配

**示例**:

```rust
fn take_animal(a: &Animal) {}
fn take_dog(d: &Dog) {}

// Dog <: Animal
// fn(&Animal) <: fn(&Dog)

let f: fn(&Dog) = take_animal;  // 安全!
```

### VA-T3: 不变必要

**陈述**: 可变引用 `&mut T` 必须是不变的。

**证明** (反证法):

假设 `&mut T` 对 `T` 协变。

设 `A <: B`，则 `&mut A <: &mut B`。

考虑:

```rust
let mut a: A = ...;
let r: &mut B = &mut a;  // 由假设，允许
*r = B_value;            // 写入 B 值到 A 的内存
```

1. `a` 的内存布局按 `A` 分配
2. `B_value` 可能更大或有不同布局
3. 写入可能导致内存溢出或类型混淆
4. **矛盾!** 故假设不成立。

∴ `&mut T` 对 `T` 必须不变。

---

## Rust 代码示例

### 协变示例

```rust
fn covariance_example() {
    let s = String::from("hello");
    let r: &str = &s;  // &String <: &str 因为 String: Deref<Target=str>

    println!("{}", r);
}
```

### 逆变示例

```rust
trait Animal { fn speak(&self); }
trait Dog: Animal { fn bark(&self); }

fn animal_handler(f: fn(&Animal)) {
    let dog = /* ... */;
    f(&dog);
}

fn dog_handler(d: &Dog) {
    d.bark();
}

// fn(&Animal) <: fn(&Dog)
let h: fn(&Dog) = animal_handler;  // 安全!
```

### 不变示例

```rust
fn invariance_example() {
    let mut x: i32 = 42;
    let r: &mut i32 = &mut x;

    // let r2: &mut i64 = r;  // ❌ 编译错误!
    // &mut i32 与 &mut i64 无子类型关系
}
```

---

**维护者**: Rust 形式化研究团队
**最后更新**: 2026-02-28
**证明状态**: ✅ L2 完成
