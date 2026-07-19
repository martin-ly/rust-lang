# 范畴论与 Rust 类型系统 (Category Theory)

## 目录

- [范畴论与 Rust 类型系统 (Category Theory)](#范畴论与-rust-类型系统-category-theory)
  - [目录](#目录)
  - [引言](#引言)
    - [为什么程序员需要范畴论？](#为什么程序员需要范畴论)
    - [范畴论与编程的对应关系](#范畴论与编程的对应关系)
  - [范畴论基础](#范畴论基础)
    - [范畴的定义](#范畴的定义)
    - [Rust 类型范畴](#rust-类型范畴)
    - [常见范畴](#常见范畴)
  - [函子 (Functors)](#函子-functors)
    - [定义](#定义)
    - [Rust 中的 Functor Trait](#rust-中的-functor-trait)
    - [常见 Functor 实例](#常见-functor-实例)
      - [1. Option Functor](#1-option-functor)
      - [2. Vec Functor](#2-vec-functor)
      - [3. Result Functor](#3-result-functor)
      - [4. 函数 Functor (Reader)](#4-函数-functor-reader)
    - [协变与逆变函子](#协变与逆变函子)
  - [自然变换 (Natural Transformations)](#自然变换-natural-transformations)
    - [定义1](#定义1)
    - [Rust 中的自然变换](#rust-中的自然变换)
    - [常见自然变换](#常见自然变换)
      - [1. 列表到 Option (safeHead)](#1-列表到-option-safehead)
      - [2. Option 展平 (join)](#2-option-展平-join)
      - [3. Result 到 Option](#3-result-到-option)
  - [单子 (Monads)](#单子-monads)
    - [定义2](#定义2)
    - [Monad Trait 定义](#monad-trait-定义)
    - [Option Monad](#option-monad)
    - [Result Monad](#result-monad)
    - [Vec Monad (List Monad)](#vec-monad-list-monad)
    - [do-notation 风格 (使用宏)](#do-notation-风格-使用宏)
  - [应用函子 (Applicative Functors)](#应用函子-applicative-functors)
    - [定义3](#定义3)
    - [Option Applicative](#option-applicative)
    - [应用函子定律](#应用函子定律)
  - [伴随函子 (Adjunctions)](#伴随函子-adjunctions)
    - [定义4](#定义4)
    - [Rust 中的伴随示例](#rust-中的伴随示例)
      - [Free-Forgetful 伴随](#free-forgetful-伴随)
      - [Product-Exponential 伴随](#product-exponential-伴随)
  - [积与余积 (Products and Coproducts)](#积与余积-products-and-coproducts)
    - [积 (Product)](#积-product)
      - [Rust 中的积](#rust-中的积)
    - [余积 (Coproduct)](#余积-coproduct)
      - [Rust 中的余积](#rust-中的余积)
  - [指数对象 (Exponential Objects)](#指数对象-exponential-objects)
    - [定义5](#定义5)
    - [Rust 中的指数对象](#rust-中的指数对象)
  - [Yoneda 引理](#yoneda-引理)
    - [陈述](#陈述)
    - [Rust 中的 Yoneda](#rust-中的-yoneda)
    - [Co-Yoneda](#co-yoneda)
  - [范畴论在 Rust 中的应用](#范畴论在-rust-中的应用)
    - [1. 错误处理组合](#1-错误处理组合)
    - [2. Iterator 作为 Monad](#2-iterator-作为-monad)
    - [3. Future/Async 作为 Monad](#3-futureasync-作为-monad)
    - [4. 设计模式: Builder as Free Monad](#4-设计模式-builder-as-free-monad)
    - [5. Lens: 函子组合](#5-lens-函子组合)
  - [参考文献](#参考文献)
    - [经典文献](#经典文献)
    - [Haskell 与范畴论](#haskell-与范畴论)
    - [Rust 与范畴论](#rust-与范畴论)
    - [在线资源](#在线资源)
  - [总结](#总结)

---

## 引言

**范畴论** (Category Theory) 是研究数学结构之间关系的抽象理论，被称为"数学的数学"。
在编程语言理论中，范畴论为类型系统、抽象和组合提供了强大的理论框架。

### 为什么程序员需要范畴论？

1. **抽象模式**: 识别和复用通用编程模式
2. **组合性**: 理解如何组合小的组件构建大的系统
3. **类型类设计**: 指导 trait 设计（如 Functor, Monad）
4. **函数式编程**: 理解 FP 核心概念的数学基础
5. **并行和并发**: 范畴论提供并发语义的数学模型

### 范畴论与编程的对应关系

| 范畴论概念 | 编程概念 | Rust 示例 |
|-----------|---------|----------|
| 范畴 | 类型系统 | Rust 类型 |
| 对象 | 类型 | `i32`, `String` |
| 态射 | 函数 | `fn(A) -> B` |
| 函子 | 类型构造器 | `Option<T>`, `Vec<T>` |
| 自然变换 | 多态函数 | `fn<T>(Option<T>) -> Vec<T>` |
| 单子 | 计算上下文 | `Result<T, E>` |

---

## 范畴论基础

### 范畴的定义

一个**范畴** C 包含:

1. **对象集合** Ob(C)
2. **态射集合** Hom(C), 对于每对对象 A, B, 存在态射集 Hom(A, B)
3. **组合运算** ∘: 若 f: A → B, g: B → C, 则 g ∘ f: A → C
4. **单位态射** id: 对每个对象 A, 存在 idₐ: A → A

**范畴公理**:

```text
1. 结合律: h ∘ (g ∘ f) = (h ∘ g) ∘ f
2. 单位律: f ∘ idₐ = f = idᵦ ∘ f
```

### Rust 类型范畴

**范畴 Rust**:

- **对象**: Rust 类型 (`i32`, `String`, `Vec<T>`, ...)
- **态射**: Rust 函数 (`fn(A) -> B`)
- **组合**: 函数组合
- **单位**: 恒等函数

```rust
// 对象: 类型
type A = i32;
type B = String;
type C = bool;

// 态射: 函数
fn f(a: A) -> B {
    a.to_string()
}

fn g(b: B) -> C {
    b.is_empty()
}

// 组合: g ∘ f
fn compose<A, B, C>(
    f: impl Fn(A) -> B,
    g: impl Fn(B) -> C,
) -> impl Fn(A) -> C {
    move |a| g(f(a))
}

// 单位态射
fn identity<T>(x: T) -> T {
    x
}

fn example() {
    let h = compose(f, g); // h: i32 -> bool
    assert_eq!(h(42), false); // "42".is_empty() = false
    
    // 验证单位律: f ∘ id = f
    let f_id = compose(identity::<i32>, f);
    assert_eq!(f(10), f_id(10));
}
```

### 常见范畴

| 范畴 | 对象 | 态射 |
|------|------|------|
| **Set** | 集合 | 函数 |
| **Type** | 类型 | 函数 |
| **Poset** | 偏序集元素 | a ≤ b 关系 |
| **Mon** | 幺半群 | 幺半群同态 |
| **Grp** | 群 | 群同态 |
| **Vec** | 向量空间 | 线性变换 |

---

## 函子 (Functors)

### 定义

**函子** F: C → D 是范畴之间的映射:

1. **对象映射**: F(A) ∈ Ob(D) 对所有 A ∈ Ob(C)
2. **态射映射**: F(f: A → B) = F(f): F(A) → F(B)

**函子定律**:

```text
1. 保持单位: F(idₐ) = id_{F(A)}
2. 保持组合: F(g ∘ f) = F(g) ∘ F(f)
```

### Rust 中的 Functor Trait

```rust
// Functor trait (需要高阶类型支持，Rust 通过关联类型模拟)
trait Functor {
    type Wrapped<T>;
    
    fn fmap<A, B>(
        fa: Self::Wrapped<A>,
        f: impl Fn(A) -> B
    ) -> Self::Wrapped<B>;
}

// Option 作为 Functor
struct OptionFunctor;

impl Functor for OptionFunctor {
    type Wrapped<T> = Option<T>;
    
    fn fmap<A, B>(
        fa: Option<A>,
        f: impl Fn(A) -> B
    ) -> Option<B> {
        fa.map(f)
    }
}

// 验证函子定律
fn verify_functor_laws() {
    let x = Some(42);
    
    // 定律 1: fmap id = id
    let id = |x: i32| x;
    assert_eq!(
        OptionFunctor::fmap(x, id),
        x
    );
    
    // 定律 2: fmap (g ∘ f) = fmap g ∘ fmap f
    let f = |x: i32| x + 1;
    let g = |x: i32| x * 2;
    
    let lhs = OptionFunctor::fmap(x, |a| g(f(a)));
    let rhs = OptionFunctor::fmap(
        OptionFunctor::fmap(x, f),
        g
    );
    
    assert_eq!(lhs, rhs);
}
```

### 常见 Functor 实例

#### 1. Option Functor

```rust
impl<T> Option<T> {
    // fmap: (A → B) → Option<A> → Option<B>
    fn fmap<B, F: FnOnce(T) -> B>(self, f: F) -> Option<B> {
        self.map(f)
    }
}

fn example_option_functor() {
    let x: Option<i32> = Some(5);
    let y: Option<String> = x.fmap(|n| n.to_string());
    assert_eq!(y, Some("5".to_string()));
}
```

#### 2. Vec Functor

```rust
impl<T> Vec<T> {
    // fmap: (A → B) → Vec<A> → Vec<B>
    fn fmap<B, F: FnMut(T) -> B>(self, f: F) -> Vec<B> {
        self.into_iter().map(f).collect()
    }
}

fn example_vec_functor() {
    let xs = vec![1, 2, 3];
    let ys = xs.fmap(|x| x * 2);
    assert_eq!(ys, vec![2, 4, 6]);
}
```

#### 3. Result Functor

```rust
impl<T, E> Result<T, E> {
    // fmap: (A → B) → Result<A, E> → Result<B, E>
    fn fmap<B, F: FnOnce(T) -> B>(self, f: F) -> Result<B, E> {
        self.map(f)
    }
}

fn example_result_functor() {
    let x: Result<i32, &str> = Ok(42);
    let y: Result<String, &str> = x.fmap(|n| n.to_string());
    assert_eq!(y, Ok("42".to_string()));
}
```

#### 4. 函数 Functor (Reader)

```rust
// Reader functor: (->) r
struct Reader<R, A> {
    run: Box<dyn Fn(R) -> A>,
}

impl<R: 'static, A: 'static> Reader<R, A> {
    fn fmap<B: 'static, F>(self, f: F) -> Reader<R, B>
    where
        F: Fn(A) -> B + 'static,
    {
        Reader {
            run: Box::new(move |r| f((self.run)(r))),
        }
    }
}

fn example_reader_functor() {
    let reader = Reader {
        run: Box::new(|r: i32| r + 1),
    };
    
    let mapped = reader.fmap(|x| x * 2);
    assert_eq!((mapped.run)(5), 12); // (5 + 1) * 2
}
```

### 协变与逆变函子

```rust
// 协变函子: F<A> → F<B> 当 A → B
// 例如: Option, Vec, Box

// 逆变函子: F<B> → F<A> 当 A → B
// 例如: 函数参数位置

trait ContravariantFunctor {
    type Wrapped<T>;
    
    fn contramap<A, B>(
        fb: Self::Wrapped<B>,
        f: impl Fn(A) -> B
    ) -> Self::Wrapped<A>;
}

// 函数作为逆变函子（参数位置）
struct FunctionContra<B, C>(Box<dyn Fn(B) -> C>);

impl<B: 'static, C: 'static> ContravariantFunctor for FunctionContra<B, C> {
    type Wrapped<T> = Box<dyn Fn(T) -> C>;
    
    fn contramap<A, B2>(
        fb: Box<dyn Fn(B2) -> C>,
        f: impl Fn(A) -> B2 + 'static,
    ) -> Box<dyn Fn(A) -> C> {
        Box::new(move |a| fb(f(a)))
    }
}
```

---

## 自然变换 (Natural Transformations)

### 定义1

给定两个函子 F, G: C → D, **自然变换** η: F ⇒ G 是态射族:

```text
η_A: F(A) → G(A)  对所有对象 A ∈ C
```

**自然性方格**:

```text
F(A) --η_A--> G(A)
 |              |
F(f)          G(f)
 |              |
 v              v
F(B) --η_B--> G(B)
```

**自然性条件**: `G(f) ∘ η_A = η_B ∘ F(f)`

### Rust 中的自然变换

```rust
// 自然变换: Option ⇒ Vec
fn option_to_vec<T>(opt: Option<T>) -> Vec<T> {
    opt.into_iter().collect()
}

// 验证自然性
fn verify_naturality() {
    let f = |x: i32| x + 1;
    let opt = Some(42);
    
    // 路径 1: fmap f 然后 transform
    let path1 = option_to_vec(opt.map(f));
    
    // 路径 2: transform 然后 fmap f
    let path2 = option_to_vec(opt).into_iter().map(f).collect::<Vec<_>>();
    
    assert_eq!(path1, path2); // 自然性成立
}
```

### 常见自然变换

#### 1. 列表到 Option (safeHead)

```rust
fn safe_head<T>(vec: Vec<T>) -> Option<T> {
    vec.into_iter().next()
}

// 自然性: safe_head ∘ fmap f = fmap f ∘ safe_head
```

#### 2. Option 展平 (join)

```rust
fn join_option<T>(opt_opt: Option<Option<T>>) -> Option<T> {
    opt_opt.flatten()
}

// 自然性验证
fn verify_join_naturality() {
    let f = |x: i32| x * 2;
    let nested = Some(Some(21));
    
    // 路径 1: join 然后 map
    let path1 = join_option(nested).map(f);
    
    // 路径 2: double map 然后 join
    let path2 = join_option(nested.map(|inner| inner.map(f)));
    
    assert_eq!(path1, path2);
}
```

#### 3. Result 到 Option

```rust
fn result_to_option<T, E>(res: Result<T, E>) -> Option<T> {
    res.ok()
}

// 自然变换: Result<_, E> ⇒ Option
```

---

## 单子 (Monads)

### 定义2

**单子** 是一个三元组 (M, η, μ):

1. **函子** M: C → C
2. **单位** η: Id ⇒ M (自然变换)
3. **乘法** μ: M ∘ M ⇒ M (自然变换, 也称 join)

**单子定律**:

```text
1. 左单位: μ ∘ η_M = id_M
2. 右单位: μ ∘ M(η) = id_M
3. 结合律: μ ∘ μ_M = μ ∘ M(μ)
```

### Monad Trait 定义

```rust
trait Monad: Functor {
    // return/pure/unit: A → M<A>
    fn pure<T>(value: T) -> Self::Wrapped<T>;
    
    // bind/flatMap: M<A> → (A → M<B>) → M<B>
    fn bind<A, B>(
        ma: Self::Wrapped<A>,
        f: impl Fn(A) -> Self::Wrapped<B>
    ) -> Self::Wrapped<B>;
    
    // join: M<M<A>> → M<A>
    fn join<A>(mma: Self::Wrapped<Self::Wrapped<A>>) -> Self::Wrapped<A>
    where
        Self: Sized;
}
```

### Option Monad

```rust
struct OptionMonad;

impl Functor for OptionMonad {
    type Wrapped<T> = Option<T>;
    
    fn fmap<A, B>(
        fa: Option<A>,
        f: impl Fn(A) -> B
    ) -> Option<B> {
        fa.map(f)
    }
}

impl Monad for OptionMonad {
    fn pure<T>(value: T) -> Option<T> {
        Some(value)
    }
    
    fn bind<A, B>(
        ma: Option<A>,
        f: impl Fn(A) -> Option<B>
    ) -> Option<B> {
        ma.and_then(f)
    }
    
    fn join<A>(mma: Option<Option<A>>) -> Option<A> {
        mma.flatten()
    }
}

// 验证单子定律
fn verify_option_monad_laws() {
    let x = 42;
    let m = Some(x);
    let f = |a: i32| Some(a + 1);
    let g = |b: i32| Some(b * 2);
    
    // 左单位: pure(x) >>= f  ≡  f(x)
    assert_eq!(
        OptionMonad::bind(OptionMonad::pure(x), &f),
        f(x)
    );
    
    // 右单位: m >>= pure  ≡  m
    assert_eq!(
        OptionMonad::bind(m, OptionMonad::pure),
        m
    );
    
    // 结合律: (m >>= f) >>= g  ≡  m >>= (|x| f(x) >>= g)
    let lhs = OptionMonad::bind(
        OptionMonad::bind(m, &f),
        &g
    );
    let rhs = OptionMonad::bind(m, |x| {
        OptionMonad::bind(f(x), &g)
    });
    assert_eq!(lhs, rhs);
}
```

### Result Monad

```rust
struct ResultMonad<E>(std::marker::PhantomData<E>);

impl<E> Functor for ResultMonad<E> {
    type Wrapped<T> = Result<T, E>;
    
    fn fmap<A, B>(
        fa: Result<A, E>,
        f: impl Fn(A) -> B
    ) -> Result<B, E> {
        fa.map(f)
    }
}

impl<E> Monad for ResultMonad<E> {
    fn pure<T>(value: T) -> Result<T, E> {
        Ok(value)
    }
    
    fn bind<A, B>(
        ma: Result<A, E>,
        f: impl Fn(A) -> Result<B, E>
    ) -> Result<B, E> {
        ma.and_then(f)
    }
    
    fn join<A>(mma: Result<Result<A, E>, E>) -> Result<A, E> {
        mma.and_then(|inner| inner)
    }
}

// 错误处理的单子组合
fn example_result_monad() -> Result<i32, String> {
    let parse_int = |s: &str| -> Result<i32, String> {
        s.parse().map_err(|_| format!("Parse error: {}", s))
    };
    
    let validate = |n: i32| -> Result<i32, String> {
        if n > 0 {
            Ok(n)
        } else {
            Err("Number must be positive".to_string())
        }
    };
    
    // 单子组合
    ResultMonad::bind(
        parse_int("42"),
        |n| ResultMonad::bind(
            validate(n),
            |m| Ok(m * 2)
        )
    )
}
```

### Vec Monad (List Monad)

```rust
struct VecMonad;

impl Functor for VecMonad {
    type Wrapped<T> = Vec<T>;
    
    fn fmap<A, B>(
        fa: Vec<A>,
        f: impl Fn(A) -> B
    ) -> Vec<B> {
        fa.into_iter().map(f).collect()
    }
}

impl Monad for VecMonad {
    fn pure<T>(value: T) -> Vec<T> {
        vec![value]
    }
    
    fn bind<A, B>(
        ma: Vec<A>,
        f: impl Fn(A) -> Vec<B>
    ) -> Vec<B> {
        ma.into_iter().flat_map(f).collect()
    }
    
    fn join<A>(mma: Vec<Vec<A>>) -> Vec<A> {
        mma.into_iter().flatten().collect()
    }
}

// 非确定性计算
fn example_vec_monad() {
    let numbers = vec![1, 2, 3];
    
    let result = VecMonad::bind(numbers, |n| {
        VecMonad::bind(vec!['a', 'b'], move |c| {
            vec![(n, c)]
        })
    });
    
    // 结果: [(1,'a'), (1,'b'), (2,'a'), (2,'b'), (3,'a'), (3,'b')]
    assert_eq!(
        result,
        vec![
            (1, 'a'), (1, 'b'),
            (2, 'a'), (2, 'b'),
            (3, 'a'), (3, 'b'),
        ]
    );
}
```

### do-notation 风格 (使用宏)

```rust
macro_rules! mdo {
    ($monad:ident { return $e:expr }) => {
        $monad::pure($e)
    };
    
    ($monad:ident { $p:pat <- $e:expr; $($rest:tt)* }) => {
        $monad::bind($e, |$p| mdo!($monad { $($rest)* }))
    };
}

fn example_do_notation() -> Option<i32> {
    mdo!(OptionMonad {
        x <- Some(3);
        y <- Some(4);
        return x * x + y * y
    })
    // 结果: Some(25)
}
```

---

## 应用函子 (Applicative Functors)

### 定义3

**应用函子** 是一个更强大的抽象，介于 Functor 和 Monad 之间:

```rust
trait Applicative: Functor {
    // pure: A → F<A>
    fn pure<T>(value: T) -> Self::Wrapped<T>;
    
    // ap/apply: F<A → B> → F<A> → F<B>
    fn ap<A, B>(
        ff: Self::Wrapped<Box<dyn Fn(A) -> B>>,
        fa: Self::Wrapped<A>
    ) -> Self::Wrapped<B>;
}
```

### Option Applicative

```rust
impl Applicative for OptionMonad {
    fn pure<T>(value: T) -> Option<T> {
        Some(value)
    }
    
    fn ap<A, B>(
        ff: Option<Box<dyn Fn(A) -> B>>,
        fa: Option<A>
    ) -> Option<B> {
        match (ff, fa) {
            (Some(f), Some(a)) => Some(f(a)),
            _ => None,
        }
    }
}

// 多参数函数提升
fn example_applicative() {
    let add = |x: i32| -> Box<dyn Fn(i32) -> i32> {
        Box::new(move |y| x + y)
    };
    
    let x = Some(3);
    let y = Some(4);
    
    // 使用 Applicative 组合
    let f = x.map(add);
    let result = OptionMonad::ap(f, y);
    
    assert_eq!(result, Some(7));
}
```

### 应用函子定律

```text
1. 同一律: pure id <*> v ≡ v
2. 组合律: pure (∘) <*> u <*> v <*> w ≡ u <*> (v <*> w)
3. 同态: pure f <*> pure x ≡ pure (f x)
4. 交换: u <*> pure y ≡ pure ($ y) <*> u
```

---

## 伴随函子 (Adjunctions)

### 定义4

函子 F: C → D 和 G: D → C 构成**伴随** F ⊣ G，如果存在自然同构:

```text
Hom_D(F(A), B) ≅ Hom_C(A, G(B))
```

F 称为**左伴随**, G 称为**右伴随**。

### Rust 中的伴随示例

#### Free-Forgetful 伴随

```rust
// Forgetful functor: Monoid → Type
// (忘记幺半群结构，只保留底层类型)

trait Monoid {
    fn empty() -> Self;
    fn append(self, other: Self) -> Self;
}

// Free functor: Type → Monoid
// (从类型构造自由幺半群 = 列表)
struct FreeMonoid<T>(Vec<T>);

impl<T> Monoid for FreeMonoid<T> {
    fn empty() -> Self {
        FreeMonoid(vec![])
    }
    
    fn append(mut self, mut other: Self) -> Self {
        self.0.append(&mut other.0);
        self
    }
}

// 伴随关系: Free ⊣ Forgetful
// Hom_Monoid(Free(A), M) ≅ Hom_Type(A, Forget(M))
```

#### Product-Exponential 伴随

```rust
// (- × B) ⊣ (- → B)
// Hom(A × B, C) ≅ Hom(A, B → C)

// Curry
fn curry<A, B, C>(f: impl Fn((A, B)) -> C) -> impl Fn(A) -> Box<dyn Fn(B) -> C> {
    move |a| Box::new(move |b| f((a, b)))
}

// Uncurry
fn uncurry<A, B, C>(f: impl Fn(A) -> Box<dyn Fn(B) -> C>) -> impl Fn((A, B)) -> C {
    move |(a, b)| f(a)(b)
}
```

---

## 积与余积 (Products and Coproducts)

### 积 (Product)

**积** A × B 是带有投影的对象:

```text
π₁: A × B → A
π₂: A × B → B
```

**泛性质**: 对任何 C 和态射 f: C → A, g: C → B, 存在唯一 h: C → A × B 使得:

```text
π₁ ∘ h = f
π₂ ∘ h = g
```

#### Rust 中的积

```rust
// 元组作为积
fn product_example() {
    let pair: (i32, String) = (42, "hello".to_string());
    
    // 投影
    let fst = pair.0; // π₁
    let snd = pair.1; // π₂
    
    // 泛性质: 配对函数
    fn pair<A, B, C>(f: impl Fn(C) -> A, g: impl Fn(C) -> B) -> impl Fn(C) -> (A, B) {
        move |c| (f(c), g(c))
    }
}
```

### 余积 (Coproduct)

**余积** A + B 是带有注入的对象:

```text
ι₁: A → A + B
ι₂: B → A + B
```

**泛性质**: 对任何 C 和态射 f: A → C, g: B → C, 存在唯一 h: A + B → C 使得:

```text
h ∘ ι₁ = f
h ∘ ι₂ = g
```

#### Rust 中的余积

```rust
// 枚举作为余积
enum Either<A, B> {
    Left(A),
    Right(B),
}

fn coproduct_example() {
    // 注入
    let left: Either<i32, String> = Either::Left(42);
    let right: Either<i32, String> = Either::Right("hello".to_string());
    
    // 泛性质: case 分析
    fn either<A, B, C>(
        e: Either<A, B>,
        f: impl FnOnce(A) -> C,
        g: impl FnOnce(B) -> C,
    ) -> C {
        match e {
            Either::Left(a) => f(a),
            Either::Right(b) => g(b),
        }
    }
}
```

---

## 指数对象 (Exponential Objects)

### 定义5

在笛卡尔闭范畴中，**指数对象** B^A 表示从 A 到 B 的所有态射:

```text
eval: B^A × A → B
```

**泛性质**: 对任何 f: C × A → B, 存在唯一 λf: C → B^A 使得:

```text
eval ∘ (λf × id_A) = f
```

### Rust 中的指数对象

```rust
// 函数类型作为指数对象
type Exp<A, B> = Box<dyn Fn(A) -> B>;

// eval: (B^A × A) → B
fn eval<A, B>(pair: (Exp<A, B>, A)) -> B {
    (pair.0)(pair.1)
}

// curry/uncurry 体现伴随关系
fn curry_example() {
    // f: (C × A) → B
    let f = |(x, y): (i32, i32)| x + y;
    
    // λf: C → B^A
    let curried = |x: i32| -> Box<dyn Fn(i32) -> i32> {
        Box::new(move |y| x + y)
    };
    
    // 验证: eval ∘ (λf × id) = f
    let x = 3;
    let y = 4;
    assert_eq!(eval((curried(x), y)), f((x, y)));
}
```

---

## Yoneda 引理

### 陈述

对任何函子 F: C → Set 和对象 A ∈ C:

```text
Nat(Hom_C(A, -), F) ≅ F(A)
```

自然变换从 Hom 函子到 F 等价于 F(A) 的元素。

### Rust 中的 Yoneda

```rust
// Yoneda 嵌入
struct Yoneda<F, A>
where
    F: Functor,
{
    run: Box<dyn for<'a> Fn(Box<dyn Fn(A) -> A>) -> F::Wrapped<A>>,
}

// Yoneda 引理: 同构
fn to_yoneda<F, A>(fa: F::Wrapped<A>) -> Yoneda<F, A>
where
    F: Functor,
    A: Clone + 'static,
{
    Yoneda {
        run: Box::new(move |f| F::fmap(fa.clone(), move |a| f(a))),
    }
}

fn from_yoneda<F, A>(yoneda: Yoneda<F, A>) -> F::Wrapped<A>
where
    F: Functor,
{
    (yoneda.run)(Box::new(|a| a))
}
```

### Co-Yoneda

```rust
// Co-Yoneda 引理
struct CoYoneda<F, A>
where
    F: Functor,
{
    fb: Box<dyn std::any::Any>,
    f: Box<dyn Fn(Box<dyn std::any::Any>) -> A>,
}

// Co-Yoneda 提供免费的 Functor 实例
impl<F> Functor for CoYoneda<F, ()>
where
    F: Functor,
{
    type Wrapped<T> = CoYoneda<F, T>;
    
    fn fmap<A, B>(
        fa: CoYoneda<F, A>,
        g: impl Fn(A) -> B + 'static
    ) -> CoYoneda<F, B> {
        CoYoneda {
            fb: fa.fb,
            f: Box::new(move |b| g((fa.f)(b))),
        }
    }
}
```

---

## 范畴论在 Rust 中的应用

### 1. 错误处理组合

```rust
use std::fs::File;
use std::io::{self, Read};

// Result Monad 组合错误处理
fn read_file(path: &str) -> io::Result<String> {
    File::open(path).and_then(|mut file| {
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(contents)
    })
}

// 使用 ? 语法糖 (单子绑定)
fn process_file(path: &str) -> io::Result<usize> {
    let contents = read_file(path)?; // >>= 的语法糖
    let lines = contents.lines().count();
    Ok(lines)
}
```

### 2. Iterator 作为 Monad

```rust
fn iterator_monad_example() {
    let result: Vec<_> = vec![1, 2, 3]
        .into_iter()
        .flat_map(|x| vec![x, x * 10]) // bind
        .map(|x| x + 1)                // fmap
        .collect();
    
    assert_eq!(result, vec![2, 11, 3, 21, 4, 31]);
}
```

### 3. Future/Async 作为 Monad

```rust
use std::future::Future;

// Future 是一个 Monad
async fn async_monad_example() -> Result<i32, String> {
    // async/await 是 do-notation
    let x = fetch_data().await?;    // bind
    let y = process_data(x).await?; // bind
    Ok(y + 1)                       // return
}

async fn fetch_data() -> Result<i32, String> {
    Ok(42)
}

async fn process_data(x: i32) -> Result<i32, String> {
    Ok(x * 2)
}
```

### 4. 设计模式: Builder as Free Monad

```rust
// Builder 模式体现自由单子
struct Config {
    host: String,
    port: u16,
    timeout: u64,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    timeout: Option<u64>,
}

impl ConfigBuilder {
    fn new() -> Self {
        ConfigBuilder {
            host: None,
            port: None,
            timeout: None,
        }
    }
    
    // 单子操作
    fn host(mut self, host: String) -> Self {
        self.host = Some(host);
        self
    }
    
    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    fn timeout(mut self, timeout: u64) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    // 单子解释器
    fn build(self) -> Result<Config, String> {
        Ok(Config {
            host: self.host.ok_or("host is required")?,
            port: self.port.unwrap_or(8080),
            timeout: self.timeout.unwrap_or(30),
        })
    }
}

fn builder_example() {
    let config = ConfigBuilder::new()
        .host("localhost".to_string())
        .port(3000)
        .timeout(60)
        .build()
        .unwrap();
}
```

### 5. Lens: 函子组合

```rust
// Lens 作为范畴论构造
struct Lens<S, A> {
    get: Box<dyn Fn(&S) -> A>,
    set: Box<dyn Fn(&S, A) -> S>,
}

impl<S, A> Lens<S, A> {
    // Lens 组合
    fn compose<B>(self, other: Lens<A, B>) -> Lens<S, B> {
        Lens {
            get: Box::new(move |s| (other.get)(&(self.get)(s))),
            set: Box::new(move |s, b| {
                let a = (self.get)(s);
                let new_a = (other.set)(&a, b);
                (self.set)(s, new_a)
            }),
        }
    }
}
```

---

## 参考文献

### 经典文献

1. **Mac Lane, S.** (1971). "Categories for the Working Mathematician"
2. **Awodey, S.** (2010). "Category Theory" (2nd Edition)
3. **Barr, M., & Wells, C.** (1990). "Category Theory for Computing Science"
4. **Bird, R., & de Moor, O.** (1997). "Algebra of Programming"

### Haskell 与范畴论

1. **Lipovača, M.** (2011). "Learn You a Haskell for Great Good!"
2. **Milewski, B.** (2018). "Category Theory for Programmers"
3. **Yorgey, B.** (2009). "The Typeclassopedia"

### Rust 与范畴论

1. **Krol, M.** (2021). "Functional Programming in Rust"
2. Rust Patterns: Functional Programming in Rust (Online)

### 在线资源

- [nLab: Category Theory](https://ncatlab.org/nlab/show/category+theory)
- [Category Theory for Programmers (Blog)](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
- [Rust Functor/Monad Crates](https://docs.rs)

---

## 总结

范畴论为 Rust 编程提供了强大的抽象工具:

1. **Functor**: 可映射的容器 (`Option`, `Vec`, `Result`)
2. **Monad**: 可组合的计算上下文 (错误处理, 异步)
3. **自然变换**: 多态函数 (`Option` → `Vec`)
4. **伴随**: Curry/Uncurry, Free/Forgetful
5. **积/余积**: 元组/枚举的理论基础

**实践价值**:

- 更好的抽象设计
- 可组合的 API
- 类型安全的重构
- 函数式编程模式

**下一步**: 探索 [线性类型论](./33_linear_type_theory.md) 了解 Rust 所有权系统的理论基础。

---

*文档版本: 1.0*  
*最后更新: 2025-10-19*  
*Rust 版本: 1.90+*
