# 代数数据类型

## 目录

1. [积类型（Product Types）](#1-积类型product-types)
2. [和类型（Sum Types）](#2-和类型sum-types)
3. [递归类型](#3-递归类型)
4. [类型代数](#4-类型代数)

## 1. 积类型（Product Types）

### 1.1 积类型的定义

**定义 1.1.1**: 对于类型 $A$ 和 $B$，它们的积类型 $A \times B$ 是所有有序对 $(a, b)$ 的集合。

**定理 1.1.1**: 积类型满足笛卡尔积的性质。

```rust
// 积类型的实现
struct Product<A, B> {
    first: A,
    second: B,
}

// 投影函数
impl<A, B> Product<A, B> {
    fn proj1(&self) -> &A { &self.first }
    fn proj2(&self) -> &B { &self.second }
}
```

### 1.2 结构体作为积类型

```rust
// 结构体作为积类型
struct Point {
    x: f64,
    y: f64,
}

// 等价于 f64 × f64
let p = Point { x: 1.0, y: 2.0 };
```

### 1.3 元组作为积类型

```rust
// 元组作为积类型
let tuple: (i32, String) = (42, "hello".to_string());
// 等价于 i32 × String

// 模式匹配解构
let (number, text) = tuple;
```

## 2. 和类型（Sum Types）

### 2.1 和类型的定义

**定义 2.1.1**: 对于类型 $A$ 和 $B$，它们的和类型 $A + B$ 是 $A$ 的值或 $B$ 的值的集合。

```rust
// 和类型的实现
enum Sum<A, B> {
    Left(A),
    Right(B),
}
```

### 2.2 枚举作为和类型

```rust
// 枚举作为和类型
enum Result<T, E> {
    Ok(T),
    Err(E),
}

// 等价于 T + E
fn divide(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Result::Err("Division by zero".to_string())
    } else {
        Result::Ok(a / b)
    }
}
```

### 2.3 模式匹配

```rust
// 模式匹配作为消除器
fn process_result<T, E>(result: Result<T, E>) -> String {
    match result {
        Result::Ok(value) => format!("Success: {:?}", value),
        Result::Err(error) => format!("Error: {:?}", error),
    }
}
```

## 3. 递归类型

### 3.1 递归类型的定义

**定义 3.1.1**: 递归类型是通过自身定义的类型。

```rust
// 递归类型的基本形式
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

// 等价于 T × List<T> + 1
```

### 3.2 列表类型

```rust
// 列表类型的完整实现
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

impl<T> List<T> {
    fn new() -> Self { List::Nil }
    
    fn prepend(self, head: T) -> Self {
        List::Cons(head, Box::new(self))
    }
    
    fn len(&self) -> usize {
        match self {
            List::Cons(_, tail) => 1 + tail.len(),
            List::Nil => 0,
        }
    }
}
```

### 3.3 树类型

```rust
// 二叉树类型
enum BinaryTree<T> {
    Node(T, Box<BinaryTree<T>>, Box<BinaryTree<T>>),
    Leaf,
}

impl<T> BinaryTree<T> {
    fn leaf() -> Self { BinaryTree::Leaf }
    
    fn node(value: T, left: BinaryTree<T>, right: BinaryTree<T>) -> Self {
        BinaryTree::Node(value, Box::new(left), Box::new(right))
    }
    
    fn size(&self) -> usize {
        match self {
            BinaryTree::Node(_, left, right) => 1 + left.size() + right.size(),
            BinaryTree::Leaf => 0,
        }
    }
}
```

## 4. 类型代数

### 4.1 类型运算

```rust
// 类型运算的基本定律

// 1. 积的交换律: A × B ≅ B × A
fn swap_pair<A, B>((a, b): (A, B)) -> (B, A) {
    (b, a)
}

// 2. 和的交换律: A + B ≅ B + A
fn swap_sum<A, B>(sum: Sum<A, B>) -> Sum<B, A> {
    match sum {
        Sum::Left(a) => Sum::Right(a),
        Sum::Right(b) => Sum::Left(b),
    }
}
```

### 4.2 类型等式

```rust
// 重要的类型等式

// 1. Option<T> ≅ T + 1
enum Option<T> {
    Some(T),
    None,
}

// 2. Result<T, E> ≅ T + E
enum Result<T, E> {
    Ok(T),
    Err(E),
}

// 3. List<T> ≅ T × List<T> + 1
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}
```

### 4.3 类型同构

```rust
// 类型同构的示例

// (A, B) 和 (B, A) 同构
struct Pair<A, B> {
    first: A,
    second: B,
}

fn pair_to_tuple<A, B>(pair: Pair<A, B>) -> (A, B) {
    (pair.first, pair.second)
}

fn tuple_to_pair<A, B>((first, second): (A, B)) -> Pair<A, B> {
    Pair { first, second }
}
```

### 4.4 类型优化

```rust
// 类型优化的示例

// 1. 消除嵌套的 Option
fn flatten_option<T>(opt: Option<Option<T>>) -> Option<T> {
    match opt {
        Some(Some(value)) => Some(value),
        Some(None) => None,
        None => None,
    }
}

// 2. 合并相同的错误类型
fn merge_results<T, E>(results: Vec<Result<T, E>>) -> Result<Vec<T>, E> {
    let mut values = Vec::new();
    for result in results {
        match result {
            Ok(value) => values.push(value),
            Err(e) => return Err(e),
        }
    }
    Ok(values)
}
```

## 综合应用

### 实际应用示例

```rust
// 完整的代数数据类型应用
#[derive(Debug, Clone)]
enum Expression {
    Literal(i32),
    Add(Box<Expression>, Box<Expression>),
    Multiply(Box<Expression>, Box<Expression>),
    Variable(String),
}

impl Expression {
    fn eval(&self, vars: &std::collections::HashMap<String, i32>) -> Result<i32, String> {
        match self {
            Expression::Literal(n) => Ok(*n),
            Expression::Add(left, right) => {
                let l = left.eval(vars)?;
                let r = right.eval(vars)?;
                Ok(l + r)
            }
            Expression::Multiply(left, right) => {
                let l = left.eval(vars)?;
                let r = right.eval(vars)?;
                Ok(l * r)
            }
            Expression::Variable(name) => {
                vars.get(name)
                    .copied()
                    .ok_or_else(|| format!("Variable '{}' not found", name))
            }
        }
    }
}
```

---
**最后更新**: 2025-01-27
**版本**: 1.0.0
**状态**: 代数数据类型理论完成 