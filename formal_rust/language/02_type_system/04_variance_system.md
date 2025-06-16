# 型变系统

## 目录

1. [协变（Covariant）](#1-协变covariant)
2. [逆变（Contravariant）](#2-逆变contravariant)
3. [不变（Invariant）](#3-不变invariant)
4. [生命周期型变](#4-生命周期型变)

## 1. 协变（Covariant）

### 1.1 协变的定义

**定义 1.1.1**: 类型构造子 $F$ 在参数 $T$ 上是协变的，如果 $A \leq B$ 蕴含 $F(A) \leq F(B)$。

**定理 1.1.1**: `Vec<T>` 在 $T$ 上是协变的。

```rust
// 协变示例
trait Animal {}
struct Dog;
impl Animal for Dog {}

fn covariant_example() {
    let dog_vec: Vec<Dog> = vec![Dog];
    
    // Vec<T> 是协变的，可以转换为 Vec<Animal>
    let animal_vec: Vec<Box<dyn Animal>> = dog_vec.into_iter()
        .map(|d| Box::new(d) as Box<dyn Animal>)
        .collect();
}
```

### 1.2 协变的类型构造子

```rust
// 协变的类型构造子
fn covariant_types() {
    // 1. Vec<T> - 协变
    let dogs: Vec<Dog> = vec![Dog];
    
    // 2. Box<T> - 协变
    let dog_box: Box<Dog> = Box::new(Dog);
    
    // 3. &T - 协变
    let dog_ref: &Dog = &Dog;
    
    // 4. fn() -> T - 协变（返回值位置）
    fn get_dog() -> Dog { Dog }
    let get_animal: fn() -> Box<dyn Animal> = || Box::new(get_dog()) as Box<dyn Animal>;
}
```

### 1.3 协变的安全性

**定理 1.3.1**: 协变类型构造子保持类型安全。

**证明**:
```rust
// 协变的安全性证明
fn covariant_safety() {
    let dogs: Vec<Dog> = vec![Dog];
    
    // 协变转换是安全的，因为：
    // 1. Dog 实现了 Animal 的所有方法
    // 2. 对 Animal 的操作对 Dog 也有效
    let animals: Vec<Box<dyn Animal>> = dogs.into_iter()
        .map(|d| Box::new(d) as Box<dyn Animal>)
        .collect();
    
    // 使用转换后的类型是安全的
    for animal in animals {
        // 可以调用 Animal 的方法
    }
}
```

## 2. 逆变（Contravariant）

### 2.1 逆变的定义

**定义 2.1.1**: 类型构造子 $F$ 在参数 $T$ 上是逆变的，如果 $A \leq B$ 蕴含 $F(B) \leq F(A)$。

**定理 2.1.1**: 函数参数位置是逆变的。

```rust
// 逆变示例
fn contravariant_example() {
    // 函数参数位置是逆变的
    fn process_animal(_: &dyn Animal) {}
    
    fn use_function(f: fn(&Dog)) {
        let dog = Dog;
        f(&dog);
    }
    
    // 逆变转换：fn(&Animal) -> fn(&Dog)
    use_function(process_animal);
}
```

### 2.2 逆变的类型构造子

```rust
// 逆变的类型构造子
fn contravariant_types() {
    // 1. fn(T) -> U - 在 T 上是逆变的
    fn process_animal(_: &dyn Animal) {}
    let process_dog: fn(&Dog) = process_animal;
    
    // 2. 函数参数位置
    fn callback(f: fn(&str)) {}
    fn process_string(_: &str) {}
    
    // 逆变转换
    callback(process_string);
}
```

### 2.3 逆变的安全性

**定理 2.3.1**: 逆变类型构造子保持类型安全。

**证明**:
```rust
// 逆变的安全性证明
fn contravariant_safety() {
    fn process_animal(_: &dyn Animal) {
        // 可以处理任何 Animal
    }
    
    fn use_dog_processor(f: fn(&Dog)) {
        let dog = Dog;
        f(&dog); // 调用处理器
    }
    
    // 逆变转换是安全的，因为：
    // 1. process_animal 可以处理任何 Animal
    // 2. Dog 是 Animal 的子类型
    // 3. 所以 process_animal 可以处理 Dog
    use_dog_processor(process_animal);
}
```

## 3. 不变（Invariant）

### 3.1 不变的定义

**定义 3.1.1**: 类型构造子 $F$ 在参数 $T$ 上是不变的，如果 $A \leq B$ 不蕴含 $F(A)$ 和 $F(B)$ 之间的子类型关系。

**定理 3.1.1**: `&mut T` 在 $T$ 上是不变的。

```rust
// 不变示例
fn invariant_example() {
    let mut dog = Dog;
    let dog_ref = &mut dog;
    
    // 不能进行类型转换
    // let animal_ref: &mut dyn Animal = dog_ref; // 错误
}
```

### 3.2 不变的类型构造子

```rust
// 不变的类型构造子
fn invariant_types() {
    // 1. &mut T - 不变
    let mut dog = Dog;
    let dog_ref = &mut dog;
    
    // 2. Cell<T> - 不变
    use std::cell::Cell;
    let dog_cell = Cell::new(Dog);
    
    // 3. RefCell<T> - 不变
    use std::cell::RefCell;
    let dog_refcell = RefCell::new(Dog);
    
    // 4. *mut T - 不变
    let dog_ptr = &mut dog as *mut Dog;
}
```

### 3.3 不变的必要性

**定理 3.3.1**: 不变性对于可变类型是必要的。

**证明**:
```rust
// 不变性的必要性证明
fn invariance_necessity() {
    let mut dog = Dog;
    let dog_ref = &mut dog;
    
    // 如果 &mut T 是协变的，会导致类型不安全
    // 假设可以进行以下转换：
    // let animal_ref: &mut dyn Animal = dog_ref;
    
    // 那么可以这样做：
    // animal_ref.some_animal_method(); // 可能调用 Dog 没有的方法
    
    // 如果 &mut T 是逆变的，也会有问题
    // 因为可变引用需要精确的类型匹配
}
```

## 4. 生命周期型变

### 4.1 生命周期协变

**定义 4.1.1**: 生命周期 `'a` 是协变的，如果 `'b: 'a` 蕴含 `&'a T` 是 `&'b T` 的子类型。

**定理 4.1.1**: 生命周期在不可变引用中是协变的。

```rust
// 生命周期协变示例
fn lifetime_covariance() {
    let mut data = String::from("hello");
    
    // 'a: 'b 意味着 'a 至少和 'b 一样长
    {
        let short_life = &data; // 'a
        {
            let long_life: &'static str = "static"; // 'b
            // 协变：&'a str 可以转换为 &'b str
            let _: &str = short_life;
        }
    }
}
```

### 4.2 生命周期逆变

**定义 4.2.1**: 生命周期在函数参数位置是逆变的。

**定理 4.2.1**: 函数参数的生命周期是逆变的。

```rust
// 生命周期逆变示例
fn lifetime_contravariance() {
    fn process_static_str(s: &'static str) {}
    fn process_any_str<'a>(s: &'a str) {}
    
    // 逆变：fn(&'static str) 可以转换为 fn(&'a str)
    let processor: fn(&str) = process_static_str;
    
    // 使用
    let data = String::from("hello");
    processor(&data);
}
```

### 4.3 生命周期不变

**定义 4.3.1**: 可变引用的生命周期是不变的。

**定理 4.3.1**: `&mut T` 的生命周期是不变的。

```rust
// 生命周期不变示例
fn lifetime_invariance() {
    let mut data = String::from("hello");
    
    {
        let short_mut = &mut data; // 'a
        // 不能转换为更长的生命周期
        // let long_mut: &'static mut String = short_mut; // 错误
    }
}
```

### 4.4 生命周期型变规则

```rust
// 生命周期型变规则总结
fn lifetime_variance_rules() {
    // 1. 不可变引用：协变
    fn covariant_ref<'a, 'b: 'a>(r: &'a str) -> &'b str {
        r // 协变转换
    }
    
    // 2. 函数参数：逆变
    fn contravariant_fn<'a, 'b: 'a>(f: fn(&'b str)) -> fn(&'a str) {
        f // 逆变转换
    }
    
    // 3. 可变引用：不变
    fn invariant_mut<'a>(r: &'a mut str) -> &'a mut str {
        r // 不能改变生命周期
    }
}
```

## 综合应用

### 型变检查器

```rust
// 型变检查器实现
struct VarianceChecker;

impl VarianceChecker {
    // 检查协变
    fn check_covariant<T, U>(_f: fn(T) -> U) where T: 'static, U: 'static {
        // 协变检查逻辑
    }
    
    // 检查逆变
    fn check_contravariant<T, U>(_f: fn(U) -> T) where T: 'static, U: 'static {
        // 逆变检查逻辑
    }
    
    // 检查不变
    fn check_invariant<T>(_f: fn(T) -> T) where T: 'static {
        // 不变检查逻辑
    }
}
```

### 型变推导

```rust
// 型变推导示例
fn variance_inference() {
    // 编译器自动推导型变
    
    // 1. Vec<T> - 协变
    let v1: Vec<Dog> = vec![Dog];
    let v2: Vec<Box<dyn Animal>> = v1.into_iter()
        .map(|d| Box::new(d) as Box<dyn Animal>)
        .collect();
    
    // 2. fn(T) -> U - 在 T 上逆变，在 U 上协变
    fn process_dog(_: &Dog) -> i32 { 42 }
    let process_animal: fn(&dyn Animal) -> i32 = |_| 42;
    
    // 3. &mut T - 不变
    let mut dog = Dog;
    let dog_ref = &mut dog;
    // 不能转换为 &mut dyn Animal
}
```

### 型变错误处理

```rust
// 型变错误处理
fn variance_error_handling() {
    // 常见的型变错误
    
    // 1. 协变错误
    fn covariant_error() {
        let mut dogs: Vec<Dog> = vec![Dog];
        // 错误：不能将 Vec<Dog> 直接转换为 Vec<Animal>
        // let animals: Vec<Animal> = dogs;
    }
    
    // 2. 逆变错误
    fn contravariant_error() {
        fn process_dog(_: &Dog) {}
        // 错误：不能将 fn(&Dog) 转换为 fn(&Animal)
        // let process_animal: fn(&dyn Animal) = process_dog;
    }
    
    // 3. 不变错误
    fn invariant_error() {
        let mut dog = Dog;
        let dog_ref = &mut dog;
        // 错误：不能将 &mut Dog 转换为 &mut Animal
        // let animal_ref: &mut dyn Animal = dog_ref;
    }
}
```

---
**最后更新**: 2025-01-27
**版本**: 1.0.0
**状态**: 型变系统理论完成 