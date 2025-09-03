/*
Operations traits 是 Rust 中用于定义基本数学运算的特征集合。
这些特征为类型提供了统一的运算接口，支持泛型编程和运算符重载。

## 基本运算特征

### 1. Add trait - 加法运算

```rust
pub trait Add<Rhs = Self> {
    type Output;
    fn add(self, rhs: Rhs) -> Self::Output;
}
```

### 2. Sub trait - 减法运算

```rust
pub trait Sub<Rhs = Self> {
    type Output;
    fn sub(self, rhs: Rhs) -> Self::Output;
}
```

### 3. Mul trait - 乘法运算

```rust
pub trait Mul<Rhs = Self> {
    type Output;
    fn mul(self, rhs: Rhs) -> Self::Output;
}
```

### 4. Div trait - 除法运算

```rust
pub trait Div<Rhs = Self> {
    type Output;
    fn div(self, rhs: Rhs) -> Self::Output;
}
```

### 5. Rem trait - 取余运算

```rust
pub trait Rem<Rhs = Self> {
    type Output;
    fn rem(self, rhs: Rhs) -> Self::Output;
}
```

## 重要特性

1. **泛型支持**: 支持不同类型的右操作数
2. **输出类型**: 每个特征定义自己的输出类型
3. **所有权语义**: 运算可能消耗操作数
4. **自动派生**: 可以为简单类型自动派生

## 实现示例

### 1. 基本数值类型

```rust
// 这些类型已经实现了所有基本运算特征
let a = 5;
let b = 3;

let sum = a + b;      // 使用 Add
let diff = a - b;     // 使用 Sub
let product = a * b;  // 使用 Mul
let quotient = a / b; // 使用 Div
let remainder = a % b; // 使用 Rem
```

### 2. 自定义类型实现运算

```rust
use std::ops::{Add, Sub, Mul, Div, Rem};

#[derive(Debug, Clone, Copy)]
struct Point {
    x: f64,
    y: f64,
}

impl Add for Point {
    type Output = Point;
    
    fn add(self, other: Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl Sub for Point {
    type Output = Point;
    
    fn sub(self, other: Point) -> Point {
        Point {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

impl Mul<f64> for Point {
    type Output = Point;
    
    fn mul(self, scalar: f64) -> Point {
        Point {
            x: self.x * scalar,
            y: self.y * scalar,
        }
    }
}

impl Div<f64> for Point {
    type Output = Point;
    
    fn div(self, scalar: f64) -> Point {
        Point {
            x: self.x / scalar,
            y: self.y / scalar,
        }
    }
}
```

### 3. 泛型运算类型

```rust
use std::ops::{Add, Sub, Mul, Div};

#[derive(Debug, Clone)]
struct Vector<T> {
    components: Vec<T>,
}

impl<T> Vector<T>
where
    T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Clone,
{
    fn new(components: Vec<T>) -> Self {
        Vector { components }
    }
    
    fn add(&self, other: &Vector<T>) -> Vector<T> {
        let components: Vec<T> = self.components
            .iter()
            .zip(other.components.iter())
            .map(|(a, b)| a.clone() + b.clone())
            .collect();
        Vector { components }
    }
    
    fn scale(&self, scalar: T) -> Vector<T> {
        let components: Vec<T> = self.components
            .iter()
            .map(|c| c.clone() * scalar.clone())
            .collect();
        Vector { components }
    }
}
```

## 使用场景

### 1. 数学计算

```rust
use std::ops::{Add, Sub, Mul, Div};

fn calculate<T>(a: T, b: T, operation: char) -> T
where
    T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Copy,
{
    match operation {
        '+' => a + b,
        '-' => a - b,
        '*' => a * b,
        '/' => a / b,
        _ => panic!("Unknown operation"),
    }
}

fn main() {
    let result1 = calculate(10, 5, '+');
    let result2 = calculate(10.5, 2.0, '*');
    
    println!("10 + 5 = {}", result1);
    println!("10.5 * 2.0 = {}", result2);
}
```

### 2. 矩阵运算

```rust
use std::ops::{Add, Mul};

#[derive(Debug, Clone)]
struct Matrix<T> {
    data: Vec<Vec<T>>,
    rows: usize,
    cols: usize,
}

impl<T> Matrix<T>
where
    T: Add<Output = T> + Mul<Output = T> + Clone + Default,
{
    fn new(data: Vec<Vec<T>>) -> Self {
        let rows = data.len();
        let cols = if rows > 0 { data[0].len() } else { 0 };
        Matrix { data, rows, cols }
    }
    
    fn add(&self, other: &Matrix<T>) -> Matrix<T> {
        let mut result = vec![vec![T::default(); self.cols]; self.rows];
        
        for i in 0..self.rows {
            for j in 0..self.cols {
                result[i][j] = self.data[i][j].clone() + other.data[i][j].clone();
            }
        }
        
        Matrix::new(result)
    }
    
    fn multiply(&self, other: &Matrix<T>) -> Matrix<T> {
        let mut result = vec![vec![T::default(); other.cols]; self.rows];
        
        for i in 0..self.rows {
            for j in 0..other.cols {
                for k in 0..self.cols {
                    result[i][j] = result[i][j].clone() + 
                        self.data[i][k].clone() * other.data[k][j].clone();
                }
            }
        }
        
        Matrix::new(result)
    }
}
```

### 3. 物理量计算

```rust
use std::ops::{Add, Sub, Mul, Div};

#[derive(Debug, Clone, Copy)]
struct Length(f64);

#[derive(Debug, Clone, Copy)]
struct Time(f64);

#[derive(Debug, Clone, Copy)]
struct Velocity(f64);

impl Add for Length {
    type Output = Length;
    
    fn add(self, other: Length) -> Length {
        Length(self.0 + other.0)
    }
}

impl Sub for Length {
    type Output = Length;
    
    fn sub(self, other: Length) -> Length {
        Length(self.0 - other.0)
    }
}

impl Div<Time> for Length {
    type Output = Velocity;
    
    fn div(self, time: Time) -> Velocity {
        Velocity(self.0 / time.0)
    }
}

impl Mul<Time> for Velocity {
    type Output = Length;
    
    fn mul(self, time: Time) -> Length {
        Length(self.0 * time.0)
    }
}
```

## 高级用法

### 1. 条件运算实现

```rust
use std::ops::{Add, Sub};

struct ConditionalNumber<T> {
    value: T,
    allow_negative: bool,
}

impl<T> ConditionalNumber<T> {
    fn new(value: T, allow_negative: bool) -> Self {
        ConditionalNumber { value, allow_negative }
    }
}

impl<T> Add for ConditionalNumber<T>
where
    T: Add<Output = T> + Clone,
{
    type Output = ConditionalNumber<T>;
    
    fn add(self, other: ConditionalNumber<T>) -> ConditionalNumber<T> {
        ConditionalNumber {
            value: self.value + other.value,
            allow_negative: self.allow_negative && other.allow_negative,
        }
    }
}

impl<T> Sub for ConditionalNumber<T>
where
    T: Sub<Output = T> + Clone,
{
    type Output = Option<ConditionalNumber<T>>;
    
    fn sub(self, other: ConditionalNumber<T>) -> Option<ConditionalNumber<T>> {
        let result = self.value - other.value;
        
        // 如果不允许负数，检查结果
        if !self.allow_negative && result < T::default() {
            None
        } else {
            Some(ConditionalNumber {
                value: result,
                allow_negative: self.allow_negative,
            })
        }
    }
}
```

### 2. 链式运算

```rust
use std::ops::{Add, Sub, Mul, Div};

#[derive(Debug, Clone)]
struct Calculator<T> {
    value: T,
    history: Vec<String>,
}

impl<T> Calculator<T>
where
    T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Clone + std::fmt::Display,
{
    fn new(value: T) -> Self {
        Calculator {
            value,
            history: Vec::new(),
        }
    }
    
    fn add(mut self, other: T) -> Self {
        let result = self.value.clone() + other.clone();
        self.history.push(format!("{} + {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    fn sub(mut self, other: T) -> Self {
        let result = self.value.clone() - other.clone();
        self.history.push(format!("{} - {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    fn mul(mut self, other: T) -> Self {
        let result = self.value.clone() * other.clone();
        self.history.push(format!("{} * {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    fn div(mut self, other: T) -> Self {
        let result = self.value.clone() / other.clone();
        self.history.push(format!("{} / {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    fn result(self) -> T {
        self.value
    }
    
    fn show_history(&self) {
        println!("Calculation history:");
        for (i, step) in self.history.iter().enumerate() {
            println!("  {}. {}", i + 1, step);
        }
    }
}
```

## 性能考虑

1. **零成本抽象**: 运算特征调用在编译时被内联
2. **所有权语义**: 注意运算是否消耗操作数
3. **泛型特化**: 为特定类型提供优化的实现
4. **内存分配**: 避免不必要的临时对象创建

## 最佳实践

1. **一致性**: 保持运算的数学语义
2. **错误处理**: 处理除零、溢出等边界情况
3. **性能**: 为常用类型提供优化实现
4. **测试**: 编写全面的运算测试用例

## 总结

Operations traits 为 Rust 提供了统一的数学运算接口。
通过实现这些特征，可以创建可组合的、类型安全的数学运算代码。
*/

use std::ops::{Add, Sub, Mul, Div, Rem};

// 基本运算特征演示
#[derive(Debug, Clone, Copy)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Add for Point {
    type Output = Point;
    
    fn add(self, other: Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl Sub for Point {
    type Output = Point;
    
    fn sub(self, other: Point) -> Point {
        Point {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

impl Mul<f64> for Point {
    type Output = Point;
    
    fn mul(self, scalar: f64) -> Point {
        Point {
            x: self.x * scalar,
            y: self.y * scalar,
        }
    }
}

impl Div<f64> for Point {
    type Output = Point;
    
    fn div(self, scalar: f64) -> Point {
        Point {
            x: self.x / scalar,
            y: self.y / scalar,
        }
    }
}

// 泛型向量类型
#[derive(Debug, Clone)]
pub struct Vector<T> {
    pub components: Vec<T>,
}

impl<T> Vector<T>
where
    T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Clone + Default,
{
    pub fn new(components: Vec<T>) -> Self {
        Vector { components }
    }
    
    pub fn add(&self, other: &Vector<T>) -> Vector<T> {
        let components: Vec<T> = self.components
            .iter()
            .zip(other.components.iter())
            .map(|(a, b)| a.clone() + b.clone())
            .collect();
        Vector { components }
    }
    
    pub fn scale(&self, scalar: T) -> Vector<T> {
        let components: Vec<T> = self.components
            .iter()
            .map(|c| c.clone() * scalar.clone())
            .collect();
        Vector { components }
    }
}

// 物理量类型
#[derive(Debug, Clone, Copy)]
pub struct Length(pub f64);

#[derive(Debug, Clone, Copy)]
pub struct Time(pub f64);

#[derive(Debug, Clone, Copy)]
pub struct Velocity(pub f64);

impl Add for Length {
    type Output = Length;
    
    fn add(self, other: Length) -> Length {
        Length(self.0 + other.0)
    }
}

impl Sub for Length {
    type Output = Length;
    
    fn sub(self, other: Length) -> Length {
        Length(self.0 - other.0)
    }
}

impl Div<Time> for Length {
    type Output = Velocity;
    
    fn div(self, time: Time) -> Velocity {
        Velocity(self.0 / time.0)
    }
}

impl Mul<Time> for Velocity {
    type Output = Length;
    
    fn mul(self, time: Time) -> Length {
        Length(self.0 * time.0)
    }
}

// 链式计算器
#[derive(Debug, Clone)]
pub struct Calculator<T> {
    pub value: T,
    pub history: Vec<String>,
}

impl<T> Calculator<T>
where
    T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Clone + std::fmt::Display,
{
    pub fn new(value: T) -> Self {
        Calculator {
            value,
            history: Vec::new(),
        }
    }
    
    pub fn add(mut self, other: T) -> Self {
        let result = self.value.clone() + other.clone();
        self.history.push(format!("{} + {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    pub fn sub(mut self, other: T) -> Self {
        let result = self.value.clone() - other.clone();
        self.history.push(format!("{} - {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    pub fn mul(mut self, other: T) -> Self {
        let result = self.value.clone() * other.clone();
        self.history.push(format!("{} * {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    pub fn div(mut self, other: T) -> Self {
        let result = self.value.clone() / other.clone();
        self.history.push(format!("{} / {} = {}", self.value, other, result));
        self.value = result;
        self
    }
    
    pub fn result(self) -> T {
        self.value
    }
    
    pub fn show_history(&self) {
        println!("Calculation history:");
        for (i, step) in self.history.iter().enumerate() {
            println!("  {}. {}", i + 1, step);
        }
    }
}

// 演示函数
pub fn demonstrate_operations() {
    println!("=== Operations Traits Demonstration ===\n");
    
    // 基本运算
    demonstrate_basic_operations();
    
    // 自定义类型运算
    demonstrate_custom_operations();
    
    // 泛型运算
    demonstrate_generic_operations();
    
    // 物理量计算
    demonstrate_physics_operations();
    
    // 链式计算
    demonstrate_chained_operations();
}

// 基本运算演示
fn demonstrate_basic_operations() {
    println!("--- Basic Operations ---");
    
    let a = 10;
    let b = 3;
    
    println!("a = {}, b = {}", a, b);
    println!("a + b = {}", a + b);
    println!("a - b = {}", a - b);
    println!("a * b = {}", a * b);
    println!("a / b = {}", a / b);
    println!("a % b = {}", a % b);
    println!();
}

// 自定义类型运算演示
fn demonstrate_custom_operations() {
    println!("--- Custom Type Operations ---");
    
    let p1 = Point { x: 1.0, y: 2.0 };
    let p2 = Point { x: 3.0, y: 4.0 };
    
    println!("Point 1: {:?}", p1);
    println!("Point 2: {:?}", p2);
    
    let sum = p1 + p2;
    let diff = p2 - p1;
    let scaled = p1 * 2.0;
    let divided = p2 / 2.0;
    
    println!("p1 + p2 = {:?}", sum);
    println!("p2 - p1 = {:?}", diff);
    println!("p1 * 2 = {:?}", scaled);
    println!("p2 / 2 = {:?}", divided);
    println!();
}

// 泛型运算演示
fn demonstrate_generic_operations() {
    println!("--- Generic Operations ---");
    
    let v1 = Vector::new(vec![1, 2, 3]);
    let v2 = Vector::new(vec![4, 5, 6]);
    
    println!("Vector 1: {:?}", v1);
    println!("Vector 2: {:?}", v2);
    
    let sum = v1.add(&v2);
    let scaled = v1.scale(2);
    
    println!("v1 + v2 = {:?}", sum);
    println!("v1 * 2 = {:?}", scaled);
    println!();
}

// 物理量计算演示
fn demonstrate_physics_operations() {
    println!("--- Physics Operations ---");
    
    let distance = Length(100.0); // 100 meters
    let time = Time(10.0);        // 10 seconds
    
    println!("Distance: {:?}", distance);
    println!("Time: {:?}", time);
    
    let velocity = distance / time;
    println!("Velocity: {:?}", velocity);
    
    let new_distance = velocity * time;
    println!("Calculated distance: {:?}", new_distance);
    println!();
}

// 链式计算演示
fn demonstrate_chained_operations() {
    println!("--- Chained Operations ---");
    
    let calculator = Calculator::new(10)
        .add(5)
        .mul(2)
        .sub(3)
        .div(2);
    
    calculator.show_history();
    println!("Final result: {}", calculator.result());
    println!();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_point_operations() {
        let p1 = Point { x: 1.0, y: 2.0 };
        let p2 = Point { x: 3.0, y: 4.0 };
        
        let sum = p1 + p2;
        assert_eq!(sum.x, 4.0);
        assert_eq!(sum.y, 6.0);
        
        let diff = p2 - p1;
        assert_eq!(diff.x, 2.0);
        assert_eq!(diff.y, 2.0);
        
        let scaled = p1 * 2.0;
        assert_eq!(scaled.x, 2.0);
        assert_eq!(scaled.y, 4.0);
        
        let divided = p2 / 2.0;
        assert_eq!(divided.x, 1.5);
        assert_eq!(divided.y, 2.0);
    }
    
    #[test]
    fn test_vector_operations() {
        let v1 = Vector::new(vec![1, 2, 3]);
        let v2 = Vector::new(vec![4, 5, 6]);
        
        let sum = v1.add(&v2);
        assert_eq!(sum.components, vec![5, 7, 9]);
        
        let scaled = v1.scale(2);
        assert_eq!(scaled.components, vec![2, 4, 6]);
    }
    
    #[test]
    fn test_physics_operations() {
        let distance = Length(100.0);
        let time = Time(10.0);
        
        let velocity = distance / time;
        assert_eq!(velocity.0, 10.0);
        
        let new_distance = velocity * time;
        assert_eq!(new_distance.0, 100.0);
    }
    
    #[test]
    fn test_calculator_chain() {
        let calculator = Calculator::new(10)
            .add(5)
            .mul(2)
            .sub(3)
            .div(2);
        
        assert_eq!(calculator.result(), 11);
        assert_eq!(calculator.history.len(), 4);
    }
}
