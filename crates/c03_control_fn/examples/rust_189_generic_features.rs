//! Rust 1.89 泛型系统特性示例
//! 
//! 本示例展示了Rust 1.89版本中的泛型系统增强特性：
//! - GATs (Generic Associated Types) 完全稳定
//! - 常量泛型改进
//! - 生命周期推断优化
//! - 类型级编程增强

use std::collections::HashMap;
use std::fmt::Display;
use std::ops::{Add, Mul};
use anyhow::Result;

/// Rust 1.89 GATs (Generic Associated Types) 完全稳定示例
/// 
/// GATs允许在trait中定义带有泛型参数的关联类型，实现复杂的类型级编程
trait Collection {
    type Item;
    type Iterator<'a>: Iterator<Item = &'a Self::Item>
    where
        Self: 'a;
    
    fn iter(&self) -> Self::Iterator<'_>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// 为Vec实现Collection trait
impl<T> Collection for Vec<T> {
    type Item = T;
    type Iterator<'a> = std::slice::Iter<'a, T>
    where
        Self: 'a;
    
    fn iter(&self) -> Self::Iterator<'_> {
        self.as_slice().iter()
    }
    
    fn len(&self) -> usize {
        self.len()
    }
}

/// 为HashMap实现Collection trait
impl<K, V> Collection for HashMap<K, V> {
    type Item = (K, V);
    type Iterator<'a> = std::collections::hash_map::Iter<'a, K, V>
    where
        Self: 'a;
    
    fn iter(&self) -> Self::Iterator<'_> {
        self.iter()
    }
    
    fn len(&self) -> usize {
        self.len()
    }
}

/// 高级GATs示例：类型级状态机
trait StateMachine {
    type State;
    type Event;
    type Transition<'a>: Iterator<Item = (Self::Event, Self::State)>
    where
        Self: 'a;
    
    fn current_state(&self) -> &Self::State;
    fn available_transitions(&self) -> Self::Transition<'_>;
    fn transition(&mut self, event: Self::Event) -> Result<Self::State>;
}

/// 订单状态机示例
#[derive(Debug, Clone, PartialEq)]
enum OrderState {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

#[derive(Debug, Clone)]
enum OrderEvent {
    Confirm,
    Ship,
    Deliver,
    Cancel,
}

struct Order {
    state: OrderState,
    id: String,
}

impl Order {
    fn new(id: String) -> Self {
        Self {
            state: OrderState::Pending,
            id,
        }
    }
}

impl StateMachine for Order {
    type State = OrderState;
    type Event = OrderEvent;
    type Transition<'a> = std::vec::IntoIter<(OrderEvent, OrderState)>;
    
    fn current_state(&self) -> &Self::State {
        &self.state
    }
    
    fn available_transitions(&self) -> Self::Transition<'_> {
        let transitions = match self.state {
            OrderState::Pending => vec![
                (OrderEvent::Confirm, OrderState::Confirmed),
                (OrderEvent::Cancel, OrderState::Cancelled),
            ],
            OrderState::Confirmed => vec![
                (OrderEvent::Ship, OrderState::Shipped),
                (OrderEvent::Cancel, OrderState::Cancelled),
            ],
            OrderState::Shipped => vec![
                (OrderEvent::Deliver, OrderState::Delivered),
            ],
            _ => vec![],
        };
        transitions.into_iter()
    }
    
    fn transition(&mut self, event: Self::Event) -> Result<Self::State> {
        let new_state = match (&self.state, event) {
            (OrderState::Pending, OrderEvent::Confirm) => OrderState::Confirmed,
            (OrderState::Pending, OrderEvent::Cancel) => OrderState::Cancelled,
            (OrderState::Confirmed, OrderEvent::Ship) => OrderState::Shipped,
            (OrderState::Confirmed, OrderEvent::Cancel) => OrderState::Cancelled,
            (OrderState::Shipped, OrderEvent::Deliver) => OrderState::Delivered,
            _ => return Err(anyhow::anyhow!("无效的状态转换")),
        };
        
        self.state = new_state.clone();
        Ok(new_state)
    }
}

/// Rust 1.89 常量泛型改进示例
/// 
/// 常量泛型现在支持更复杂的编译时计算和类型推导
struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Default + Copy, const ROWS: usize, const COLS: usize> Matrix<T, ROWS, COLS> {
    fn new() -> Self {
        Self {
            data: [[T::default(); COLS]; ROWS],
        }
    }
    
    fn get(&self, row: usize, col: usize) -> Option<&T> {
        if row < ROWS && col < COLS {
            Some(&self.data[row][col])
        } else {
            None
        }
    }
    
    fn set(&mut self, row: usize, col: usize, value: T) -> Result<()> {
        if row < ROWS && col < COLS {
            self.data[row][col] = value;
            Ok(())
        } else {
            Err(anyhow::anyhow!("索引超出范围"))
        }
    }
}

/// 常量泛型与类型级编程结合
impl<T: Add<Output = T> + Copy + Default, const ROWS: usize, const COLS: usize> 
    Matrix<T, ROWS, COLS> 
where
    T: Mul<Output = T>,
{
    /// 矩阵乘法：要求维度兼容
    fn multiply<const OTHER_COLS: usize>(
        &self,
        other: &Matrix<T, COLS, OTHER_COLS>,
    ) -> Matrix<T, ROWS, OTHER_COLS> {
        let mut result = Matrix::new();
        
        for i in 0..ROWS {
            for j in 0..OTHER_COLS {
                let mut sum = T::default();
                for k in 0..COLS {
                    if let (Some(a), Some(b)) = (self.get(i, k), other.get(k, j)) {
                        sum = sum + *a * *b;
                    }
                }
                let _ = result.set(i, j, sum);
            }
        }
        
        result
    }
}

/// 常量泛型函数示例
const fn calculate_size<const N: usize>() -> usize {
    N * N
}

/// 生命周期推断优化示例
/// 
/// Rust 1.89中生命周期推断有了显著改进，减少显式生命周期标注的需求
trait DataProcessor {
    type Input;
    type Output;
    
    fn process<'a>(&'a self, input: &'a Self::Input) -> Self::Output
    where
        Self::Input: 'a;
}

/// 改进的生命周期推断允许更简洁的代码
struct SimpleProcessor;

impl DataProcessor for SimpleProcessor {
    type Input = String;
    type Output = String;
    
    // Rust 1.89中，编译器可以自动推断生命周期，无需显式标注
    fn process(&self, input: &Self::Input) -> Self::Output {
        input.to_uppercase()
    }
}

/// 高级生命周期推断示例
struct AdvancedProcessor<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T> AdvancedProcessor<T> {
    fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: Display + Clone> DataProcessor for AdvancedProcessor<T> {
    type Input = T;
    type Output = String;
    
    // 编译器自动推断生命周期
    fn process(&self, input: &Self::Input) -> Self::Output {
        format!("处理结果: {}", input)
    }
}

/// 类型级编程增强示例
/// 
/// Rust 1.89中类型级编程能力得到了显著增强
trait TypeLevel {
    type Result;
    const VALUE: usize;
}

/// 类型级加法
struct Add<A, B>;

impl<A: TypeLevel, B: TypeLevel> TypeLevel for Add<A, B> {
    type Result = Add<A, B>;
    const VALUE: usize = A::VALUE + B::VALUE;
}

/// 类型级乘法
struct Multiply<A, B>;

impl<A: TypeLevel, B: TypeLevel> TypeLevel for Multiply<A, B> {
    type Result = Multiply<A, B>;
    const VALUE: usize = A::VALUE * B::VALUE;
}

/// 具体数值类型
struct N<const N: usize>;

impl<const N: usize> TypeLevel for N<N> {
    type Result = Self;
    const VALUE: usize = N;
}

/// 类型级计算示例
type Sum = Add<N<5>, N<3>>;
type Product = Multiply<N<4>, N<6>>;

/// 编译时类型检查
const _: () = {
    assert!(Sum::VALUE == 8);
    assert!(Product::VALUE == 24);
};

/// 泛型关联类型与迭代器结合
trait AdvancedIterator {
    type Item;
    type Iterator<'a>: Iterator<Item = &'a Self::Item>
    where
        Self: 'a;
    
    fn iter(&self) -> Self::Iterator<'_>;
    fn map<F, U>(&self, f: F) -> MappedIterator<Self, F, U>
    where
        F: Fn(&Self::Item) -> U,
        U: Clone,
    {
        MappedIterator {
            iter: self.iter(),
            f,
            _phantom: std::marker::PhantomData,
        }
    }
}

/// 映射迭代器实现
struct MappedIterator<I, F, U> {
    iter: I,
    f: F,
    _phantom: std::marker::PhantomData<U>,
}

impl<I, F, U> Iterator for MappedIterator<I, F, U>
where
    I: Iterator,
    F: Fn(&I::Item) -> U,
    U: Clone,
{
    type Item = U;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|item| (self.f)(item))
    }
}

/// 为Vec实现AdvancedIterator
impl<T> AdvancedIterator for Vec<T> {
    type Item = T;
    type Iterator<'a> = std::slice::Iter<'a, T>
    where
        Self: 'a;
    
    fn iter(&self) -> Self::Iterator<'_> {
        self.as_slice().iter()
    }
}

/// 主函数
fn main() -> Result<()> {
    println!("🚀 Rust 1.89 泛型系统特性演示");
    println!("=" * 50);
    
    // 1. GATs 示例
    println!("\n1. GATs (Generic Associated Types) 完全稳定示例");
    let vec_data: Vec<i32> = vec![1, 2, 3, 4, 5];
    let hash_data: HashMap<String, i32> = HashMap::from([
        ("a".to_string(), 1),
        ("b".to_string(), 2),
    ]);
    
    println!("Vec长度: {}", vec_data.len());
    println!("HashMap长度: {}", hash_data.len());
    
    // 2. 状态机示例
    println!("\n2. 高级GATs示例：类型级状态机");
    let mut order = Order::new("ORD-001".to_string());
    println!("初始状态: {:?}", order.current_state());
    
    let transitions: Vec<_> = order.available_transitions().collect();
    println!("可用转换: {:?}", transitions);
    
    order.transition(OrderEvent::Confirm)?;
    println!("确认后状态: {:?}", order.current_state());
    
    // 3. 常量泛型示例
    println!("\n3. 常量泛型改进示例");
    let mut matrix: Matrix<i32, 2, 3> = Matrix::new();
    matrix.set(0, 0, 1)?;
    matrix.set(0, 1, 2)?;
    matrix.set(1, 0, 3)?;
    matrix.set(1, 1, 4)?;
    
    println!("矩阵[0,0]: {:?}", matrix.get(0, 0));
    println!("矩阵[1,1]: {:?}", matrix.get(1, 1));
    
    // 4. 生命周期推断示例
    println!("\n4. 生命周期推断优化示例");
    let processor = SimpleProcessor;
    let input = "hello world".to_string();
    let output = processor.process(&input);
    println!("处理结果: {}", output);
    
    let advanced_processor = AdvancedProcessor::<i32>::new();
    let number = 42;
    let result = advanced_processor.process(&number);
    println!("高级处理结果: {}", result);
    
    // 5. 类型级编程示例
    println!("\n5. 类型级编程增强示例");
    println!("类型级加法: {} + {} = {}", N::<5>::VALUE, N::<3>::VALUE, Sum::VALUE);
    println!("类型级乘法: {} * {} = {}", N::<4>::VALUE, N::<6>::VALUE, Product::VALUE);
    
    // 6. 高级迭代器示例
    println!("\n6. 泛型关联类型与迭代器结合示例");
    let numbers = vec![1, 2, 3, 4, 5];
    let doubled: Vec<i32> = numbers.map(|&x| x * 2).collect();
    println!("原始数字: {:?}", numbers);
    println!("翻倍后: {:?}", doubled);
    
    println!("\n✅ Rust 1.89 泛型特性演示完成！");
    Ok(())
}
