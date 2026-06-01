//! 编译时优化实践示例
//! compile-timeoptimizationpractice example
//!
//! 本模块演示Rust中的编译时优化技术：
//! this module demonstration Rustin compile-time optimization technique ：
//! - const fn 函数
//! - const fn function
//! - generic optimization
//! - 编译时计算
//! - compile-time
//! - 零成本抽象
//! - cost

/// 编译时常量函数
/// compile-timeconstant function
///
/// 在编译时计算，运行时零开销
/// in compile-time ，runtime overhead
pub const fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

/// 编译时数组初始化
/// compile-time
pub const fn create_lookup_table() -> [u32; 10] {
    let mut table = [0; 10];
    let mut i = 0;
    while i < 10 {
        table[i] = fibonacci(i as u32);
        i += 1;
    }
    table
}

/// 编译时优化的查找表
/// compile-timeoptimizationsearch table
pub static FIBONACCI_TABLE: [u32; 10] = create_lookup_table();

/// 泛型优化的向量操作
/// genericoptimizationvector operation
pub struct OptimizedVector<T, const N: usize> {
    data: [T; N],
    len: usize,
}

impl<T: Copy + Default, const N: usize> Default for OptimizedVector<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy + Default, const N: usize> OptimizedVector<T, N> {
    pub fn new() -> Self {
        Self {
            data: [T::default(); N],
            len: 0,
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), &'static str> {
        if self.len < N {
            self.data[self.len] = value;
            self.len += 1;
            Ok(())
        } else {
            Err("Vector is full")
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            Some(&self.data[index])
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// 编译时类型检查
/// compile-time type
pub trait CompileTimeCheck {
    const IS_VALID: bool;
}

impl<T> CompileTimeCheck for T {
    const IS_VALID: bool = true;
}

/// 编译时优化的字符串处理
/// compile-timeoptimizationstring processing
pub const fn string_length(s: &str) -> usize {
    s.len()
}

/// 编译时优化的数学运算
/// compile-time optimization
pub const fn power_of_two(n: u32) -> u32 {
    1 << n
}

/// 编译时优化的位操作
/// compile-timeoptimization operation
pub const fn count_bits(mut n: u32) -> u32 {
    let mut count = 0;
    while n > 0 {
        count += n & 1;
        n >>= 1;
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fibonacci() {
        assert_eq!(fibonacci(0), 0);
        assert_eq!(fibonacci(1), 1);
        assert_eq!(fibonacci(5), 5);
    }

    #[test]
    fn test_lookup_table() {
        assert_eq!(FIBONACCI_TABLE[0], 0);
        assert_eq!(FIBONACCI_TABLE[1], 1);
        assert_eq!(FIBONACCI_TABLE[5], 5);
    }

    #[test]
    fn test_optimized_vector() {
        let mut vec: OptimizedVector<i32, 5> = OptimizedVector::new();

        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());

        assert_eq!(vec.get(0), Some(&1));
        assert_eq!(vec.get(1), Some(&2));
        assert_eq!(vec.len(), 2);
    }

    #[test]
    fn test_compile_time_operations() {
        assert_eq!(string_length("hello"), 5);
        assert_eq!(power_of_two(3), 8);
        assert_eq!(count_bits(5), 2); // 5 = 101 in binary
    }
}
