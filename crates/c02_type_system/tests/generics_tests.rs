//! 泛型系统测试代码
//! 
//! 本文件包含了泛型系统的各种测试用例，验证：
//! - 泛型函数和结构体的正确性
//! - 特征约束的有效性
//! - 高级泛型特性的功能
//! - 性能优化效果

// 导入示例代码中的函数和结构体
use c02_type_system::examples::generics_examples::{
    identity, make_pair, Point, Container, clone_and_debug, complex_function,
    Counter, Array, longest, use_handler, StringHandler, Iterator
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identity_function() {
        assert_eq!(identity(42), 42);
        assert_eq!(identity("hello"), "hello");
        assert_eq!(identity(3.14), 3.14);
    }

    #[test]
    fn test_make_pair() {
        let pair = make_pair(42, "hello");
        assert_eq!(pair, (42, "hello"));
        
        let pair2 = make_pair(3.14, true);
        assert_eq!(pair2, (3.14, true));
    }

    #[test]
    fn test_point_struct() {
        let point_i32 = Point::new(1, 2);
        assert_eq!(point_i32.x, 1);
        assert_eq!(point_i32.y, 2);
        
        let point_f64 = Point::new(1.0, 2.0);
        assert_eq!(point_f64.x, 1.0);
        assert_eq!(point_f64.y, 2.0);
    }

    #[test]
    fn test_container() {
        let mut container = Container::new(42);
        assert_eq!(*container.get(), 42);
        
        container.set(100);
        assert_eq!(*container.get(), 100);
    }

    #[test]
    fn test_trait_constraints() {
        let result = clone_and_debug("hello");
        assert_eq!(result, "hello");
        
        let result2 = complex_function(42, "world");
        assert!(result2.contains("42") && result2.contains("world"));
    }

    #[test]
    fn test_counter_iterator() {
        let mut counter = Counter { count: 0 };
        
        assert_eq!(counter.next(), Some(&1));
        assert_eq!(counter.next(), Some(&2));
        assert_eq!(counter.next(), Some(&3));
    }

    #[test]
    fn test_array_const_generic() {
        let array: Array<i32, 5> = Array::new();
        assert_eq!(array.len(), 5);
        
        let array2: Array<String, 10> = Array::new();
        assert_eq!(array2.len(), 10);
    }

    #[test]
    fn test_variance() {
        let long = "this is a long string";
        let short = "short";
        
        let result = longest(long, short);
        assert_eq!(result, long);
    }

    #[test]
    fn test_handler() {
        let handler = StringHandler;
        // 这个测试主要验证编译通过
        use_handler(handler);
    }
}
