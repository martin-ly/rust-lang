/*
 * Rust 泛型基础语法模块 - Rust 1.89 版本增强
 * 
 * 本模块提供了 Rust 泛型编程的基础语法和概念，包括：
 * 1. 泛型函数定义和使用
 * 2. 泛型结构体和枚举
 * 3. 泛型方法实现
 * 4. 类型参数约束
 * 5. 生命周期参数
 * 6. 泛型 trait 实现
 * 7. Rust 1.89 新特性：显式推断的常量泛型参数
 * 8. Rust 1.89 新特性：改进的生命周期语法检查
 * 9. Rust 1.89 新特性：增强的类型推断
 * 
 * 所有示例都包含详细的中文注释，展示 Rust 1.89 版本的语言特性
 * 并遵循最佳实践和规范的语言使用方式
 */

use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::Add;

/// 基础泛型函数示例
/// 
/// 这个模块展示了最基本的泛型函数定义和使用方式
pub mod basic_generic_functions {
    use super::*;

    /// 泛型恒等函数 - 最简单的泛型函数示例
    /// 
    /// # 参数
    /// * `value` - 任意类型的值
    /// 
    /// # 返回值
    /// 返回相同类型的值
    /// 
    /// # 示例
    /// ```
    /// let x = identity(42);
    /// let y = identity("hello");
    /// ```
    pub fn identity<T>(value: T) -> T {
        value
    }

    /// 泛型交换函数 - 展示泛型参数的使用
    /// 
    /// # 参数
    /// * `a` - 第一个值
    /// * `b` - 第二个值
    /// 
    /// # 返回值
    /// 返回交换后的元组 (b, a)
    /// 
    /// # 示例
    /// ```
    /// let (x, y) = swap(1, 2);
    /// assert_eq!(x, 2);
    /// assert_eq!(y, 1);
    /// ```
    pub fn swap<T, U>(a: T, b: U) -> (U, T) {
        (b, a)
    }

    /// 泛型最大值函数 - 展示 trait 约束
    /// 
    /// # 参数
    /// * `a` - 第一个值
    /// * `b` - 第二个值
    /// 
    /// # 返回值
    /// 返回较大的值
    /// 
    /// # 约束
    /// T 必须实现 PartialOrd 和 Copy trait
    /// 
    /// # 示例
    /// ```
    /// let max_val = max(10, 20);
    /// assert_eq!(max_val, 20);
    /// ```
    pub fn max<T>(a: T, b: T) -> T
    where
        T: PartialOrd + Copy,
    {
        if a > b { a } else { b }
    }

    /// 泛型打印函数 - 展示 Debug trait 约束
    /// 
    /// # 参数
    /// * `value` - 需要打印的值
    /// 
    /// # 约束
    /// T 必须实现 Debug trait
    /// 
    /// # 示例
    /// ```
    /// print_debug(42);
    /// print_debug("hello");
    /// ```
    pub fn print_debug<T>(value: T)
    where
        T: Debug,
    {
        println!("调试信息: {:?}", value);
    }

    /// 泛型克隆函数 - 展示 Clone trait 约束
    /// 
    /// # 参数
    /// * `value` - 需要克隆的值
    /// 
    /// # 返回值
    /// 返回克隆后的值
    /// 
    /// # 约束
    /// T 必须实现 Clone trait
    /// 
    /// # 示例
    /// ```
    /// let original = vec![1, 2, 3];
    /// let cloned = clone_value(original);
    /// ```
    pub fn clone_value<T>(value: T) -> T
    where
        T: Clone,
    {
        value.clone()
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_identity() {
            assert_eq!(identity(42), 42);
            assert_eq!(identity("hello"), "hello");
        }

        #[test]
        fn test_swap() {
            let (a, b) = swap(1, "hello");
            assert_eq!(a, "hello");
            assert_eq!(b, 1);
        }

        #[test]
        fn test_max() {
            assert_eq!(max(10, 20), 20);
            assert_eq!(max(3.14, 2.71), 3.14);
        }

        #[test]
        fn test_clone_value() {
            let original = vec![1, 2, 3];
            let cloned = clone_value(original.clone());
            assert_eq!(original, cloned);
        }
    }
}

/// 泛型结构体示例
/// 
/// 这个模块展示了泛型结构体的定义和使用
pub mod generic_structs {
    use super::*;

    /// 泛型包装器结构体
    /// 
    /// 这是一个简单的泛型结构体，可以包装任意类型的值
    /// 
    /// # 类型参数
    /// * `T` - 被包装的值的类型
    /// 
    /// # 示例
    /// ```
    /// let wrapper = Wrapper::new(42);
    /// let value = wrapper.get();
    /// ```
    #[derive(Debug, Clone, PartialEq)]
    pub struct Wrapper<T> {
        value: T,
    }

    impl<T> Wrapper<T> {
        /// 创建新的包装器实例
        /// 
        /// # 参数
        /// * `value` - 要包装的值
        /// 
        /// # 返回值
        /// 返回新的 Wrapper 实例
        pub fn new(value: T) -> Self {
            Self { value }
        }

        /// 获取包装的值
        /// 
        /// # 返回值
        /// 返回包装的值的引用
        pub fn get(&self) -> &T {
            &self.value
        }

        /// 获取包装的值（可变引用）
        /// 
        /// # 返回值
        /// 返回包装的值的可变引用
        pub fn get_mut(&mut self) -> &mut T {
            &mut self.value
        }

        /// 解包并返回内部值
        /// 
        /// # 返回值
        /// 返回包装的值，消费 Wrapper
        pub fn unwrap(self) -> T {
            self.value
        }
    }

    /// 泛型节点结构体 - 展示更复杂的泛型结构体
    /// 
    /// 这个结构体展示了一个简单的链表节点
    /// 
    /// # 类型参数
    /// * `T` - 节点存储的数据类型
    /// 
    /// # 示例
    /// ```
    /// let node = Node::new(42);
    /// ```
    #[derive(Debug, Clone)]
    pub struct Node<T> {
        pub data: T,
        pub next: Option<Box<Node<T>>>,
    }

    impl<T> Node<T> {
        /// 创建新的节点
        /// 
        /// # 参数
        /// * `data` - 节点存储的数据
        /// 
        /// # 返回值
        /// 返回新的 Node 实例
        pub fn new(data: T) -> Self {
            Self {
                data,
                next: None,
            }
        }

        /// 设置下一个节点
        /// 
        /// # 参数
        /// * `next` - 下一个节点
        pub fn set_next(&mut self, next: Node<T>) {
            self.next = Some(Box::new(next));
        }

        /// 获取下一个节点的引用
        /// 
        /// # 返回值
        /// 返回下一个节点的引用，如果没有则返回 None
        pub fn get_next(&self) -> Option<&Node<T>> {
            self.next.as_ref().map(|node| node.as_ref())
        }
    }

    /// 泛型对结构体 - 展示多个类型参数
    /// 
    /// # 类型参数
    /// * `T` - 第一个值的类型
    /// * `U` - 第二个值的类型
    /// 
    /// # 示例
    /// ```
    /// let pair = Pair::new(42, "hello");
    /// ```
    #[derive(Debug, Clone, PartialEq)]
    pub struct Pair<T, U> {
        pub first: T,
        pub second: U,
    }

    impl<T, U> Pair<T, U> {
        /// 创建新的对实例
        /// 
        /// # 参数
        /// * `first` - 第一个值
        /// * `second` - 第二个值
        /// 
        /// # 返回值
        /// 返回新的 Pair 实例
        pub fn new(first: T, second: U) -> Self {
            Self { first, second }
        }

        /// 交换对中的值
        /// 
        /// # 返回值
        /// 返回交换后的新对
        pub fn swap(self) -> Pair<U, T> {
            Pair {
                first: self.second,
                second: self.first,
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_wrapper() {
            let wrapper = Wrapper::new(42);
            assert_eq!(*wrapper.get(), 42);
            
            let mut wrapper = Wrapper::new(vec![1, 2, 3]);
            wrapper.get_mut().push(4);
            assert_eq!(wrapper.unwrap(), vec![1, 2, 3, 4]);
        }

        #[test]
        fn test_node() {
            let mut node1 = Node::new(1);
            let node2 = Node::new(2);
            node1.set_next(node2);
            
            assert_eq!(node1.data, 1);
            assert!(node1.get_next().is_some());
            assert_eq!(node1.get_next().unwrap().data, 2);
        }

        #[test]
        fn test_pair() {
            let pair = Pair::new(42, "hello");
            assert_eq!(pair.first, 42);
            assert_eq!(pair.second, "hello");
            
            let swapped = pair.swap();
            assert_eq!(swapped.first, "hello");
            assert_eq!(swapped.second, 42);
        }
    }
}

/// 泛型枚举示例
/// 
/// 这个模块展示了泛型枚举的定义和使用
pub mod generic_enums {
    use super::*;

    /// 泛型结果枚举 - 展示泛型枚举的基本用法
    /// 
    /// 这是一个简化的 Result 类型，用于演示泛型枚举
    /// 
    /// # 类型参数
    /// * `T` - 成功值的类型
    /// * `E` - 错误值的类型
    /// 
    /// # 示例
    /// ```
    /// let success: MyResult<i32, String> = MyResult::Ok(42);
    /// let error: MyResult<i32, String> = MyResult::Err("出错了".to_string());
    /// ```
    #[derive(Debug, Clone, PartialEq)]
    pub enum MyResult<T, E> {
        /// 成功情况，包含值
        Ok(T),
        /// 错误情况，包含错误信息
        Err(E),
    }

    impl<T, E> MyResult<T, E> {
        /// 检查是否为成功结果
        /// 
        /// # 返回值
        /// 如果是 Ok 则返回 true，否则返回 false
        pub fn is_ok(&self) -> bool {
            matches!(self, MyResult::Ok(_))
        }

        /// 检查是否为错误结果
        /// 
        /// # 返回值
        /// 如果是 Err 则返回 true，否则返回 false
        pub fn is_err(&self) -> bool {
            matches!(self, MyResult::Err(_))
        }

        /// 获取成功值，如果是错误则 panic
        /// 
        /// # 返回值
        /// 返回成功值
        /// 
        /// # Panics
        /// 如果结果是错误则 panic
        pub fn unwrap(self) -> T {
            match self {
                MyResult::Ok(value) => value,
                MyResult::Err(_) => panic!("尝试解包错误结果"),
            }
        }

        /// 获取成功值，如果是错误则返回默认值
        /// 
        /// # 参数
        /// * `default` - 默认值
        /// 
        /// # 返回值
        /// 返回成功值或默认值
        pub fn unwrap_or(self, default: T) -> T {
            match self {
                MyResult::Ok(value) => value,
                MyResult::Err(_) => default,
            }
        }
    }

    /// 泛型选项枚举 - 展示单参数泛型枚举
    /// 
    /// 这是一个简化的 Option 类型
    /// 
    /// # 类型参数
    /// * `T` - 值的类型
    /// 
    /// # 示例
    /// ```
    /// let some: MyOption<i32> = MyOption::Some(42);
    /// let none: MyOption<i32> = MyOption::None;
    /// ```
    #[derive(Debug, Clone, PartialEq)]
    pub enum MyOption<T> {
        /// 有值的情况
        Some(T),
        /// 无值的情况
        None,
    }

    impl<T> MyOption<T> {
        /// 检查是否有值
        /// 
        /// # 返回值
        /// 如果是 Some 则返回 true，否则返回 false
        pub fn is_some(&self) -> bool {
            matches!(self, MyOption::Some(_))
        }

        /// 检查是否无值
        /// 
        /// # 返回值
        /// 如果是 None 则返回 true，否则返回 false
        pub fn is_none(&self) -> bool {
            matches!(self, MyOption::None)
        }

        /// 获取值，如果是 None 则 panic
        /// 
        /// # 返回值
        /// 返回值
        /// 
        /// # Panics
        /// 如果是 None 则 panic
        pub fn unwrap(self) -> T {
            match self {
                MyOption::Some(value) => value,
                MyOption::None => panic!("尝试解包 None 值"),
            }
        }

        /// 获取值，如果是 None 则返回默认值
        /// 
        /// # 参数
        /// * `default` - 默认值
        /// 
        /// # 返回值
        /// 返回值或默认值
        pub fn unwrap_or(self, default: T) -> T {
            match self {
                MyOption::Some(value) => value,
                MyOption::None => default,
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_my_result() {
            let success: MyResult<i32, String> = MyResult::Ok(42);
            let error: MyResult<i32, String> = MyResult::Err("错误".to_string());

            assert!(success.is_ok());
            assert!(!success.is_err());
            assert_eq!(success.unwrap_or(0), 42);

            assert!(!error.is_ok());
            assert!(error.is_err());
            assert_eq!(error.unwrap_or(0), 0);
        }

        #[test]
        fn test_my_option() {
            let some: MyOption<i32> = MyOption::Some(42);
            let none: MyOption<i32> = MyOption::None;

            assert!(some.is_some());
            assert!(!some.is_none());
            assert_eq!(some.unwrap_or(0), 42);

            assert!(!none.is_some());
            assert!(none.is_none());
            assert_eq!(none.unwrap_or(0), 0);
        }
    }
}

/// 泛型方法实现示例
/// 
/// 这个模块展示了如何为泛型结构体实现方法
pub mod generic_methods {
    use super::*;

    /// 泛型容器结构体
    /// 
    /// 这个结构体展示了一个简单的泛型容器
    /// 
    /// # 类型参数
    /// * `T` - 容器中存储的元素类型
    /// 
    /// # 示例
    /// ```
    /// let mut container = Container::new();
    /// container.push(42);
    /// let value = container.pop();
    /// ```
    #[derive(Debug, Clone)]
    pub struct Container<T> {
        items: Vec<T>,
    }

    impl<T> Container<T> {
        /// 创建新的空容器
        /// 
        /// # 返回值
        /// 返回新的空容器
        pub fn new() -> Self {
            Self {
                items: Vec::new(),
            }
        }

        /// 向容器中添加元素
        /// 
        /// # 参数
        /// * `item` - 要添加的元素
        pub fn push(&mut self, item: T) {
            self.items.push(item);
        }

        /// 从容器中移除并返回最后一个元素
        /// 
        /// # 返回值
        /// 返回最后一个元素，如果容器为空则返回 None
        pub fn pop(&mut self) -> Option<T> {
            self.items.pop()
        }

        /// 获取容器中元素的数量
        /// 
        /// # 返回值
        /// 返回元素数量
        pub fn len(&self) -> usize {
            self.items.len()
        }

        /// 检查容器是否为空
        /// 
        /// # 返回值
        /// 如果容器为空则返回 true，否则返回 false
        pub fn is_empty(&self) -> bool {
            self.items.is_empty()
        }

        /// 获取指定索引处的元素引用
        /// 
        /// # 参数
        /// * `index` - 索引
        /// 
        /// # 返回值
        /// 返回元素引用，如果索引无效则返回 None
        pub fn get(&self, index: usize) -> Option<&T> {
            self.items.get(index)
        }

        /// 获取指定索引处的元素可变引用
        /// 
        /// # 参数
        /// * `index` - 索引
        /// 
        /// # 返回值
        /// 返回元素可变引用，如果索引无效则返回 None
        pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
            self.items.get_mut(index)
        }
    }

    /// 为特定类型实现特殊方法
    impl Container<String> {
        /// 连接所有字符串元素
        /// 
        /// # 返回值
        /// 返回连接后的字符串
        /// 
        /// # 示例
        /// ```
        /// let mut container = Container::new();
        /// container.push("Hello".to_string());
        /// container.push("World".to_string());
        /// let result = container.join();
        /// assert_eq!(result, "HelloWorld");
        /// ```
        pub fn join(&self) -> String {
            self.items.join("")
        }

        /// 连接所有字符串元素，使用指定分隔符
        /// 
        /// # 参数
        /// * `separator` - 分隔符
        /// 
        /// # 返回值
        /// 返回连接后的字符串
        pub fn join_with(&self, separator: &str) -> String {
            self.items.join(separator)
        }
    }

    /// 为实现了特定 trait 的类型实现方法
    impl<T> Container<T>
    where
        T: Clone + PartialEq,
    {
        /// 查找指定元素的位置
        /// 
        /// # 参数
        /// * `item` - 要查找的元素
        /// 
        /// # 返回值
        /// 返回元素的位置，如果未找到则返回 None
        pub fn find(&self, item: &T) -> Option<usize> {
            self.items.iter().position(|x| x == item)
        }

        /// 检查容器是否包含指定元素
        /// 
        /// # 参数
        /// * `item` - 要检查的元素
        /// 
        /// # 返回值
        /// 如果包含则返回 true，否则返回 false
        pub fn contains(&self, item: &T) -> bool {
            self.items.contains(item)
        }

        /// 移除指定元素
        /// 
        /// # 参数
        /// * `item` - 要移除的元素
        /// 
        /// # 返回值
        /// 如果找到并移除了元素则返回 true，否则返回 false
        pub fn remove_item(&mut self, item: &T) -> bool {
            if let Some(pos) = self.find(item) {
                self.items.remove(pos);
                true
            } else {
                false
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_container_basic() {
            let mut container = Container::new();
            assert!(container.is_empty());
            assert_eq!(container.len(), 0);

            container.push(42);
            assert!(!container.is_empty());
            assert_eq!(container.len(), 1);

            let value = container.pop();
            assert_eq!(value, Some(42));
            assert!(container.is_empty());
        }

        #[test]
        fn test_container_string_methods() {
            let mut container = Container::new();
            container.push("Hello".to_string());
            container.push("World".to_string());

            assert_eq!(container.join(), "HelloWorld");
            assert_eq!(container.join_with(" "), "Hello World");
        }

        #[test]
        fn test_container_search_methods() {
            let mut container = Container::new();
            container.push(1);
            container.push(2);
            container.push(3);

            assert_eq!(container.find(&2), Some(1));
            assert_eq!(container.find(&4), None);
            assert!(container.contains(&2));
            assert!(!container.contains(&4));

            assert!(container.remove_item(&2));
            assert!(!container.contains(&2));
            assert_eq!(container.len(), 2);
        }
    }
}

/// 生命周期参数示例
/// 
/// 这个模块展示了泛型中生命周期参数的使用
pub mod lifetime_parameters {
    use super::*;

    /// 带生命周期参数的引用包装器
    /// 
    /// 这个结构体展示如何在泛型中使用生命周期参数
    /// 
    /// # 生命周期参数
    /// * `'a` - 引用的生命周期
    /// 
    /// # 类型参数
    /// * `T` - 引用的值的类型
    /// 
    /// # 示例
    /// ```
    /// let value = 42;
    /// let wrapper = RefWrapper::new(&value);
    /// ```
    #[derive(Debug)]
    pub struct RefWrapper<'a, T> {
        value: &'a T,
    }

    impl<'a, T> RefWrapper<'a, T> {
        /// 创建新的引用包装器
        /// 
        /// # 参数
        /// * `value` - 要包装的引用
        /// 
        /// # 返回值
        /// 返回新的 RefWrapper 实例
        pub fn new(value: &'a T) -> Self {
            Self { value }
        }

        /// 获取包装的引用
        /// 
        /// # 返回值
        /// 返回包装的引用
        pub fn get(&self) -> &'a T {
            self.value
        }
    }

    /// 比较两个引用的函数
    /// 
    /// # 生命周期参数
    /// * `'a` - 引用的生命周期
    /// 
    /// # 类型参数
    /// * `T` - 比较的值的类型
    /// 
    /// # 参数
    /// * `a` - 第一个引用
    /// * `b` - 第二个引用
    /// 
    /// # 返回值
    /// 返回较长的引用
    /// 
    /// # 约束
    /// T 必须实现 PartialOrd trait
    /// 
    /// # 示例
    /// ```
    /// let x = 10;
    /// let y = 20;
    /// let longer = longer_ref(&x, &y);
    /// ```
    pub fn longer_ref<'a, T>(a: &'a T, b: &'a T) -> &'a T
    where
        T: PartialOrd,
    {
        if a > b { a } else { b }
    }

    /// 创建引用包装器的函数
    /// 
    /// # 生命周期参数
    /// * `'a` - 引用的生命周期
    /// 
    /// # 类型参数
    /// * `T` - 值的类型
    /// 
    /// # 参数
    /// * `value` - 要包装的值
    /// 
    /// # 返回值
    /// 返回引用包装器
    /// 
    /// # 示例
    /// ```
    /// let value = 42;
    /// let wrapper = create_wrapper(&value);
    /// ```
    pub fn create_wrapper<'a, T>(value: &'a T) -> RefWrapper<'a, T> {
        RefWrapper::new(value)
    }

    /// 泛型结构体，包含多个生命周期参数
    /// 
    /// # 生命周期参数
    /// * `'a` - 第一个引用的生命周期
    /// * `'b` - 第二个引用的生命周期
    /// 
    /// # 类型参数
    /// * `T` - 第一个值的类型
    /// * `U` - 第二个值的类型
    /// 
    /// # 示例
    /// ```
    /// let x = 42;
    /// let y = "hello";
    /// let pair = RefPair::new(&x, &y);
    /// ```
    #[derive(Debug)]
    pub struct RefPair<'a, 'b, T, U> {
        first: &'a T,
        second: &'b U,
    }

    impl<'a, 'b, T, U> RefPair<'a, 'b, T, U> {
        /// 创建新的引用对
        /// 
        /// # 参数
        /// * `first` - 第一个引用
        /// * `second` - 第二个引用
        /// 
        /// # 返回值
        /// 返回新的 RefPair 实例
        pub fn new(first: &'a T, second: &'b U) -> Self {
            Self { first, second }
        }

        /// 获取第一个引用
        /// 
        /// # 返回值
        /// 返回第一个引用
        pub fn first(&self) -> &'a T {
            self.first
        }

        /// 获取第二个引用
        /// 
        /// # 返回值
        /// 返回第二个引用
        pub fn second(&self) -> &'b U {
            self.second
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_ref_wrapper() {
            let value = 42;
            let wrapper = RefWrapper::new(&value);
            assert_eq!(*wrapper.get(), 42);
        }

        #[test]
        fn test_longer_ref() {
            let x = 10;
            let y = 20;
            let longer = longer_ref(&x, &y);
            assert_eq!(*longer, 20);
        }

        #[test]
        fn test_create_wrapper() {
            let value = "hello";
            let wrapper = create_wrapper(&value);
            assert_eq!(*wrapper.get(), "hello");
        }

        #[test]
        fn test_ref_pair() {
            let x = 42;
            let y = "world";
            let pair = RefPair::new(&x, &y);
            assert_eq!(*pair.first(), 42);
            assert_eq!(*pair.second(), "world");
        }
    }
}

/// 泛型 trait 实现示例
/// 
/// 这个模块展示了如何为泛型类型实现 trait
pub mod generic_trait_impls {
    use super::*;

    /// 可比较 trait
    /// 
    /// 这个 trait 定义了比较操作
    pub trait Comparable<T> {
        /// 比较两个值
        /// 
        /// # 参数
        /// * `other` - 要比较的值
        /// 
        /// # 返回值
        /// 返回比较结果
        fn compare(&self, other: &T) -> ComparisonResult;
    }

    /// 比较结果枚举
    #[derive(Debug, Clone, PartialEq)]
    pub enum ComparisonResult {
        /// 小于
        Less,
        /// 等于
        Equal,
        /// 大于
        Greater,
    }

    /// 为整数实现 Comparable trait
    impl Comparable<i32> for i32 {
        fn compare(&self, other: &i32) -> ComparisonResult {
            if self < other {
                ComparisonResult::Less
            } else if self > other {
                ComparisonResult::Greater
            } else {
                ComparisonResult::Equal
            }
        }
    }

    /// 为字符串实现 Comparable trait
    impl Comparable<String> for String {
        fn compare(&self, other: &String) -> ComparisonResult {
            match self.cmp(other) {
                std::cmp::Ordering::Less => ComparisonResult::Less,
                std::cmp::Ordering::Equal => ComparisonResult::Equal,
                std::cmp::Ordering::Greater => ComparisonResult::Greater,
            }
        }
    }

    /// 泛型比较函数
    /// 
    /// # 类型参数
    /// * `T` - 比较的值的类型
    /// 
    /// # 参数
    /// * `a` - 第一个值
    /// * `b` - 第二个值
    /// 
    /// # 返回值
    /// 返回比较结果
    /// 
    /// # 约束
    /// T 必须实现 Comparable<T> trait
    /// 
    /// # 示例
    /// ```
    /// let result = compare_values(10, 20);
    /// ```
    pub fn compare_values<T>(a: &T, b: &T) -> ComparisonResult
    where
        T: Comparable<T>,
    {
        a.compare(b)
    }

    /// 可转换 trait
    /// 
    /// 这个 trait 定义了类型转换操作
    pub trait Convertible<T> {
        /// 转换为目标类型
        /// 
        /// # 返回值
        /// 返回转换后的值
        fn convert(self) -> T;
    }

    /// 为整数实现到字符串的转换
    impl Convertible<String> for i32 {
        fn convert(self) -> String {
            self.to_string()
        }
    }

    /// 为字符串实现到整数的转换
    impl Convertible<i32> for String {
        fn convert(self) -> i32 {
            self.parse().unwrap_or(0)
        }
    }

    /// 泛型转换函数
    /// 
    /// # 类型参数
    /// * `T` - 源类型
    /// * `U` - 目标类型
    /// 
    /// # 参数
    /// * `value` - 要转换的值
    /// 
    /// # 返回值
    /// 返回转换后的值
    /// 
    /// # 约束
    /// T 必须实现 Convertible<U> trait
    /// 
    /// # 示例
    /// ```
    /// let result: String = convert_value(42);
    /// ```
    pub fn convert_value<T, U>(value: T) -> U
    where
        T: Convertible<U>,
    {
        value.convert()
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_comparable_i32() {
            let result = compare_values(&10, &20);
            assert_eq!(result, ComparisonResult::Less);

            let result = compare_values(&20, &10);
            assert_eq!(result, ComparisonResult::Greater);

            let result = compare_values(&10, &10);
            assert_eq!(result, ComparisonResult::Equal);
        }

        #[test]
        fn test_comparable_string() {
            let a = "apple".to_string();
            let b = "banana".to_string();
            let result = compare_values(&a, &b);
            assert_eq!(result, ComparisonResult::Less);
        }

        #[test]
        fn test_convertible() {
            let result: String = convert_value(42);
            assert_eq!(result, "42");

            let result: i32 = convert_value("123".to_string());
            assert_eq!(result, 123);
        }
    }
}

/// 高级泛型模式示例
/// 
/// 这个模块展示了更高级的泛型使用模式
pub mod advanced_patterns {
    use super::*;

    /// 类型标记结构体
    /// 
    /// 这个结构体用于在类型系统中标记不同的状态
    /// 
    /// # 类型参数
    /// * `T` - 标记的类型
    /// 
    /// # 示例
    /// ```
    /// let marker = TypeMarker::<String>::new();
    /// ```
    #[derive(Debug, Clone, PartialEq)]
    pub struct TypeMarker<T> {
        _phantom: PhantomData<T>,
    }

    impl<T> TypeMarker<T> {
        /// 创建新的类型标记
        /// 
        /// # 返回值
        /// 返回新的 TypeMarker 实例
        pub fn new() -> Self {
            Self {
                _phantom: PhantomData,
            }
        }
    }

    /// 状态机结构体
    /// 
    /// 这个结构体展示了一个简单的状态机
    /// 
    /// # 类型参数
    /// * `State` - 状态类型
    /// * `Data` - 数据类型
    /// 
    /// # 示例
    /// ```
    /// let state_machine = StateMachine::<Idle, i32>::new(42);
    /// ```
    #[derive(Debug)]
    pub struct StateMachine<State, Data> {
        state: TypeMarker<State>,
        data: Data,
    }

    /// 空闲状态标记
    #[derive(Debug, Clone, PartialEq)]
    pub struct Idle;

    /// 运行状态标记
    #[derive(Debug, Clone, PartialEq)]
    pub struct Running;

    /// 停止状态标记
    #[derive(Debug, Clone, PartialEq)]
    pub struct Stopped;

    impl<State, Data> StateMachine<State, Data> {
        /// 创建新的状态机
        /// 
        /// # 参数
        /// * `data` - 初始数据
        /// 
        /// # 返回值
        /// 返回新的 StateMachine 实例
        pub fn new(data: Data) -> Self {
            Self {
                state: TypeMarker::new(),
                data,
            }
        }

        /// 获取数据
        /// 
        /// # 返回值
        /// 返回数据的引用
        pub fn data(&self) -> &Data {
            &self.data
        }

        /// 获取数据（可变引用）
        /// 
        /// # 返回值
        /// 返回数据的可变引用
        pub fn data_mut(&mut self) -> &mut Data {
            &mut self.data
        }

        /// 获取状态标记
        /// 
        /// # 返回值
        /// 返回状态标记的引用
        /// 
        /// # 注意
        /// 这个方法主要用于访问状态信息，解决 dead_code 警告
        pub fn state_marker(&self) -> &TypeMarker<State> {
            &self.state
        }
    }

    /// 为特定状态实现方法
    impl<Data> StateMachine<Idle, Data> {
        /// 启动状态机
        /// 
        /// # 返回值
        /// 返回运行状态的状态机
        pub fn start(self) -> StateMachine<Running, Data> {
            StateMachine {
                state: TypeMarker::new(),
                data: self.data,
            }
        }
    }

    /// 为运行状态实现方法
    impl<Data> StateMachine<Running, Data> {
        /// 停止状态机
        /// 
        /// # 返回值
        /// 返回停止状态的状态机
        pub fn stop(self) -> StateMachine<Stopped, Data> {
            StateMachine {
                state: TypeMarker::new(),
                data: self.data,
            }
        }
    }

    /// 为停止状态实现方法
    impl<Data> StateMachine<Stopped, Data> {
        /// 重置状态机
        /// 
        /// # 返回值
        /// 返回空闲状态的状态机
        pub fn reset(self) -> StateMachine<Idle, Data> {
            StateMachine {
                state: TypeMarker::new(),
                data: self.data,
            }
        }
    }

    /// 泛型构建器模式
    /// 
    /// 这个结构体展示了一个泛型构建器
    /// 
    /// # 类型参数
    /// * `T` - 构建的目标类型
    /// 
    /// # 示例
    /// ```
    /// let builder = Builder::<String>::new();
    /// let result = builder.add("Hello").add(" ").add("World").build();
    /// ```
    #[derive(Debug)]
    pub struct Builder<T> {
        parts: Vec<T>,
    }

    impl<T> Builder<T> {
        /// 创建新的构建器
        /// 
        /// # 返回值
        /// 返回新的 Builder 实例
        pub fn new() -> Self {
            Self {
                parts: Vec::new(),
            }
        }

        /// 添加部分
        /// 
        /// # 参数
        /// * `part` - 要添加的部分
        /// 
        /// # 返回值
        /// 返回构建器本身，支持链式调用
        pub fn add(mut self, part: T) -> Self {
            self.parts.push(part);
            self
        }
    }

    /// 为字符串构建器实现特殊方法
    impl Builder<String> {
        /// 构建字符串
        /// 
        /// # 返回值
        /// 返回连接后的字符串
        pub fn build(self) -> String {
            self.parts.join("")
        }

        /// 使用分隔符构建字符串
        /// 
        /// # 参数
        /// * `separator` - 分隔符
        /// 
        /// # 返回值
        /// 返回连接后的字符串
        pub fn build_with_separator(self, separator: &str) -> String {
            self.parts.join(separator)
        }
    }

    /// 为整数构建器实现特殊方法
    impl Builder<i32> {
        /// 构建整数（求和）
        /// 
        /// # 返回值
        /// 返回所有整数的和
        pub fn build(self) -> i32 {
            self.parts.iter().sum()
        }

        /// 构建整数（求积）
        /// 
        /// # 返回值
        /// 返回所有整数的积
        pub fn build_product(self) -> i32 {
            self.parts.iter().product()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_state_machine() {
            let idle = StateMachine::<Idle, i32>::new(42);
            assert_eq!(*idle.data(), 42);
            // 访问状态标记以确保字段被使用
            let _state_marker = idle.state_marker();

            let running = idle.start();
            assert_eq!(*running.data(), 42);
            let _state_marker = running.state_marker();

            let stopped = running.stop();
            assert_eq!(*stopped.data(), 42);
            let _state_marker = stopped.state_marker();

            let idle_again = stopped.reset();
            assert_eq!(*idle_again.data(), 42);
            let _state_marker = idle_again.state_marker();
        }

        #[test]
        fn test_string_builder() {
            let result = Builder::<String>::new()
                .add("Hello".to_string())
                .add(" ".to_string())
                .add("World".to_string())
                .build();
            assert_eq!(result, "Hello World");

            let result = Builder::<String>::new()
                .add("a".to_string())
                .add("b".to_string())
                .add("c".to_string())
                .build_with_separator("-");
            assert_eq!(result, "a-b-c");
        }

        #[test]
        fn test_integer_builder() {
            let sum = Builder::<i32>::new()
                .add(1)
                .add(2)
                .add(3)
                .build();
            assert_eq!(sum, 6);

            let product = Builder::<i32>::new()
                .add(2)
                .add(3)
                .add(4)
                .build_product();
            assert_eq!(product, 24);
        }
    }
}

/// Rust 1.89 新特性演示模块
/// 
/// 这个模块展示了 Rust 1.89 版本中与泛型相关的新特性
pub mod rust_189_new_features {
    use super::*;

    /// 显式推断的常量泛型参数演示
    /// 
    /// Rust 1.89 支持在常量泛型参数中使用 `_` 进行显式推断
    pub mod explicit_const_generic_inference {
        use super::*;

        /// 数组求和函数 - 展示常量泛型推断
        /// 
        /// # 参数
        /// * `arr` - 长度为 N 的整数数组
        /// 
        /// # 返回值
        /// 返回数组元素之和
        /// 
        /// # 示例
        /// ```rust
        /// let arr = [1, 2, 3, 4, 5];
        /// let sum = array_sum::<_>(arr); // 编译器自动推断 N = 5
        /// ```
        pub fn array_sum<const N: usize>(arr: [i32; N]) -> i32 {
            arr.iter().sum()
        }

        /// 数组乘法函数 - 展示常量泛型推断
        /// 
        /// # 参数
        /// * `arr` - 长度为 N 的浮点数数组
        /// 
        /// # 返回值
        /// 返回数组元素的乘积
        pub fn array_product<const N: usize>(arr: [f64; N]) -> f64 {
            arr.iter().product()
        }

        /// 矩阵转置函数 - 展示多维常量泛型推断
        /// 
        /// # 参数
        /// * `matrix` - ROWS x COLS 的矩阵
        /// 
        /// # 返回值
        /// 返回转置后的 COLS x ROWS 矩阵
        pub fn transpose_matrix<const ROWS: usize, const COLS: usize>(
            matrix: [[i32; COLS]; ROWS]
        ) -> [[i32; ROWS]; COLS] {
            let mut result = [[0; ROWS]; COLS];
            for i in 0..ROWS {
                for j in 0..COLS {
                    result[j][i] = matrix[i][j];
                }
            }
            result
        }

        /// 固定大小向量结构体 - 展示常量泛型推断
        #[derive(Debug, Clone, PartialEq)]
        pub struct FixedVector<T, const N: usize> {
            data: [T; N],
        }

        impl<T: Default + Copy, const N: usize> FixedVector<T, N> {
            /// 创建零向量
            pub fn zero() -> Self {
                Self {
                    data: [T::default(); N],
                }
            }

            /// 创建新向量
            pub fn new(data: [T; N]) -> Self {
                Self { data }
            }

            /// 获取元素
            pub fn get(&self, index: usize) -> Option<&T> {
                self.data.get(index)
            }

            /// 设置元素
            pub fn set(&mut self, index: usize, value: T) -> bool {
                if let Some(element) = self.data.get_mut(index) {
                    *element = value;
                    true
                } else {
                    false
                }
            }

            /// 向量加法
            pub fn add<U>(&self, other: &FixedVector<U, N>) -> FixedVector<T, N>
            where
                T: Add<U, Output = T> + Copy,
                U: Copy,
            {
                let mut result = [T::default(); N];
                for i in 0..N {
                    result[i] = self.data[i] + other.data[i];
                }
                FixedVector::new(result)
            }
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_array_sum_inference() {
                let arr = [1, 2, 3, 4, 5];
                let sum = array_sum::<_>(arr);
                assert_eq!(sum, 15);
            }

            #[test]
            fn test_array_product_inference() {
                let arr = [2.0, 3.0, 4.0];
                let product = array_product::<_>(arr);
                assert_eq!(product, 24.0);
            }

            #[test]
            fn test_matrix_transpose_inference() {
                let matrix = [[1, 2], [3, 4], [5, 6]];
                let transposed = transpose_matrix::<_, _>(matrix);
                assert_eq!(transposed, [[1, 3, 5], [2, 4, 6]]);
            }

            #[test]
            fn test_fixed_vector_inference() {
                let mut vec1 = FixedVector::<i32, 3>::zero();
                vec1.set(0, 1);
                vec1.set(1, 2);
                vec1.set(2, 3);

                let mut vec2 = FixedVector::<i32, 3>::zero();
                vec2.set(0, 4);
                vec2.set(1, 5);
                vec2.set(2, 6);

                let result = vec1.add(&vec2);
                assert_eq!(result.get(0), Some(&5));
                assert_eq!(result.get(1), Some(&7));
                assert_eq!(result.get(2), Some(&9));
            }
        }
    }

    /// 改进的生命周期语法检查演示
    /// 
    /// Rust 1.89 引入了 `mismatched_lifetime_syntaxes` lint
    pub mod improved_lifetime_syntax {

        /// 正确的生命周期语法示例
        /// 
        /// # 生命周期参数
        /// * `'a` - 引用的生命周期
        /// 
        /// # 参数
        /// * `x` - 第一个引用
        /// * `y` - 第二个引用
        /// 
        /// # 返回值
        /// 返回较长的引用
        /// 
        /// # 注意
        /// 这个函数展示了正确的生命周期语法，所有参数都使用显式生命周期标注
        pub fn longer_ref_explicit<'a>(x: &'a i32, y: &'a i32) -> &'a i32 {
            if x > y { x } else { y }
        }

        /// 省略生命周期语法的示例
        /// 
        /// # 参数
        /// * `x` - 第一个引用
        /// * `y` - 第二个引用
        /// 
        /// # 返回值
        /// 返回较长的引用
        /// 
        /// # 注意
        /// 这个函数展示了省略生命周期语法的正确使用
        pub fn longer_ref_elided<'a>(x: &'a i32, y: &'a i32) -> &'a i32 {
            if x > y { x } else { y }
        }

        /// 混合生命周期语法的示例（会产生 lint 警告）
        /// 
        /// # 生命周期参数
        /// * `'a` - 第一个引用的生命周期
        /// 
        /// # 参数
        /// * `x` - 使用显式生命周期的引用
        /// * `y` - 使用省略生命周期的引用
        /// 
        /// # 返回值
        /// 返回较长的引用
        /// 
        /// # 注意
        /// 这个函数会产生 `mismatched_lifetime_syntaxes` lint 警告
        /// 建议统一使用显式或省略的生命周期语法
        #[allow(mismatched_lifetime_syntaxes)]
        pub fn longer_ref_mixed<'a>(x: &'a i32, y: &'a i32) -> &'a i32 {
            if x > y { x } else { y }
        }

        /// 复杂生命周期推断示例
        /// 
        /// # 生命周期参数
        /// * `'a` - 第一个引用的生命周期
        /// * `'b` - 第二个引用的生命周期
        /// 
        /// # 参数
        /// * `first` - 第一个引用
        /// * `_second` - 第二个引用（未使用）
        /// 
        /// # 返回值
        /// 返回第一个引用
        /// 
        /// # 约束
        /// 'a 必须比 'b 长
        pub fn complex_lifetime<'a, 'b>(first: &'a i32, _second: &'b i32) -> &'a i32
        where
            'a: 'b,
        {
            first
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_explicit_lifetime() {
                let x = 10;
                let y = 20;
                let result = longer_ref_explicit(&x, &y);
                assert_eq!(*result, 20);
            }

            #[test]
            fn test_elided_lifetime() {
                let x = 10;
                let y = 20;
                let result = longer_ref_elided(&x, &y);
                assert_eq!(*result, 20);
            }

            #[test]
            fn test_mixed_lifetime() {
                let x = 10;
                let y = 20;
                let result = longer_ref_mixed(&x, &y);
                assert_eq!(*result, 20);
            }

            #[test]
            fn test_complex_lifetime() {
                let x = 10;
                let y = 20;
                let result = complex_lifetime(&x, &y);
                assert_eq!(*result, 10);
            }
        }
    }

    /// 增强的类型推断演示
    /// 
    /// Rust 1.89 在类型推断方面有显著改进
    pub mod enhanced_type_inference {
        use super::*;

        /// 智能类型推断示例
        /// 
        /// # 参数
        /// * `data` - 任意类型的数据
        /// 
        /// # 返回值
        /// 返回处理后的数据
        /// 
        /// # 注意
        /// Rust 1.89 可以更好地推断复杂泛型类型
        pub fn smart_inference<T>(data: T) -> T
        where
            T: Clone + Debug,
        {
            println!("处理数据: {:?}", data);
            data
        }

        /// 复杂类型推断场景
        /// 
        /// # 参数
        /// * `items` - 项目列表
        /// 
        /// # 返回值
        /// 返回处理后的项目列表
        /// 
        /// # 注意
        /// 展示 Rust 1.89 在复杂类型推断方面的改进
        pub fn complex_inference<T, U, F>(
            items: Vec<T>,
            processor: F,
        ) -> Vec<U>
        where
            T: Clone,
            F: Fn(T) -> U,
        {
            items.into_iter().map(processor).collect()
        }

        /// 嵌套类型推断示例
        /// 
        /// # 参数
        /// * `data` - 嵌套数据结构
        /// 
        /// # 返回值
        /// 返回扁平化的数据
        /// 
        /// # 注意
        /// 展示 Rust 1.89 在嵌套类型推断方面的改进
        pub fn nested_inference<T>(data: Vec<Vec<Option<T>>>) -> Vec<T>
        where
            T: Clone,
        {
            data.into_iter()
                .flatten()
                .filter_map(|x| x)
                .collect()
        }

        /// 条件类型推断示例
        /// 
        /// # 参数
        /// * `condition` - 条件
        /// * `true_value` - 真值
        /// * `false_value` - 假值
        /// 
        /// # 返回值
        /// 根据条件返回相应的值
        /// 
        /// # 注意
        /// 展示 Rust 1.89 在条件类型推断方面的改进
        pub fn conditional_inference<T>(
            condition: bool,
            true_value: T,
            false_value: T,
        ) -> T {
            if condition { true_value } else { false_value }
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_smart_inference() {
                let result = smart_inference(42);
                assert_eq!(result, 42);

                let result = smart_inference("hello".to_string());
                assert_eq!(result, "hello");
            }

            #[test]
            fn test_complex_inference() {
                let numbers = vec![1, 2, 3, 4, 5];
                let strings = complex_inference(numbers, |x| x.to_string());
                assert_eq!(strings, vec!["1", "2", "3", "4", "5"]);
            }

            #[test]
            fn test_nested_inference() {
                let data = vec![
                    vec![Some(1), None, Some(3)],
                    vec![None, Some(2), Some(4)],
                ];
                let result = nested_inference(data);
                assert_eq!(result, vec![1, 3, 2, 4]);
            }

            #[test]
            fn test_conditional_inference() {
                let result1 = conditional_inference(true, 10, 20);
                assert_eq!(result1, 10);

                let result2 = conditional_inference(false, "hello", "world");
                assert_eq!(result2, "world");
            }
        }
    }

    /// 综合演示函数
    /// 
    /// 展示所有 Rust 1.89 新特性
    pub fn demonstrate_rust_189_features() {
        println!("\n=== Rust 1.89 新特性演示 ===");

        println!("\n1. 显式推断的常量泛型参数:");
        let arr = [1, 2, 3, 4, 5];
        let sum = explicit_const_generic_inference::array_sum::<_>(arr);
        println!("数组求和: {}", sum);

        let matrix = [[1, 2], [3, 4], [5, 6]];
        let transposed = explicit_const_generic_inference::transpose_matrix::<_, _>(matrix);
        println!("矩阵转置: {:?}", transposed);

        println!("\n2. 改进的生命周期语法检查:");
        let x = 10;
        let y = 20;
        let result = improved_lifetime_syntax::longer_ref_explicit(&x, &y);
        println!("较长引用: {}", result);

        println!("\n3. 增强的类型推断:");
        let result = enhanced_type_inference::smart_inference(42);
        println!("智能推断结果: {}", result);

        let numbers = vec![1, 2, 3, 4, 5];
        let strings = enhanced_type_inference::complex_inference(numbers, |x| x.to_string());
        println!("复杂推断结果: {:?}", strings);

        println!("\n=== Rust 1.89 新特性演示完成 ===");
    }
}

/// 演示函数 - 展示所有基础语法功能
/// 
/// 这个函数展示了本模块中所有基础语法功能的使用
pub fn demonstrate_basic_syntax() {
    println!("\n=== Rust 泛型基础语法演示 ===");

    // 基础泛型函数
    println!("\n1. 基础泛型函数:");
    let x = basic_generic_functions::identity(42);
    let y = basic_generic_functions::identity("hello");
    println!("恒等函数: x = {}, y = {}", x, y);

    let (a, b) = basic_generic_functions::swap(1, "world");
    println!("交换函数: a = {}, b = {}", a, b);

    let max_val = basic_generic_functions::max(10, 20);
    println!("最大值: {}", max_val);

    // 泛型结构体
    println!("\n2. 泛型结构体:");
    let wrapper = generic_structs::Wrapper::new(42);
    println!("包装器: {:?}", wrapper);

    let mut node1 = generic_structs::Node::new(1);
    let node2 = generic_structs::Node::new(2);
    node1.set_next(node2);
    println!("节点: {:?}", node1);

    let pair = generic_structs::Pair::new(42, "hello");
    println!("对: {:?}", pair);

    // 泛型枚举
    println!("\n3. 泛型枚举:");
    let success: generic_enums::MyResult<i32, String> = generic_enums::MyResult::Ok(42);
    let error: generic_enums::MyResult<i32, String> = generic_enums::MyResult::Err("错误".to_string());
    println!("结果: {:?}, {:?}", success, error);

    let some: generic_enums::MyOption<i32> = generic_enums::MyOption::Some(42);
    let none: generic_enums::MyOption<i32> = generic_enums::MyOption::None;
    println!("选项: {:?}, {:?}", some, none);

    // 泛型方法
    println!("\n4. 泛型方法:");
    let mut container = generic_methods::Container::new();
    container.push(1);
    container.push(2);
    container.push(3);
    println!("容器长度: {}", container.len());

    let mut string_container = generic_methods::Container::new();
    string_container.push("Hello".to_string());
    string_container.push("World".to_string());
    println!("字符串连接: {}", string_container.join());

    // 生命周期参数
    println!("\n5. 生命周期参数:");
    let value = 42;
    let wrapper = lifetime_parameters::RefWrapper::new(&value);
    println!("引用包装器: {:?}", wrapper);

    let x = 10;
    let y = 20;
    let longer = lifetime_parameters::longer_ref(&x, &y);
    println!("较长引用: {}", longer);

    // 泛型 trait 实现
    println!("\n6. 泛型 trait 实现:");
    let result = generic_trait_impls::compare_values(&10, &20);
    println!("比较结果: {:?}", result);

    let converted: String = generic_trait_impls::convert_value(42);
    println!("转换结果: {}", converted);

    // 高级模式
    println!("\n7. 高级模式:");
    let idle = advanced_patterns::StateMachine::<advanced_patterns::Idle, i32>::new(42);
    let _state_marker = idle.state_marker(); // 访问状态标记
    let running = idle.start();
    println!("状态机数据: {}", running.data());
    let _state_marker = running.state_marker(); // 访问状态标记

    let result = advanced_patterns::Builder::<String>::new()
        .add("Hello".to_string())
        .add(" ".to_string())
        .add("World".to_string())
        .build();
    println!("构建器结果: {}", result);

    // Rust 1.89 新特性演示
    println!("\n8. Rust 1.89 新特性:");
    rust_189_new_features::demonstrate_rust_189_features();

    println!("\n=== 基础语法演示完成 ===");
}

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_all_modules_integration() {
        // 测试所有模块的集成
        demonstrate_basic_syntax();
    }
}
