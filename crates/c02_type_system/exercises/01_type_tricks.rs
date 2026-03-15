//! C02 类型系统练习
//! 
//! 运行: cargo test --package c02_type_system -- exercises::type_tricks

#[cfg(test)]
mod tests {
    /// 练习 1: 实现一个类型，它可以是整数或字符串
    #[derive(Debug, PartialEq)]
    enum IntOrString {
        Int(i32),
        String(String),
    }

    #[test]
    fn test_enum_variants() {
        let int_val = IntOrString::Int(42);
        let str_val = IntOrString::String(String::from("hello"));
        
        assert!(matches!(int_val, IntOrString::Int(42)));
        assert!(matches!(str_val, IntOrString::String(_)));
    }

    /// 练习 2: 实现一个泛型函数，返回类型的默认值
    fn default_value<T: Default>() -> T {
        T::default()
    }

    #[test]
    fn test_default_value() {
        assert_eq!(default_value::<i32>(), 0);
        assert_eq!(default_value::<bool>(), false);
        assert_eq!(default_value::<String>(), "");
    }

    /// 练习 3: 使用类型别名简化复杂类型
    type ResultMap<K, V> = Result<std::collections::HashMap<K, V>, String>;

    fn create_map<K: std::hash::Hash + Eq, V>() -> ResultMap<K, V> {
        Ok(std::collections::HashMap::new())
    }

    #[test]
    fn test_type_alias() {
        let map: ResultMap<String, i32> = create_map();
        assert!(map.is_ok());
    }

    /// 练习 4: Newtype 模式
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct UserId(u64);
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct ProductId(u64);

    fn find_user(_id: UserId) -> Option<String> {
        Some(String::from("Alice"))
    }

    fn find_product(_id: ProductId) -> Option<String> {
        Some(String::from("Laptop"))
    }

    #[test]
    fn test_newtype_pattern() {
        let user_id = UserId(1);
        let product_id = ProductId(1);
        
        // 类型系统阻止了以下错误：
        // find_product(user_id); // 编译错误！
        
        assert_eq!(find_user(user_id), Some(String::from("Alice")));
        assert_eq!(find_product(product_id), Some(String::from("Laptop")));
    }
}
