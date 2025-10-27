//! 高级声明宏模式

/// 创建字符串向量
///
/// # 示例
///
/// ```
/// # use c11_macro_system::vec_of_strings;
/// let strings = vec_of_strings!["hello", "world"];
/// assert_eq!(strings, vec!["hello".to_string(), "world".to_string()]);
/// ```
#[macro_export]
macro_rules! vec_of_strings {
    ($($x:expr),* $(,)?) => {
        vec![$($x.to_string()),*]
    };
}

/// HashMap创建宏
///
/// # 示例
///
/// ```
/// # use c11_macro_system::hashmap;
/// # use std::collections::HashMap;
/// let map = hashmap! {
///     "key1" => "value1",
///     "key2" => "value2",
/// };
/// ```
#[macro_export]
macro_rules! hashmap {
    ($($key:expr => $val:expr),* $(,)?) => {
        {
            let mut map = ::std::collections::HashMap::new();
            $(
                map.insert($key, $val);
            )*
            map
        }
    };
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    #[test]
    fn test_vec_of_strings() {
        let result = vec_of_strings!["a", "b", "c"];
        assert_eq!(result, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_hashmap() {
        let map: HashMap<&str, i32> = hashmap! {
            "one" => 1,
            "two" => 2,
        };
        assert_eq!(map.get("one"), Some(&1));
        assert_eq!(map.get("two"), Some(&2));
    }
}

