//! 实用声明宏集合
//! 
//! 提供常见的实用宏模式

/// 实现 getter 和 setter 方法
///
/// # 示例
///
/// ```
/// # use c11_macro_system::impl_getter_setter;
/// struct Person {
///     name: String,
///     age: u32,
/// }
/// 
/// impl Person {
///     impl_getter_setter! { name: String }
///     impl_getter_setter! { age: u32 }
/// }
/// ```
#[macro_export]
macro_rules! impl_getter_setter {
    ($field:ident: $type:ty) => {
        pub fn $field(&self) -> &$type {
            &self.$field
        }
        
        paste::paste! {
            pub fn [<set_ $field>](&mut self, value: $type) {
                self.$field = value;
            }
        }
    };
}

/// 创建测试模块
///
/// # 示例
///
/// ```
/// # use c11_macro_system::test_module;
/// test_module! {
///     test_add: {
///         assert_eq!(1 + 1, 2);
///     }
///     test_sub: {
///         assert_eq!(2 - 1, 1);
///     }
/// }
/// ```
#[macro_export]
macro_rules! test_module {
    ($($name:ident: $body:block)+) => {
        #[cfg(test)]
        mod tests {
            use super::*;
            $(
                #[test]
                fn $name() {
                    $body
                }
            )+
        }
    };
}

/// 实现 From 转换
///
/// # 示例
///
/// ```
/// # use c11_macro_system::impl_from;
/// struct Wrapper<T>(T);
/// 
/// impl_from! { String => Wrapper<String> }
/// ```
#[macro_export]
macro_rules! impl_from {
    ($from:ty => $to:ty) => {
        impl From<$from> for $to {
            fn from(value: $from) -> Self {
                Self(value)
            }
        }
    };
}

/// 实现 Display trait
///
/// # 示例
///
/// ```ignore
/// use c11_macro_system::impl_display;
/// struct Point { x: i32, y: i32 }
/// 
/// impl_display! { Point, "Point({}, {})", x, y }
/// ```
#[macro_export]
macro_rules! impl_display {
    ($type:ty, $fmt:literal $(, $field:ident)+) => {
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, $fmt $(, self.$field)+)
            }
        }
    };
}

/// 创建 vec 的简写宏
///
/// # 示例
///
/// ```
/// # use c11_macro_system::vec_of;
/// let v = vec_of![1, 2, 3];
/// ```
#[macro_export]
macro_rules! vec_of {
    ($($item:expr),*) => {
        vec![$($item),*]
    };
}

/// 实现 Deref 和 DerefMut
///
/// # 示例
///
/// ```ignore
/// use c11_macro_system::impl_deref;
/// struct MyVec<T>(Vec<T>);
/// 
/// impl_deref! { MyVec<T> => Vec<T> }
/// ```
#[macro_export]
macro_rules! impl_deref {
    ($type:ty => $target:ty) => {
        impl std::ops::Deref for $type {
            type Target = $target;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }
        
        impl std::ops::DerefMut for $type {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    
    struct TestWrapper(String);
    impl_from! { String => TestWrapper }
    
    #[test]
    fn test_impl_from() {
        let s = String::from("hello");
        let w: TestWrapper = s.into();
        assert_eq!(w.0, "hello");
    }
    
    #[test]
    fn test_vec_of() {
        let v = vec_of![1, 2, 3];
        assert_eq!(v, vec![1, 2, 3]);
    }
}
