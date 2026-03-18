//! 宏卫生（Macro Hygiene）
//!
//! Rust宏卫生的概念和最佳实践。

/// 宏卫生示例：变量不会泄漏到外部作用域
#[macro_export]
macro_rules! hygienic_let {
    ($name:ident = $value:expr) => {
        let $name = $value;
    };
}

/// 非卫生宏的问题示例（对比）
/// 在C/C++的宏中，这种情况会导致问题
#[macro_export]
macro_rules! problematic_in_other_languages {
    // 在Rust中这是安全的，因为宏有自己的作用域
    () => {
        let x = 42; // 这个x不会泄漏
    };
}

/// 使用$crate确保卫生
#[macro_export]
macro_rules! use_crate_path {
    () => {
        // $crate确保宏使用的是定义它的crate中的项
        use $crate::some_internal_fn;
    };
}

/// 内部函数，通过$crate暴露
pub fn some_internal_fn() {
    println!("Internal function called");
}

/// 避免名称冲突的模式
#[macro_export]
macro_rules! with_unique_ident {
    ($name:ident, $body:tt) => {
        // 使用paste crate生成唯一标识符
        paste::paste! {
            $body
        }
    };
}

/// 宏中的生命周期卫生
#[macro_export]
macro_rules! make_wrapper {
    ($name:ident) => {
        pub struct $name<'a, T: 'a> {
            inner: &'a T,
        }
        
        impl<'a, T> $name<'a, T> {
            pub fn new(inner: &'a T) -> Self {
                Self { inner }
            }
            
            pub fn get(&self) -> &'a T {
                self.inner
            }
        }
    };
}

/// 宏卫生测试示例
#[cfg(test)]
mod hygiene_tests {
    /// 测试变量不泄漏
    #[test]
    fn test_variable_hygiene() {
        hygienic_let!(x = 42);
        assert_eq!(x, 42);
        
        // 再次使用相同的宏不会冲突
        hygienic_let!(x = 100);
        assert_eq!(x, 100);
    }
    
    /// 测试生命周期卫生
    #[test]
    fn test_lifetime_hygiene() {
        make_wrapper!(MyWrapper);
        
        let value = 42;
        let wrapper = MyWrapper::new(&value);
        assert_eq!(*wrapper.get(), 42);
    }
}

/// 宏卫生最佳实践总结
pub mod best_practices {
    /// 1. 始终使用$crate引用当前crate的项
    pub fn use_crate_path() {}
    
    /// 2. 避免在宏中创建可能冲突的变量名
    pub fn avoid_common_names() {}
    
    /// 3. 使用局部作用域限制变量生命周期
    pub fn use_local_scope() {}
    
    /// 4. 文档化宏创建的所有标识符
    pub fn document_identifiers() {}
}
