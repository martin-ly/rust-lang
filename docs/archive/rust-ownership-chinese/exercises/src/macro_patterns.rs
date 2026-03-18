//! 宏与所有权
//!
//! 过程宏和声明宏对所有权的影响

// ============================================
// 声明宏模式
// ============================================

/// 所有权感知的vec!变体
#[macro_export]
macro_rules! owning_vec {
    // 移动所有元素
    ($($x:expr),* $(,)?) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}

/// 延迟求值宏
#[macro_export]
macro_rules! lazy_eval {
    ($e:expr) => {
        || $e
    };
}

/// 作用域守卫宏
#[macro_export]
macro_rules! scope_guard {
    ($cleanup:expr) => {
        struct _Guard;
        impl Drop for _Guard {
            fn drop(&mut self) {
                $cleanup
            }
        }
        let _guard = _Guard;
    };
}

/// defer宏（Go风格）
#[macro_export]
macro_rules! defer {
    ($($body:tt)*) => {
        let _deferred = $crate::macro_patterns::Defer::new(|| { $($body)* });
    };
}

pub struct Defer<F: FnOnce()> {
    f: Option<F>,
}

impl<F: FnOnce()> Defer<F> {
    pub fn new(f: F) -> Self {
        Self { f: Some(f) }
    }
}

impl<F: FnOnce()> Drop for Defer<F> {
    fn drop(&mut self) {
        if let Some(f) = self.f.take() {
            f();
        }
    }
}

// ============================================
// 类型级宏模式
// ============================================

/// 复制性检查宏
#[macro_export]
macro_rules! assert_copy {
    ($t:ty) => {
        const _: () = {
            trait CopyCheck {
                fn check()
                where
                    Self: Copy;
                
                fn _ensure_compiles()
                where
                    Self: Copy,
                {
                    Self::check()
                }
            }
            
            impl CopyCheck for $t {
                fn check() {}
            }
        };
    };
}

/// 所有权语义宏
#[macro_export]
macro_rules! ownership_semantics {
    (move $v:ident) => {
        {
            let _ = $v; // 消费所有权
        }
    };
    (borrow $v:ident) => {
        {
            let _ = &$v; // 借用
        }
    };
    (mut_borrow $v:ident) => {
        {
            let _ = &mut $v; // 可变借用
        }
    };
}

// ============================================
// 派生宏助手
// ============================================

/// 手动实现Clone（教育用途）
#[macro_export]
macro_rules! manual_clone {
    ($struct_name:ident { $($field:ident),* }) => {
        impl Clone for $struct_name {
            fn clone(&self) -> Self {
                Self {
                    $($field: self.$field.clone()),*
                }
            }
        }
    };
}

/// 所有权转移调试
#[macro_export]
macro_rules! trace_move {
    ($e:expr) => {{
        let result = $e;
        #[cfg(debug_assertions)]
        eprintln!("[TRACE] Value moved at {}:{}", file!(), line!());
        result
    }};
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_owning_vec() {
        let v = owning_vec![1, 2, 3];
        assert_eq!(v, vec![1, 2, 3]);
        
        let s = "hello".to_string();
        let v = owning_vec![s]; // s被移动
        assert_eq!(v[0], "hello");
    }
    
    #[test]
    fn test_defer() {
        use std::cell::Cell;
        let x = Cell::new(0);
        {
            let x_ref = &x;
            defer! { x_ref.set(42); }
            assert_eq!(x.get(), 0);
        }
        assert_eq!(x.get(), 42);
    }
    
    #[test]
    fn test_lazy_eval() {
        let f = lazy_eval!(42);
        assert_eq!(f(), 42);
    }
    
    #[derive(Clone)]
    struct TestStruct {
        a: i32,
        b: String,
    }
    
    #[test]
    fn test_manual_clone() {
        let s = TestStruct { a: 1, b: "test".to_string() };
        let cloned = s.clone();
        assert_eq!(s.a, cloned.a);
    }
}
