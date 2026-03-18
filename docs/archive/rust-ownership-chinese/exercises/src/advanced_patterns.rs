//! 高级所有权模式
//! 
//! 本模块展示Rust所有权系统的高级用法

use std::pin::Pin;
use std::marker::PhantomPinned;

/// 复杂生命周期模式 - 多个生命周期参数
///
/// 'a 和 'b 可能有不同的生命周期
/// 返回的生命周期 'a 与输入 s1 绑定
/// 
/// # 形式语义
/// ∀ 'a, 'b. s1: &'a str, s2: &'b str, flag: bool ⊢ select_string(s1, s2, flag): &'a str
pub fn select_string<'a>(s1: &'a str, s2: &'a str, flag: bool) -> &'a str {
    if flag { s1 } else { s2 }
}

/// 生命周期省略的局限性
/// 
/// 以下函数无法使用生命周期省略规则，需要显式标注
pub fn longest_with_suffix<'a>(s1: &'a str, s2: &'a str, suffix: &str) -> &'a str {
    let s = if s1.len() > s2.len() { s1 } else { s2 };
    println!("Suffix: {}", suffix);
    s
}

/// 泛型生命周期约束
pub struct Parser<'a, 'b: 'a> {
    input: &'a str,
    delimiter: &'b str,
}

impl<'a, 'b: 'a> Parser<'a, 'b> {
    pub fn new(input: &'a str, delimiter: &'b str) -> Self {
        Self { input, delimiter }
    }
    
    pub fn parse(&self) -> Vec<&'a str> {
        self.input.split(self.delimiter).collect()
    }
}

// ============================================
// 自引用结构模式
// ============================================

/// 使用Pin的自引用结构
/// 
/// 这是安全的自引用实现方式
pub struct SelfReferential {
    data: String,
    ptr: *const str,
    _pin: PhantomPinned,
}

impl SelfReferential {
    pub fn new(data: String) -> Pin<Box<Self>> {
        // 先分配空间，避免移动
        let mut boxed = Box::new(Self {
            data,
            ptr: std::ptr::slice_from_raw_parts(std::ptr::null::<u8>(), 0) as *const str,
            _pin: PhantomPinned,
        });
        
        // 设置自引用
        let ptr: *const str = &boxed.data[..];
        boxed.ptr = ptr;
        
        // 现在可以Pin
        Pin::from(boxed)
    }
    
    pub fn get_data(&self) -> &str {
        &self.data
    }
    
    /// # Safety
    /// 必须在Pin的保护下调用
    pub fn get_ref(self: Pin<&Self>) -> &str {
        unsafe { &*self.ptr }
    }
}

// ouroboros示例 (条件编译)
#[cfg(feature = "ouroboros")]
pub mod self_ref_crate {
    use ouroboros::self_referencing;
    
    #[self_referencing]
    pub struct SelfRefParser {
        data: String,
        #[borrows(data)]
        slice: &'this str,
    }
}

// ============================================
// 零成本抽象模式
// ============================================

/// 迭代器链的零成本抽象
pub fn zero_cost_iterator_chain(data: &[i32]) -> i32 {
    data
        .iter()
        .filter(|&&x| x % 2 == 0)
        .map(|x| x * x)
        .take(10)
        .sum()
}

/// 泛型单态化示例
pub fn generic_monomorphization() {
    fn process<T: AsRef<[u8]>>(data: T) -> usize {
        data.as_ref().len()
    }
    
    let _ = process(vec![1u8, 2, 3]);
    let _ = process(&[1u8, 2, 3]);
    let _ = process("hello");
}

/// const泛型的零成本抽象
pub struct Array<T, const N: usize> {
    data: [T; N],
}

impl<T: Default + Copy, const N: usize> Array<T, N> {
    pub fn new() -> Self {
        Self { data: [T::default(); N] }
    }
    
    pub fn len(&self) -> usize { N }
    
    pub fn is_empty(&self) -> bool { N == 0 }
}

// ============================================
// 内存布局优化模式
// ============================================

/// 使用Box减少栈空间占用
pub enum RecursiveTree<T> {
    Leaf(T),
    Node(Box<RecursiveTree<T>>, T, Box<RecursiveTree<T>>),
}

/// 使用NonNull优化Option<Box<T>>
use std::ptr::NonNull;

pub struct CompactList<T> {
    head: Option<NonNull<Node<T>>>,
}

struct Node<T> {
    data: T,
    next: Option<NonNull<Node<T>>>,
}

// ============================================
// 类型状态模式
// ============================================

/// 未验证状态
pub struct Unverified;
/// 已验证状态  
pub struct Verified;

/// 类型状态模式：编译时状态机
pub struct Request<State> {
    url: String,
    _state: std::marker::PhantomData<State>,
}

impl Request<Unverified> {
    pub fn new(url: String) -> Self {
        Self { url, _state: std::marker::PhantomData }
    }
    
    pub fn verify(self) -> Result<Request<Verified>, String> {
        if self.url.starts_with("https://") {
            Ok(Request { 
                url: self.url, 
                _state: std::marker::PhantomData 
            })
        } else {
            Err("URL must use HTTPS".to_string())
        }
    }
}

impl Request<Verified> {
    pub fn send(&self) -> String {
        format!("Sending request to {}", self.url)
    }
}

// ============================================
// 子类型与变型
// ============================================

/// 协变示例
pub struct Covariant<'a> {
    data: &'a str,
}

/// 不变示例
pub struct Invariant<'a> {
    data: std::cell::Cell<&'a str>,
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_select_string() {
        let s1 = "hello";
        let s2 = "world";
        assert_eq!(select_string(s1, s2, true), "hello");
        assert_eq!(select_string(s1, s2, false), "world");
    }
    
    #[test]
    fn test_parser() {
        let parser = Parser::new("a,b,c", ",");
        assert_eq!(parser.parse(), vec!["a", "b", "c"]);
    }
    
    #[test]
    fn test_iterator_chain() {
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        assert_eq!(zero_cost_iterator_chain(&data), 220); // 4+16+36+64+100=220
    }
    
    #[test]
    fn test_typestate() {
        let req = Request::<Unverified>::new("https://example.com".to_string());
        let verified = req.verify().unwrap();
        assert_eq!(verified.send(), "Sending request to https://example.com");
    }
}
