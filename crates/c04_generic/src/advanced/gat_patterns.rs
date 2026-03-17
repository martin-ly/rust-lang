//! C04 - 高级泛型模式
//! 
//! 本模块演示 GAT、类型族、HList 等高级泛型特性

/// 泛型关联类型演示
#[allow(dead_code)]
pub trait LendingIterator {
    type Item<'a>
    where
        Self: 'a;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

/// 窗口迭代器 (GAT 典型用例)
pub struct WindowIter<'a, T> {
    #[allow(dead_code)]
    slice: &'a [T],
    #[allow(dead_code)]
    window_size: usize,
}

impl<'a, T> WindowIter<'a, T> {
    pub fn new(slice: &'a [T], window_size: usize) -> Self {
        Self { slice, window_size }
    }
}

impl<'a, T> LendingIterator for WindowIter<'a, T> {
    type Item<'b> = &'b [T]
    where
        Self: 'b;
    
    fn next<'b>(&'b mut self) -> Option<Self::Item<'b>> {
        if self.slice.len() >= self.window_size {
            let window = &self.slice[..self.window_size];
            self.slice = &self.slice[1..];
            Some(window)
        } else {
            None
        }
    }
}

/// HList - 异构列表
#[derive(Debug)]
pub struct HNil;

/// HList cons 单元
#[derive(Debug)]
pub struct HCons<H, T> {
    /// 头部元素
    pub head: H,
    /// 尾部列表
    pub tail: T,
}

/// HList trait - 标记 trait 用于类型约束
#[allow(dead_code)]
pub trait HList {}
impl HList for HNil {}
impl<H, T: HList> HList for HCons<H, T> {}

/// HList 长度计算
pub trait HListLength {
    const LEN: usize;
}

impl HListLength for HNil {
    const LEN: usize = 0;
}

impl<H, T: HListLength> HListLength for HCons<H, T> {
    const LEN: usize = 1 + T::LEN;
}

/// 获取 HList 长度
pub const fn hlist_len<H, T>() -> usize
where
    HCons<H, T>: HListLength,
{
    HCons::<H, T>::LEN
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_window_iter() {
        let data = vec![1, 2, 3, 4, 5];
        let mut iter = WindowIter::new(&data, 3);
        
        assert_eq!(iter.next(), Some(&[1, 2, 3][..]));
        assert_eq!(iter.next(), Some(&[2, 3, 4][..]));
        assert_eq!(iter.next(), Some(&[3, 4, 5][..]));
        assert_eq!(iter.next(), None);
    }
    
    #[test]
    fn test_hlist_length() {
        let _list = HCons {
            head: 1,
            tail: HCons {
                head: "hello",
                tail: HNil,
            },
        };
        
        assert_eq!(<HCons<i32, HCons<&str, HNil>> as HListLength>::LEN, 2);
    }
}
