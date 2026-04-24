//! # 练习 2: 关联类型
//!
//! **难度**: Medium  
//! **考点**: associated type、Iterator trait 模式
//!
//! ## 题目描述
//!
//! 定义一个 Container 特质，使用关联类型表示元素类型，
//! 为 Vec 和自定义结构体实现该特质。

/// 容器特质
pub trait Container {
    /// 容器中元素的类型
    type Item;

    /// 添加元素
    fn add(&mut self, item: Self::Item);

    /// 返回元素数量
    fn len(&self) -> usize;

    /// 判断是否为空
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Container for Vec<T> {
    type Item = T;

    fn add(&mut self, item: Self::Item) {
        self.push(item);
    }

    fn len(&self) -> usize {
        self.len()
    }
}

/// 固定容量的栈
#[derive(Debug)]
pub struct FixedStack<T, const N: usize> {
    data: [Option<T>; N],
    top: usize,
}

impl<T: Default + Copy, const N: usize> FixedStack<T, N> {
    pub fn new() -> Self {
        Self {
            data: [Default::default(); N],
            top: 0,
        }
    }
}

impl<T: Default + Copy, const N: usize> Container for FixedStack<T, N> {
    type Item = T;

    fn add(&mut self, item: Self::Item) {
        if self.top < N {
            self.data[self.top] = Some(item);
            self.top += 1;
        }
    }

    fn len(&self) -> usize {
        self.top
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec_container() {
        let mut v: Vec<i32> = Vec::new();
        <Vec<i32> as Container>::add(&mut v, 10);
        v.add(20);
        assert_eq!(v.len(), 2);
        assert!(!v.is_empty());
    }

    #[test]
    fn test_fixed_stack() {
        let mut stack: FixedStack<i32, 3> = FixedStack::new();
        assert!(stack.is_empty());
        stack.add(1);
        stack.add(2);
        assert_eq!(stack.len(), 2);
    }
}
