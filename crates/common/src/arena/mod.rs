//! # Arena 分配器概念模块
//!
//! 提供基于 arena 的内存管理概念实现。
//!
//! Arena 分配器是一种高效的批量内存管理策略：
//! - 一次性分配大块内存
//! - 从中分配小对象
//! - 最后一次性释放整个 arena
//!
//! ## 核心优势
//!
//! - **O(1) 分配**: 只需递增指针
//! - **无碎片**: 连续内存布局
//! - **批量释放**: 无需逐个析构
//!
//! ## 典型用例
//!
//! - 编译器 AST 节点分配
//! - 游戏帧临时对象
//! - 解析器中间表示
//!
//! ## 安全限制
//!
//! 由于 `#[forbid(unsafe_code)]`，本模块使用 `Vec` + 索引模拟 arena 语义，
//! 不实现真正的指针 bump allocator。

use std::marker::PhantomData;

/// Arena 中的对象句柄（索引）
///
/// 使用索引而非指针，避免悬垂引用问题。
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Handle<T> {
    index: usize,
    _marker: PhantomData<T>,
}

// 手动实现 Clone 和 Copy，不依赖 T 的 trait bounds
impl<T> Clone for Handle<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Handle<T> {}

impl<T> Handle<T> {
    /// 创建新句柄
    pub const fn new(index: usize) -> Self {
        Self {
            index,
            _marker: PhantomData,
        }
    }

    /// 获取内部索引
    pub const fn index(self) -> usize {
        self.index
    }
}

/// 类型安全的 Arena 分配器
///
/// 使用 `Vec<T>` 作为底层存储，通过 `Handle<T>` 访问元素。
/// 所有对象在 Arena 销毁时一并释放。
#[derive(Debug)]
pub struct Arena<T> {
    storage: Vec<T>,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Arena<T> {
    /// 创建空的 Arena
    pub fn new() -> Self {
        Self {
            storage: Vec::new(),
        }
    }

    /// 创建具有指定容量的 Arena
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            storage: Vec::with_capacity(capacity),
        }
    }

    /// 在 Arena 中分配一个对象，返回句柄
    pub fn alloc(&mut self, value: T) -> Handle<T> {
        let index = self.storage.len();
        self.storage.push(value);
        Handle::new(index)
    }

    /// 通过句柄获取引用
    pub fn get(&self, handle: Handle<T>) -> Option<&T> {
        self.storage.get(handle.index)
    }

    /// 通过句柄获取可变引用
    pub fn get_mut(&mut self, handle: Handle<T>) -> Option<&mut T> {
        self.storage.get_mut(handle.index)
    }

    /// 获取 Arena 中对象数量
    pub fn len(&self) -> usize {
        self.storage.len()
    }

    /// 检查 Arena 是否为空
    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    /// 清空 Arena（释放所有对象）
    pub fn clear(&mut self) {
        self.storage.clear();
    }

    /// 遍历所有元素
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.storage.iter()
    }

    /// 遍历所有元素（可变）
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.storage.iter_mut()
    }

    /// 获取 Arena 统计信息
    pub fn stats(&self) -> ArenaStats {
        ArenaStats {
            allocations: self.storage.len(),
            capacity: self.storage.capacity(),
        }
    }
}

/// Arena 使用统计
#[derive(Debug, Clone, Copy, Default)]
pub struct ArenaStats {
    pub allocations: usize,
    pub capacity: usize,
}

/// 支持嵌套 Arena 的类型
///
/// 允许在 Arena 中存储对其他 Arena 元素的引用（通过句柄）
pub trait ArenaAllocated {
    type HandleType;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_alloc_and_get() {
        let mut arena = Arena::new();
        let h1 = arena.alloc("hello");
        let h2 = arena.alloc("world");

        assert_eq!(arena.get(h1), Some(&"hello"));
        assert_eq!(arena.get(h2), Some(&"world"));
        assert_eq!(arena.len(), 2);
    }

    #[test]
    fn test_arena_get_mut() {
        let mut arena = Arena::new();
        let h = arena.alloc(42);

        *arena.get_mut(h).unwrap() = 100;
        assert_eq!(arena.get(h), Some(&100));
    }

    #[test]
    fn test_arena_clear() {
        let mut arena = Arena::new();
        arena.alloc(1);
        arena.alloc(2);
        arena.clear();

        assert!(arena.is_empty());
    }

    #[test]
    fn test_arena_with_capacity() {
        let mut arena = Arena::with_capacity(100);
        for i in 0..50 {
            arena.alloc(i);
        }

        let stats = arena.stats();
        assert_eq!(stats.allocations, 50);
        assert!(stats.capacity >= 100);
    }

    #[test]
    fn test_handle_equality() {
        let h1: Handle<i32> = Handle::new(5);
        let h2: Handle<i32> = Handle::new(5);
        let h3: Handle<i32> = Handle::new(10);

        assert_eq!(h1, h2);
        assert_ne!(h1, h3);
    }

    #[test]
    fn test_arena_iteration() {
        let mut arena = Arena::new();
        arena.alloc(10);
        arena.alloc(20);
        arena.alloc(30);

        let sum: i32 = arena.iter().copied().sum();
        assert_eq!(sum, 60);
    }

    #[test]
    fn test_arena_complex_type() {
        #[derive(Debug, PartialEq)]
        struct Node {
            value: String,
            children: Vec<Handle<Node>>,
        }

        let mut arena: Arena<Node> = Arena::new();

        let child1 = arena.alloc(Node {
            value: "child1".to_string(),
            children: vec![],
        });

        let _root = arena.alloc(Node {
            value: "root".to_string(),
            children: vec![child1],
        });

        assert_eq!(arena.get(_root).unwrap().value, "root");
        assert_eq!(
            arena
                .get(arena.get(_root).unwrap().children[0])
                .unwrap()
                .value,
            "child1"
        );
    }
}
