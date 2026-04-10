//! Miri 测试模块 - 算法内存安全验证

use std::mem::MaybeUninit;
use std::ptr;

// ==================== 排序算法 ====================

/// 测试 1: 快速排序内存安全
#[test]
fn test_quicksort_safety() {
    fn quicksort<T: Ord>(arr: &mut [T]) {
        if arr.len() <= 1 { return; }
        let pivot_index = partition(arr);
        quicksort(&mut arr[..pivot_index]);
        quicksort(&mut arr[pivot_index + 1..]);
    }
    
    fn partition<T: Ord>(arr: &mut [T]) -> usize {
        let len = arr.len();
        let pivot_index = len / 2;
        arr.swap(pivot_index, len - 1);
        let mut store_index = 0;
        for i in 0..len - 1 {
            if arr[i] < arr[len - 1] {
                arr.swap(i, store_index);
                store_index += 1;
            }
        }
        arr.swap(store_index, len - 1);
        store_index
    }
    
    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
    quicksort(&mut data);
    assert_eq!(data, vec![1, 1, 2, 3, 4, 5, 6, 9]);
}

// ==================== 链表 ====================

struct ListNode<T> {
    data: T,
    next: Option<Box<ListNode<T>>>,
}

struct LinkedList<T> {
    head: Option<Box<ListNode<T>>>,
}

impl<T> LinkedList<T> {
    fn new() -> Self { Self { head: None } }
    
    fn push_front(&mut self, data: T) {
        self.head = Some(Box::new(ListNode {
            data,
            next: self.head.take(),
        }));
    }
    
    fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.data
        })
    }
}

/// 测试 2: 链表内存安全
#[test]
fn test_linked_list_safety() {
    let mut list = LinkedList::new();
    list.push_front(1);
    list.push_front(2);
    list.push_front(3);
    assert_eq!(list.pop_front(), Some(3));
    assert_eq!(list.pop_front(), Some(2));
    assert_eq!(list.pop_front(), Some(1));
}

// ==================== 二叉树 ====================

struct TreeNode<T> {
    data: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

struct BinarySearchTree<T: Ord> {
    root: Option<Box<TreeNode<T>>>,
}

impl<T: Ord> BinarySearchTree<T> {
    fn new() -> Self { Self { root: None } }
    
    fn insert(&mut self, data: T) {
        match self.root {
            None => {
                self.root = Some(Box::new(TreeNode {
                    data, left: None, right: None,
                }));
            }
            Some(ref mut node) => Self::insert_node(node, data),
        }
    }
    
    fn insert_node(node: &mut Box<TreeNode<T>>, data: T) {
        if data < node.data {
            match node.left {
                None => node.left = Some(Box::new(TreeNode {
                    data, left: None, right: None,
                })),
                Some(ref mut left) => Self::insert_node(left, data),
            }
        } else {
            match node.right {
                None => node.right = Some(Box::new(TreeNode {
                    data, left: None, right: None,
                })),
                Some(ref mut right) => Self::insert_node(right, data),
            }
        }
    }
}

/// 测试 3: 二叉搜索树内存安全
#[test]
fn test_bst_safety() {
    let mut tree = BinarySearchTree::new();
    tree.insert(5);
    tree.insert(3);
    tree.insert(7);
    assert!(tree.root.is_some());
}

// ==================== 栈和队列 ====================

struct Stack<T> {
    data: Vec<T>,
}

impl<T> Stack<T> {
    fn new() -> Self { Self { data: Vec::new() } }
    fn push(&mut self, item: T) { self.data.push(item); }
    fn pop(&mut self) -> Option<T> { self.data.pop() }
}

/// 测试 4: 栈内存安全
#[test]
fn test_stack_safety() {
    let mut stack = Stack::new();
    stack.push(1);
    stack.push(2);
    assert_eq!(stack.pop(), Some(2));
    assert_eq!(stack.pop(), Some(1));
}

// ==================== 不安全数组操作 ====================

/// 测试 5: 安全的原地数组反转
#[test]
fn test_inplace_reverse() {
    fn reverse<T>(arr: &mut [T]) {
        let len = arr.len();
        for i in 0..len / 2 {
            arr.swap(i, len - 1 - i);
        }
    }
    
    let mut data = [1, 2, 3, 4, 5];
    reverse(&mut data);
    assert_eq!(data, [5, 4, 3, 2, 1]);
}

/// 测试 6: MaybeUninit 数组处理
#[test]
fn test_maybeuninit_array() {
    let mut arr: [MaybeUninit<i32>; 5] = unsafe {
        MaybeUninit::uninit().assume_init()
    };
    
    for i in 0..5 {
        arr[i].write((i * 10) as i32);
    }
    
    unsafe {
        for i in 0..5 {
            assert_eq!(arr[i].assume_init_read(), (i * 10) as i32);
        }
    }
    
    std::mem::forget(arr);
}
