//! Aeneas 验证友好示例。
//!
//! Aeneas 目前主要支持安全的纯函数子集。本文件提供递归求和与有序链表插入，
//! 避免 `unsafe`、复杂 trait 和循环，以便 Aeneas 进行翻译和证明。
#![allow(dead_code)]

/// 递归整数链表。
pub enum List {
    /// 空节点。
    Nil,
    /// 头元素与尾部链表。
    Cons(i32, Box<List>),
}

/// 递归求和。
///
/// 使用不可变借用，符合 Aeneas 对纯函数的偏好。
pub fn sum(list: &List) -> i32 {
    match list {
        List::Nil => 0,
        List::Cons(head, tail) => head + sum(tail),
    }
}

/// 在有序链表中插入元素，返回新链表。
///
/// 该实现保持原有节点不变，通过 `Box` 构造新结构，属于 Aeneas 可处理的
/// 纯函数式风格。
pub fn insert(list: List, value: i32) -> List {
    match list {
        List::Nil => List::Cons(value, Box::new(List::Nil)),
        List::Cons(head, tail) => {
            if value <= head {
                List::Cons(value, Box::new(List::Cons(head, tail)))
            } else {
                List::Cons(head, Box::new(insert(*tail, value)))
            }
        }
    }
}

fn main() {
    let list = List::Cons(1, Box::new(List::Cons(3, Box::new(List::Nil))));
    assert_eq!(sum(&list), 4);

    let inserted = insert(list, 2);
    assert_eq!(sum(&inserted), 6);

    println!("Aeneas example compiled successfully (run Aeneas separately for verification).");
}
