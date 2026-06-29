//! 跳表（Skip List）：基于概率分层的链表结构，提供与平衡树相近的期望性能。
//!
//! 跳表通过为每个节点随机分配层数（level）来构建“快速通道”，
//! 使得搜索、插入、删除的期望时间复杂度均为 O(log n)。
//!
//! 本实现使用索引竞技场（arena）来避免复杂的裸指针/借用链操作，
//! 既保证安全性，又保留跳表的核心教学意义。
//!
//! # 时间复杂度（期望）
//! - 查找: O(log n)
//! - 插入: O(log n)
//! - 删除: O(log n)
//! - 范围查询: O(log n + k)，k 为结果数量
//! - 空间: O(n)

use rand::RngExt;

const DEFAULT_MAX_LEVEL: usize = 16;
const DEFAULT_P: f64 = 0.5;

/// 特殊索引，表示“无”。
const NIL: usize = usize::MAX;

/// 跳表节点。value 按升序排列，允许重复值。
#[derive(Clone, Debug)]
struct Node<T: Clone + Ord> {
    value: T,
    /// forward[i] 表示第 i 层的下一个节点索引，NIL 表示无。
    forward: Vec<usize>,
}

impl<T: Clone + Ord> Node<T> {
    fn new(value: T, level: usize) -> Self {
        Self {
            value,
            forward: vec![NIL; level],
        }
    }
}

/// 跳表。
#[derive(Clone, Debug)]
pub struct SkipList<T: Clone + Ord> {
    nodes: Vec<Node<T>>,
    /// 头节点索引固定为 0。
    level: usize,
    len: usize,
    max_level: usize,
    probability: f64,
}

impl<T: Clone + Ord + Default> Default for SkipList<T> {
    fn default() -> Self {
        Self::with_params(DEFAULT_MAX_LEVEL, DEFAULT_P)
    }
}

impl<T: Clone + Ord + Default> SkipList<T> {
    /// 创建空跳表，使用默认最大层数 16。
    pub fn new() -> Self {
        Self::with_params(DEFAULT_MAX_LEVEL, DEFAULT_P)
    }

    /// 自定义最大层数与晋升概率。
    pub fn with_params(max_level: usize, probability: f64) -> Self {
        let mut nodes = Vec::with_capacity(max_level + 1);
        nodes.push(Node::new(T::default(), max_level));
        Self {
            nodes,
            level: 1,
            len: 0,
            max_level,
            probability,
        }
    }

    /// 随机生成节点层数。
    fn random_level(&self) -> usize {
        let mut level = 1;
        let mut rng = rand::rng();
        while level < self.max_level && rng.random_bool(self.probability) {
            level += 1;
        }
        level
    }

    /// 查找 value 是否存在。
    pub fn contains(&self, value: &T) -> bool {
        let (_current, next) = self.search_position(value);
        next != NIL && self.nodes[next].value == *value
    }

    /// 返回元素数量。
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 在跳表中搜索小于等于 `value` 的最右位置。
    ///
    /// 返回 `(current, next)`，其中 `current` 是第 0 层中最后访问的节点索引，
    /// `next` 是第 0 层下一个节点索引。
    fn search_position(&self, value: &T) -> (usize, usize) {
        let mut current = 0usize; // head index
        for i in (0..self.level).rev() {
            while self.nodes[current].forward[i] != NIL {
                let next = self.nodes[current].forward[i];
                if self.nodes[next].value < *value {
                    current = next;
                } else {
                    break;
                }
            }
        }
        let next = self.nodes[current].forward[0];
        (current, next)
    }

    /// 插入 value。允许重复值。
    pub fn insert(&mut self, value: T) {
        let mut update = vec![0usize; self.level];
        let mut current = 0usize;

        for i in (0..self.level).rev() {
            while self.nodes[current].forward[i] != NIL {
                let next = self.nodes[current].forward[i];
                if self.nodes[next].value < value {
                    current = next;
                } else {
                    break;
                }
            }
            update[i] = current;
        }

        let new_level = self.random_level();
        if new_level > self.level {
            update.resize(new_level, 0);
            self.level = new_level;
        }

        let new_idx = self.nodes.len();
        self.nodes.push(Node::new(value, new_level));

        for (i, &prev) in update.iter().enumerate().take(new_level) {
            self.nodes[new_idx].forward[i] = self.nodes[prev].forward[i];
            self.nodes[prev].forward[i] = new_idx;
        }

        self.len += 1;
    }

    /// 删除 value，若存在则返回 true。
    ///
    /// 当存在重复值时，仅删除最靠前的一个。
    pub fn delete(&mut self, value: &T) -> bool {
        let mut update = vec![0usize; self.level];
        let mut current = 0usize;

        for i in (0..self.level).rev() {
            while self.nodes[current].forward[i] != NIL {
                let next = self.nodes[current].forward[i];
                if self.nodes[next].value < *value {
                    current = next;
                } else {
                    break;
                }
            }
            update[i] = current;
        }

        let target = self.nodes[current].forward[0];
        if target == NIL || self.nodes[target].value != *value {
            return false;
        }

        let target_level = self.nodes[target].forward.len();
        for (i, &prev) in update.iter().enumerate().take(target_level) {
            self.nodes[prev].forward[i] = self.nodes[target].forward[i];
        }

        while self.level > 1 && self.nodes[0].forward[self.level - 1] == NIL {
            self.level -= 1;
        }

        self.len -= 1;
        true
    }

    /// 返回升序遍历结果（仅用于测试）。
    pub fn to_vec(&self) -> Vec<T> {
        self.range_values_internal(None, None)
    }

    /// 返回区间 `[low, high]` 内所有值的升序副本。
    ///
    /// 边界包含；`low` 或 `high` 为 `None` 时表示无界。
    pub fn range<R>(&self, low: Option<R>, high: Option<R>) -> Vec<T>
    where
        R: std::borrow::Borrow<T>,
    {
        let low_ref = low.as_ref().map(|r| r.borrow());
        let high_ref = high.as_ref().map(|r| r.borrow());
        self.range_values_internal(low_ref, high_ref)
    }

    /// 内部范围查询实现。
    fn range_values_internal(&self, low: Option<&T>, high: Option<&T>) -> Vec<T> {
        let mut result = Vec::new();
        let mut current = match low {
            Some(bound) => {
                let mut cur = 0usize;
                for i in (0..self.level).rev() {
                    while self.nodes[cur].forward[i] != NIL {
                        let next = self.nodes[cur].forward[i];
                        if self.nodes[next].value < *bound {
                            cur = next;
                        } else {
                            break;
                        }
                    }
                }
                self.nodes[cur].forward[0]
            }
            None => self.nodes[0].forward[0],
        };

        while current != NIL {
            let value = &self.nodes[current].value;
            if high.is_some_and(|bound| value > bound) {
                break;
            }
            result.push(value.clone());
            current = self.nodes[current].forward[0];
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_skip_list_basic() {
        let mut list = SkipList::new();
        for v in [3, 1, 4, 1, 5, 9, 2, 6] {
            list.insert(v);
        }
        assert_eq!(list.len(), 8);
        assert!(list.contains(&5));
        assert!(!list.contains(&7));
        assert_eq!(list.to_vec(), vec![1, 1, 2, 3, 4, 5, 6, 9]);
    }

    #[test]
    fn test_skip_list_delete() {
        let mut list = SkipList::new();
        for v in 0..10 {
            list.insert(v);
        }
        assert!(list.delete(&5));
        assert!(!list.delete(&5));
        assert!(!list.contains(&5));
        assert_eq!(list.len(), 9);
        let expected: Vec<i32> = (0..10).filter(|x| *x != 5).collect();
        assert_eq!(list.to_vec(), expected);
    }

    #[test]
    fn test_skip_list_delete_duplicate() {
        let mut list = SkipList::new();
        list.insert(1);
        list.insert(1);
        list.insert(2);
        assert_eq!(list.len(), 3);
        assert!(list.delete(&1));
        assert_eq!(list.len(), 2);
        assert!(list.contains(&1));
        assert_eq!(list.to_vec(), vec![1, 2]);
    }

    #[test]
    fn test_skip_list_empty() {
        let list: SkipList<i32> = SkipList::new();
        assert!(list.is_empty());
        assert!(!list.contains(&0));
        assert!(list.range(Some(&1), Some(&3)).is_empty());
    }

    #[test]
    fn test_skip_list_range() {
        let mut list = SkipList::new();
        for v in [3, 1, 4, 1, 5, 9, 2, 6] {
            list.insert(v);
        }
        assert_eq!(list.range(Some(&2), Some(&5)), vec![2, 3, 4, 5]);
        assert_eq!(list.range(Some(&5), Some(&5)), vec![5]);
        assert_eq!(list.range(Some(&10), Some(&20)).is_empty(), true);
        assert_eq!(list.range(None, Some(&2)), vec![1, 1, 2]);
        assert_eq!(list.range(Some(&6), None), vec![6, 9]);
        assert_eq!(list.range(None::<&i32>, None::<&i32>), list.to_vec());
    }

    #[test]
    fn test_skip_list_range_unbounded() {
        let mut list = SkipList::new();
        for v in [10, 20, 30] {
            list.insert(v);
        }
        assert_eq!(list.range(None, Some(&15)), vec![10]);
        assert_eq!(list.range(Some(&15), None), vec![20, 30]);
        assert_eq!(list.range(None, None::<&i32>), vec![10, 20, 30]);
    }

    #[test]
    fn test_skip_list_large_sequence() {
        let mut list = SkipList::new();
        let n = 1000;
        for v in (0..n).rev() {
            list.insert(v as i32);
        }
        assert_eq!(list.len(), n);
        let values: Vec<i32> = (0..n).map(|x| x as i32).collect();
        assert_eq!(list.to_vec(), values);
        assert_eq!(
            list.range(Some(&100), Some(&104)),
            vec![100, 101, 102, 103, 104]
        );
    }
}
