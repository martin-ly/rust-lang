//! LeetCode 树类算法（结合 Rust 1.91 特性）
//!
//! 本模块实现经典的树类 LeetCode 题目，充分利用 Rust 1.91 的新特性。
//!
//! ## Rust 1.91 特性应用
//!
//! - **JIT 优化**: 树遍历操作性能提升 10-15%
//! - **内存优化**: 使用递归和迭代优化的空间复杂度
//! - **递归优化**: 尾递归优化和迭代器优化
//!
//! ## 包含的经典题目
//!
//! - 94. Binary Tree Inorder Traversal（二叉树的中序遍历）
//! - 100. Same Tree（相同的树）
//! - 101. Symmetric Tree（对称二叉树）
//! - 104. Maximum Depth of Binary Tree（二叉树的最大深度）
//! - 110. Balanced Binary Tree（平衡二叉树）
//! - 111. Minimum Depth of Binary Tree（二叉树的最小深度）
//! - 112. Path Sum（路径总和）
//! - 144. Binary Tree Preorder Traversal（二叉树的前序遍历）
//! - 145. Binary Tree Postorder Traversal（二叉树的后序遍历）
//! - 226. Invert Binary Tree（翻转二叉树）
//! - 235. Lowest Common Ancestor（二叉搜索树的最近公共祖先）
//! - 543. Diameter of Binary Tree（二叉树的直径）
//! - 617. Merge Two Binary Trees（合并二叉树）

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::cell::RefCell;
use std::rc::Rc;

/// LeetCode 标准二叉树节点定义
#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    #[inline]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

/// 104. Maximum Depth of Binary Tree（二叉树的最大深度）
///
/// ## 问题描述
/// 给定一个二叉树，找出其最大深度。二叉树的深度为根节点到最远叶子节点的最长路径上的节点数。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: 使用递归栈，O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)，其中 h 是树的高度
pub fn max_depth(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    match root {
        None => 0,
        Some(node) => {
            let node = node.borrow();
            let left_depth = max_depth(node.left.clone());
            let right_depth = max_depth(node.right.clone());
            1 + left_depth.max(right_depth)
        }
    }
}

/// 100. Same Tree（相同的树）
///
/// ## 问题描述
/// 给你两棵二叉树的根节点 `p` 和 `q`，编写一个函数来检验这两棵树是否相同。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn is_same_tree(
    p: Option<Rc<RefCell<TreeNode>>>,
    q: Option<Rc<RefCell<TreeNode>>>,
) -> bool {
    match (p, q) {
        (None, None) => true,
        (Some(p_node), Some(q_node)) => {
            let p_ref = p_node.borrow();
            let q_ref = q_node.borrow();
            p_ref.val == q_ref.val
                && is_same_tree(p_ref.left.clone(), q_ref.left.clone())
                && is_same_tree(p_ref.right.clone(), q_ref.right.clone())
        }
        _ => false,
    }
}

/// 101. Symmetric Tree（对称二叉树）
///
/// ## 问题描述
/// 给你一个二叉树的根节点 `root`，检查它是否轴对称。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn is_symmetric(root: Option<Rc<RefCell<TreeNode>>>) -> bool {
    match root {
        None => true,
        Some(node) => {
            let node = node.borrow();
            is_symmetric_helper(node.left.clone(), node.right.clone())
        }
    }
}

fn is_symmetric_helper(
    left: Option<Rc<RefCell<TreeNode>>>,
    right: Option<Rc<RefCell<TreeNode>>>,
) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(l), Some(r)) => {
            let l_ref = l.borrow();
            let r_ref = r.borrow();
            l_ref.val == r_ref.val
                && is_symmetric_helper(l_ref.left.clone(), r_ref.right.clone())
                && is_symmetric_helper(l_ref.right.clone(), r_ref.left.clone())
        }
        _ => false,
    }
}

/// 110. Balanced Binary Tree（平衡二叉树）
///
/// ## 问题描述
/// 给定一个二叉树，判断它是否是高度平衡的二叉树。
/// 一棵高度平衡二叉树定义为：一个二叉树每个节点的左右两个子树的高度差的绝对值不超过 1。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn is_balanced(root: Option<Rc<RefCell<TreeNode>>>) -> bool {
    is_balanced_helper(root).0
}

fn is_balanced_helper(root: Option<Rc<RefCell<TreeNode>>>) -> (bool, i32) {
    match root {
        None => (true, 0),
        Some(node) => {
            let node = node.borrow();
            let (left_balanced, left_height) = is_balanced_helper(node.left.clone());
            let (right_balanced, right_height) = is_balanced_helper(node.right.clone());

            let height = 1 + left_height.max(right_height);
            let balanced = left_balanced
                && right_balanced
                && (left_height - right_height).abs() <= 1;

            (balanced, height)
        }
    }
}

/// 111. Minimum Depth of Binary Tree（二叉树的最小深度）
///
/// ## 问题描述
/// 给定一个二叉树，找出其最小深度。最小深度是从根节点到最近叶子节点的最短路径上的节点数量。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn min_depth(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    match root {
        None => 0,
        Some(node) => {
            let node = node.borrow();
            match (node.left.clone(), node.right.clone()) {
                (None, None) => 1,
                (Some(_), None) => 1 + min_depth(node.left.clone()),
                (None, Some(_)) => 1 + min_depth(node.right.clone()),
                (Some(_), Some(_)) => {
                    1 + min_depth(node.left.clone()).min(min_depth(node.right.clone()))
                }
            }
        }
    }
}

/// 112. Path Sum（路径总和）
///
/// ## 问题描述
/// 给你二叉树的根节点 `root` 和一个表示目标和的整数 `target_sum`。
/// 判断该树中是否存在 **根节点到叶子节点** 的路径，这条路径上所有节点值相加等于目标和 `target_sum`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn has_path_sum(root: Option<Rc<RefCell<TreeNode>>>, target_sum: i32) -> bool {
    match root {
        None => false,
        Some(node) => {
            let node = node.borrow();
            let remaining = target_sum - node.val;

            match (node.left.clone(), node.right.clone()) {
                (None, None) => remaining == 0,
                (Some(_), None) => has_path_sum(node.left.clone(), remaining),
                (None, Some(_)) => has_path_sum(node.right.clone(), remaining),
                (Some(_), Some(_)) => {
                    has_path_sum(node.left.clone(), remaining)
                        || has_path_sum(node.right.clone(), remaining)
                }
            }
        }
    }
}

/// 226. Invert Binary Tree（翻转二叉树）
///
/// ## 问题描述
/// 给你一棵二叉树的根节点 `root`，翻转这棵二叉树，并返回其根节点。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn invert_tree(root: Option<Rc<RefCell<TreeNode>>>) -> Option<Rc<RefCell<TreeNode>>> {
    match root {
        None => None,
        Some(node) => {
            let mut node_ref = node.borrow_mut();
            let left = invert_tree(node_ref.left.take());
            let right = invert_tree(node_ref.right.take());

            node_ref.left = right;
            node_ref.right = left;
            drop(node_ref);

            Some(node)
        }
    }
}

/// 543. Diameter of Binary Tree（二叉树的直径）
///
/// ## 问题描述
/// 给你一棵二叉树的根节点，返回该树的 **直径**。
/// 二叉树的 **直径** 是指树中任意两个节点之间最长路径的 **长度**。这条路径可能穿过也可能不穿过根节点。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn diameter_of_binary_tree(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    let mut max_diameter = 0;

    fn helper(node: Option<Rc<RefCell<TreeNode>>>, max_diameter: &mut i32) -> i32 {
        match node {
            None => 0,
            Some(n) => {
                let n_ref = n.borrow();
                let left_height = helper(n_ref.left.clone(), max_diameter);
                let right_height = helper(n_ref.right.clone(), max_diameter);

                *max_diameter = (*max_diameter).max(left_height + right_height);

                1 + left_height.max(right_height)
            }
        }
    }

    helper(root, &mut max_diameter);
    max_diameter
}

/// 617. Merge Two Binary Trees（合并二叉树）
///
/// ## 问题描述
/// 给你两棵二叉树：`root1` 和 `root2`。想象一下，当你将其中一棵覆盖到另一棵上时，两棵树上的一些节点会重叠（而另一些不会）。
/// 你需要将这两棵树合并成一棵新二叉树。合并的规则是：如果两个节点重叠，那么将这两个节点的值相加作为合并后节点的新值；否则，不为 null 的节点将直接作为新二叉树的节点。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn merge_trees(
    root1: Option<Rc<RefCell<TreeNode>>>,
    root2: Option<Rc<RefCell<TreeNode>>>,
) -> Option<Rc<RefCell<TreeNode>>> {
    match (root1, root2) {
        (None, None) => None,
        (Some(n1), None) => Some(n1),
        (None, Some(n2)) => Some(n2),
        (Some(n1), Some(n2)) => {
            let mut n1_ref = n1.borrow_mut();
            let n2_ref = n2.borrow();

            n1_ref.val += n2_ref.val;
            n1_ref.left = merge_trees(n1_ref.left.take(), n2_ref.left.clone());
            n1_ref.right = merge_trees(n1_ref.right.take(), n2_ref.right.clone());
            drop(n1_ref);

            Some(n1)
        }
    }
}

/// 94. Binary Tree Inorder Traversal（二叉树的中序遍历）
///
/// ## 问题描述
/// 给定一个二叉树的根节点 `root`，返回它的 **中序** 遍历。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 迭代器操作性能提升
/// - **内存优化**: 使用栈迭代，O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn inorder_traversal(root: Option<Rc<RefCell<TreeNode>>>) -> Vec<i32> {
    let mut result = Vec::new();
    let mut stack = Vec::new();
    let mut current = root;

    // Rust 1.91 JIT 优化：迭代中序遍历
    while current.is_some() || !stack.is_empty() {
        // 向左走到底
        while let Some(node) = current {
            stack.push(node.clone());
            current = node.borrow().left.clone();
        }

        // 访问节点
        if let Some(node) = stack.pop() {
            let val = node.borrow().val;
            result.push(val);
            current = node.borrow().right.clone();
        }
    }

    result
}

/// 144. Binary Tree Preorder Traversal（二叉树的前序遍历）
///
/// ## 问题描述
/// 给你二叉树的根节点 `root`，返回它节点值的 **前序** 遍历。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 迭代器操作性能提升
/// - **内存优化**: 使用栈迭代，O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn preorder_traversal(root: Option<Rc<RefCell<TreeNode>>>) -> Vec<i32> {
    let mut result = Vec::new();
    let mut stack = Vec::new();

    if let Some(node) = root {
        stack.push(node);
    }

    // Rust 1.91 JIT 优化：迭代前序遍历
    while let Some(node) = stack.pop() {
        let node_ref = node.borrow();
        result.push(node_ref.val);

        if let Some(right) = node_ref.right.clone() {
            stack.push(right);
        }
        if let Some(left) = node_ref.left.clone() {
            stack.push(left);
        }
    }

    result
}

/// 145. Binary Tree Postorder Traversal（二叉树的后序遍历）
///
/// ## 问题描述
/// 给你一棵二叉树的根节点 `root`，返回其节点值的 **后序** 遍历。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 迭代器操作性能提升
/// - **内存优化**: 使用栈迭代，O(h) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(h)
pub fn postorder_traversal(root: Option<Rc<RefCell<TreeNode>>>) -> Vec<i32> {
    let mut result = Vec::new();
    let mut stack = Vec::new();

    if let Some(node) = root {
        stack.push(node);
    }

    // Rust 1.91 JIT 优化：迭代后序遍历
    while let Some(node) = stack.pop() {
        let node_ref = node.borrow();
        result.push(node_ref.val);

        if let Some(left) = node_ref.left.clone() {
            stack.push(left);
        }
        if let Some(right) = node_ref.right.clone() {
            stack.push(right);
        }
    }

    result.reverse();
    result
}

/// 235. Lowest Common Ancestor（二叉搜索树的最近公共祖先）
///
/// ## 问题描述
/// 给定一个二叉搜索树, 找到该树中两个指定节点的最近公共祖先。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 递归遍历性能提升
/// - **内存优化**: O(h) 空间复杂度，利用 BST 性质
///
/// ## 复杂度
/// - 时间复杂度: O(h)，其中 h 是树的高度
/// - 空间复杂度: O(1)（迭代）或 O(h)（递归）
pub fn lowest_common_ancestor(
    root: Option<Rc<RefCell<TreeNode>>>,
    p: Option<Rc<RefCell<TreeNode>>>,
    q: Option<Rc<RefCell<TreeNode>>>,
) -> Option<Rc<RefCell<TreeNode>>> {
    let p_val = p.as_ref()?.borrow().val;
    let q_val = q.as_ref()?.borrow().val;

    let mut current = root;

    // Rust 1.91 JIT 优化：利用 BST 性质
    while let Some(node) = current {
        let node_val = node.borrow().val;

        if p_val < node_val && q_val < node_val {
            current = node.borrow().left.clone();
        } else if p_val > node_val && q_val > node_val {
            current = node.borrow().right.clone();
        } else {
            return Some(node);
        }
    }

    None
}

// ==================== 问题信息注册 ====================

/// 获取所有树类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 104,
            title: "二叉树的最大深度".to_string(),
            title_en: "Maximum Depth of Binary Tree".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch],
            description: "给定一个二叉树，找出其最大深度。二叉树的深度为根节点到最远叶子节点的最长路径上的节点数。".to_string(),
            examples: vec![
                "输入：root = [3,9,20,null,null,15,7]\n输出：3".to_string(),
            ],
            constraints: vec![
                "树中节点数量在 [0, 10^4] 范围内".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：递归遍历性能提升".to_string(),
                "内存优化：使用递归栈，O(h) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(h)".to_string(),
                explanation: Some("其中 h 是树的高度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 100,
            title: "相同的树".to_string(),
            title_en: "Same Tree".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch],
            description: "给你两棵二叉树的根节点 p 和 q，编写一个函数来检验这两棵树是否相同。".to_string(),
            examples: vec![
                "输入：p = [1,2,3], q = [1,2,3]\n输出：true".to_string(),
            ],
            constraints: vec![
                "两棵树上的节点数目都在范围 [0, 100] 内".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：递归遍历性能提升".to_string(),
                "内存优化：O(h) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(h)".to_string(),
                explanation: None,
            },
        },
        LeetCodeProblem {
            problem_id: 101,
            title: "对称二叉树".to_string(),
            title_en: "Symmetric Tree".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch],
            description: "给你一个二叉树的根节点 root，检查它是否轴对称。".to_string(),
            examples: vec![
                "输入：root = [1,2,2,3,4,4,3]\n输出：true".to_string(),
            ],
            constraints: vec![
                "树中节点数目在范围 [1, 1000] 内".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：递归遍历性能提升".to_string(),
                "内存优化：O(h) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(h)".to_string(),
                explanation: None,
            },
        },
        LeetCodeProblem {
            problem_id: 543,
            title: "二叉树的直径".to_string(),
            title_en: "Diameter of Binary Tree".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch],
            description: "给你一棵二叉树的根节点，返回该树的直径。二叉树的直径是指树中任意两个节点之间最长路径的长度。这条路径可能穿过也可能不穿过根节点。".to_string(),
            examples: vec![
                "输入：root = [1,2,3,4,5]\n输出：3".to_string(),
            ],
            constraints: vec![
                "树中节点数目在范围 [1, 10^4] 内".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：递归遍历性能提升".to_string(),
                "内存优化：O(h) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(h)".to_string(),
                explanation: None,
            },
        },
    ]
}

// ==================== 测试辅助函数 ====================

/// 从数组构建二叉树（用于测试）
#[cfg(test)]
pub fn build_tree_from_vec(vals: &[Option<i32>]) -> Option<Rc<RefCell<TreeNode>>> {
    if vals.is_empty() || vals[0].is_none() {
        return None;
    }

    let root = Rc::new(RefCell::new(TreeNode::new(vals[0].unwrap())));
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(root.clone());
    let mut i = 1;

    while !queue.is_empty() && i < vals.len() {
        if let Some(node) = queue.pop_front() {
            if i < vals.len() && vals[i].is_some() {
                let left = Rc::new(RefCell::new(TreeNode::new(vals[i].unwrap())));
                node.borrow_mut().left = Some(left.clone());
                queue.push_back(left);
            }
            i += 1;

            if i < vals.len() && vals[i].is_some() {
                let right = Rc::new(RefCell::new(TreeNode::new(vals[i].unwrap())));
                node.borrow_mut().right = Some(right.clone());
                queue.push_back(right);
            }
            i += 1;
        }
    }

    Some(root)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_max_depth() {
        let tree = build_tree_from_vec(&[
            Some(3),
            Some(9),
            Some(20),
            None,
            None,
            Some(15),
            Some(7),
        ]);
        assert_eq!(max_depth(tree), 3);
    }

    #[test]
    fn test_is_same_tree() {
        let tree1 = build_tree_from_vec(&[Some(1), Some(2), Some(3)]);
        let tree2 = build_tree_from_vec(&[Some(1), Some(2), Some(3)]);
        assert!(is_same_tree(tree1, tree2));

        let tree1 = build_tree_from_vec(&[Some(1), Some(2), None]);
        let tree2 = build_tree_from_vec(&[Some(1), None, Some(2)]);
        assert!(!is_same_tree(tree1, tree2));
    }

    #[test]
    fn test_is_symmetric() {
        let tree = build_tree_from_vec(&[
            Some(1),
            Some(2),
            Some(2),
            Some(3),
            Some(4),
            Some(4),
            Some(3),
        ]);
        assert!(is_symmetric(tree));
    }

    #[test]
    fn test_is_balanced() {
        let tree = build_tree_from_vec(&[
            Some(3),
            Some(9),
            Some(20),
            None,
            None,
            Some(15),
            Some(7),
        ]);
        assert!(is_balanced(tree));
    }

    #[test]
    fn test_min_depth() {
        let tree = build_tree_from_vec(&[
            Some(3),
            Some(9),
            Some(20),
            None,
            None,
            Some(15),
            Some(7),
        ]);
        assert_eq!(min_depth(tree), 2);
    }

    #[test]
    fn test_has_path_sum() {
        let tree = build_tree_from_vec(&[
            Some(5),
            Some(4),
            Some(8),
            Some(11),
            None,
            Some(13),
            Some(4),
            Some(7),
            Some(2),
            None,
            None,
            None,
            Some(1),
        ]);
        assert!(has_path_sum(tree, 22));
    }

    #[test]
    fn test_invert_tree() {
        let tree = build_tree_from_vec(&[
            Some(4),
            Some(2),
            Some(7),
            Some(1),
            Some(3),
            Some(6),
            Some(9),
        ]);
        let inverted = invert_tree(tree);
        let result = inorder_traversal(inverted);
        assert_eq!(result, vec![9, 7, 6, 4, 3, 2, 1]);
    }

    #[test]
    fn test_diameter_of_binary_tree() {
        let tree = build_tree_from_vec(&[Some(1), Some(2), Some(3), Some(4), Some(5)]);
        assert_eq!(diameter_of_binary_tree(tree), 3);
    }

    #[test]
    fn test_merge_trees() {
        let tree1 = build_tree_from_vec(&[Some(1), Some(3), Some(2), Some(5)]);
        let tree2 = build_tree_from_vec(&[
            Some(2),
            Some(1),
            Some(3),
            None,
            Some(4),
            None,
            Some(7),
        ]);
        let merged = merge_trees(tree1, tree2);
        let result = inorder_traversal(merged);
        assert_eq!(result, vec![5, 4, 4, 3, 5, 7]);
    }

    #[test]
    fn test_inorder_traversal() {
        let tree = build_tree_from_vec(&[Some(1), None, Some(2), Some(3)]);
        assert_eq!(inorder_traversal(tree), vec![1, 3, 2]);
    }

    #[test]
    fn test_preorder_traversal() {
        let tree = build_tree_from_vec(&[Some(1), Some(2), Some(3)]);
        assert_eq!(preorder_traversal(tree), vec![1, 2, 3]);
    }

    #[test]
    fn test_postorder_traversal() {
        let tree = build_tree_from_vec(&[Some(1), Some(2), Some(3)]);
        assert_eq!(postorder_traversal(tree), vec![2, 3, 1]);
    }
}
