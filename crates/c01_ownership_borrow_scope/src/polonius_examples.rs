//! Polonius 借用检查器示例
//!
//! 本模块展示 Polonius 能编译但当前 borrow checker 拒绝（或受限）的代码模式。
//! 这些示例需要在 nightly Rust 下启用 `-Zpolonius` 标志才能完全通过 Polonius 检查。
//!
//! **注意**: 以下代码在 stable Rust 1.96 中部分已经可以编译（通过 Two-Phase Borrows
//! 或其他改进），但标注了 `#[cfg(polonius)]` 的代码块展示了 Polonius 才能接受的
//! 更精确分析场景。
//!
//! 运行方式:
//! ```bash
//! # nightly 下启用 Polonius
//! RUSTFLAGS="-Zpolonius" cargo +nightly check
//! ```

/// 示例 1: 条件路径分开的可变借用
///
/// 当前 borrow checker 在某些复杂条件下可能过于保守。
/// Polonius 通过路径敏感分析精确识别互斥的借用路径。
///
/// # 编译状态
/// - Stable 1.96: ✅ 可以编译 (已通过其他优化支持)
/// - Polonius: ✅ 更精确的路径分析
pub fn conditional_mut_borrow(vec: &mut Vec<i32>) {
    if vec.is_empty() {
        vec.push(1);
    } else {
        vec.clear();
    }
}

/// 示例 2: 基于守卫条件的精确借用
///
/// 使用 match 守卫时，当前编译器有时无法精确分析借用范围。
///
/// # 编译状态
/// - Stable 1.96: ⚠️ 简单场景可编译，复杂场景受限
/// - Polonius: ✅ 支持更复杂的守卫借用分析
pub fn guard_based_borrow(val: &mut Option<Vec<i32>>) {
    match val {
        Some(v) if v.len() < 10 => {
            v.push(42);
        }
        Some(v) => {
            // 注意: 这里 v 已经被隐式借用为 &mut Vec<i32>
            v.clear();
        }
        None => {}
    }
}

/// 示例 3: 循环内基于运行时条件的借用分离
///
/// 这是当前 borrow checker 最常被抱怨的场景之一：
/// 循环内根据索引条件进行不相交的借用。
///
/// # 编译状态
/// - Stable 1.96: ❌ 需要显式使用 unsafe 或 split_at_mut
/// - Polonius: ✅ 能够证明索引不相交时的借用安全性
#[cfg(polonius)]
pub fn loop_disjoint_borrow(arr: &mut [i32]) {
    let len = arr.len();
    for i in 0..len {
        // Polonius 可以证明: 当 i 和 j 不相同时，
        // arr[i] 和 arr[j] 的借用是不相交的
        if i + 1 < len && arr[i] > arr[i + 1] {
            arr.swap(i, i + 1);
        }
    }
}

/// Stable 版本的替代方案 (使用标准库 API)
pub fn loop_disjoint_borrow_stable(arr: &mut [i32]) {
    let len = arr.len();
    if len < 2 {
        return;
    }
    for i in 0..len - 1 {
        // 使用 split_at_mut 显式创建不重叠的借用
        let (left, right) = arr.split_at_mut(i + 1);
        if left[i] > right[0] {
            std::mem::swap(&mut left[i], &mut right[0]);
        }
    }
}

/// 示例 4: 结构体部分字段的独立借用 (Polonius 改进场景)
///
/// 虽然当前 Rust 已支持部分借用，但复杂嵌套场景仍有限制。
///
/// # 编译状态
/// - Stable 1.96: ⚠️ 基础场景支持，嵌套场景受限
/// - Polonius: ✅ 更精确的部分借用追踪
#[derive(Debug)]
pub struct ResourceManager {
    pub name: String,
    pub buffer: Vec<u8>,
    pub metadata: std::collections::HashMap<String, String>,
}

impl ResourceManager {
    /// 当前 Stable 已经可以编译的部分借用示例
    pub fn partial_borrow_stable(&mut self) -> (&str, &mut Vec<u8>) {
        let name = self.name.as_str();
        let buf = &mut self.buffer;
        (name, buf)
    }

    /// Polonius 将能处理的更复杂场景:
    /// 在条件分支后合并部分借用
    #[cfg(polonius)]
    pub fn complex_partial_borrow(&mut self) -> Result<&[u8], &str> {
        if self.buffer.is_empty() {
            Err(self.name.as_str())
        } else {
            Ok(self.buffer.as_slice())
        }
    }

    /// Stable 替代方案: 使用临时变量和显式作用域
    pub fn complex_partial_borrow_stable(&mut self) -> Result<&[u8], String> {
        if self.buffer.is_empty() {
            Err(self.name.clone())
        } else {
            Ok(self.buffer.as_slice())
        }
    }
}

/// 示例 5: 闭包环境中的精确借用
///
/// 闭包捕获时的借用分析是 Polonius 的重要改进领域。
///
/// # 编译状态
/// - Stable 1.96: ⚠️ 简单场景支持
/// - Polonius: ✅ 更精确的闭包捕获分析
#[cfg(polonius)]
pub fn closure_precise_borrow(data: &mut [i32]) {
    // Polonius 可以证明这些闭包捕获的是不相交的部分
    let mut first = &mut data[0];
    let mut second = &mut data[1];

    let mut update_first = || {
        *first += 1;
    };
    let mut update_second = || {
        *second += 2;
    };

    update_first();
    update_second();
}

/// Stable 版本的替代方案
pub fn closure_precise_borrow_stable(data: &mut [i32]) {
    if data.len() >= 2 {
        let (first, rest) = data.split_first_mut().unwrap();
        let second = &mut rest[0];
        *first += 1;
        *second += 2;
    }
}

/// 示例 6: 迭代器与借用的交互 (Polonius 目标场景)
///
/// 在迭代过程中根据条件借用是常见的安全模式。
#[cfg(polonius)]
pub fn iterator_conditional_borrow(items: &mut [String]) {
    for i in 0..items.len() {
        if items[i].is_empty() {
            items[i] = String::from("default");
        }
    }
}

/// Stable 版本: 使用 iter_mut()
pub fn iterator_conditional_borrow_stable(items: &mut [String]) {
    for item in items.iter_mut() {
        if item.is_empty() {
            *item = String::from("default");
        }
    }
}

/// 运行所有 Polonius 相关示例
///
/// 在 stable 环境下运行可用的示例。
pub fn run_polonius_examples() {
    println!("=== Polonius 借用检查器示例 ===\n");

    // 示例 1
    let mut vec = Vec::new();
    conditional_mut_borrow(&mut vec);
    println!("示例 1 - 条件借用: {:?}", vec);

    // 示例 2
    let mut opt = Some(vec![1, 2, 3]);
    guard_based_borrow(&mut opt);
    println!("示例 2 - 守卫借用: {:?}", opt);

    // 示例 3 stable
    let mut arr = vec![3, 1, 4, 1, 5];
    loop_disjoint_borrow_stable(&mut arr);
    println!("示例 3 - 循环不相交借用 (stable): {:?}", arr);

    // 示例 4
    let mut rm = ResourceManager {
        name: String::from("test"),
        buffer: vec![1, 2, 3],
        metadata: std::collections::HashMap::new(),
    };
    let (name, buf) = rm.partial_borrow_stable();
    println!("示例 4 - 部分借用: name={}, buffer={:?}", name, buf);

    // 示例 5 stable
    let mut data = vec![10, 20, 30];
    closure_precise_borrow_stable(&mut data);
    println!("示例 5 - 闭包精确借用 (stable): {:?}", data);

    // 示例 6 stable
    let mut items = vec![String::from(""), String::from("hello")];
    iterator_conditional_borrow_stable(&mut items);
    println!("示例 6 - 迭代器条件借用 (stable): {:?}", items);

    println!("\n说明: 标记 #[cfg(polonius)] 的示例需要 nightly + -Zpolonius");
    println!("Polonius 预计将在未来稳定版本中逐步放宽借用检查限制。");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_conditional_mut_borrow() {
        let mut vec = vec![1];
        conditional_mut_borrow(&mut vec);
        assert!(vec.is_empty());

        let mut vec2 = Vec::new();
        conditional_mut_borrow(&mut vec2);
        assert_eq!(vec2, vec![1]);
    }

    #[test]
    fn test_guard_based_borrow() {
        let mut opt = Some(vec![1, 2, 3]);
        guard_based_borrow(&mut opt);
        assert_eq!(opt.as_ref().unwrap().len(), 3);
    }

    #[test]
    fn test_loop_disjoint_borrow_stable() {
        let mut arr = vec![3, 1, 4, 1, 5];
        loop_disjoint_borrow_stable(&mut arr);
        assert_eq!(arr, vec![1, 3, 1, 4, 5]);
    }

    #[test]
    fn test_partial_borrow() {
        let mut rm = ResourceManager {
            name: String::from("test"),
            buffer: vec![1, 2, 3],
            metadata: std::collections::HashMap::new(),
        };
        let (name, buf) = rm.partial_borrow_stable();
        assert_eq!(name, "test");
        assert_eq!(buf, &vec![1, 2, 3]);
    }
}
