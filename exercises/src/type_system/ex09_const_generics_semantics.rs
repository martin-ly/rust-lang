//! # 练习 9: 常量泛型语义 / Exercise 9: Const Generics Semantics
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 常量泛型、编译期长度约束、依赖类型片段
//!   Const generics, compile-time length constraints, dependent-type fragments
//!
//! ## 题目描述 / Problem Description
//!
//! 用常量泛型在编译期编码向量长度，体验 Rust 中“依赖类型片段”的表达方式。
//! Use const generics to encode vector length at compile time, experiencing
//! the "dependent type fragment" style in Rust.
//!
//! ## 对应概念 / Related Concepts
//!
//! - `concept/04_formal/00_type_theory/10_dependent_refinement_types.md`
//! - `concept/02_intermediate/01_generics/01_generics.md`

/// 定长向量：长度在类型层面编码 / Fixed-length vector: length encoded at the type level
#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T, const N: usize> {
    data: [T; N],
}

impl<T: Copy + Default, const N: usize> Vector<T, N> {
    /// 创建零初始化向量 / Create a zero-initialized vector
    pub fn new() -> Self {
        Self {
            data: [T::default(); N],
        }
    }

    /// 从数组构造 / Construct from an array
    pub fn from_array(data: [T; N]) -> Self {
        Self { data }
    }

    /// 长度（编译期已知）/ Length (known at compile time)
    pub const fn len(&self) -> usize {
        N
    }

    /// 是否为空向量（`N == 0`）/ Whether this is an empty vector (`N == 0`)
    pub const fn is_empty(&self) -> bool {
        N == 0
    }

    /// 逐元素相加；类型系统保证两侧长度相同 / Element-wise add; same length guaranteed by types
    pub fn add(&self, other: &Self) -> Self
    where
        T: std::ops::Add<Output = T>,
    {
        let mut out = [T::default(); N];
        let mut i = 0;
        while i < N {
            out[i] = self.data[i] + other.data[i];
            i += 1;
        }
        Self { data: out }
    }
}

impl<T: Copy + Default, const N: usize> Default for Vector<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// 拼接两个定长向量：返回长度 `N + M` 的向量 / Concatenate: result length is `N + M`
///
/// 注意：完整的 `N + M` 泛型求值依赖 `generic_const_exprs`（nightly），
/// 本练习用运行期 `Vec` 演示等价语义。stable Rust 的编译期长度运算仍有边界。
pub fn concat<T: Copy, const N: usize, const M: usize>(
    a: &Vector<T, N>,
    b: &Vector<T, M>,
) -> Vec<T> {
    let mut out = Vec::with_capacity(N + M);
    out.extend_from_slice(&a.data);
    out.extend_from_slice(&b.data);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_zero_vector() {
        let v: Vector<i32, 3> = Vector::new();
        assert_eq!(v.len(), 3);
        assert_eq!(v, Vector::from_array([0, 0, 0]));
    }

    #[test]
    fn test_add_same_length() {
        let a = Vector::<i32, 3>::from_array([1, 2, 3]);
        let b = Vector::<i32, 3>::from_array([10, 20, 30]);
        assert_eq!(a.add(&b), Vector::from_array([11, 22, 33]));
    }

    #[test]
    fn test_add_floats() {
        let a = Vector::<f64, 2>::from_array([0.5, 1.5]);
        let b = Vector::<f64, 2>::from_array([0.5, 0.5]);
        assert_eq!(a.add(&b), Vector::from_array([1.0, 2.0]));
    }

    #[test]
    fn test_concat_lengths_add_up() {
        let a = Vector::<i32, 2>::from_array([1, 2]);
        let b = Vector::<i32, 3>::from_array([3, 4, 5]);
        let c = concat(&a, &b);
        assert_eq!(c, vec![1, 2, 3, 4, 5]);
        assert_eq!(c.len(), 2 + 3);
    }

    #[test]
    fn test_default_trait() {
        let v: Vector<u8, 4> = Vector::default();
        assert_eq!(v.len(), 4);
    }

    #[test]
    fn test_is_empty() {
        assert!(Vector::<i32, 0>::new().is_empty());
        assert!(!Vector::<i32, 1>::new().is_empty());
    }
}
