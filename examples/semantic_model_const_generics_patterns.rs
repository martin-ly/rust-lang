//! Rust const generics 模式：依赖类型的工程可用片段
//!
//! 本示例对应概念页 `concept/04_formal/00_type_theory/10_dependent_refinement_types.md`，
//! 展示如何用 const generics、associated consts 和 Phantom 类型在稳定 Rust 中表达
//! “值进入类型”的受限形式，并标明与完整依赖类型的边界。

use std::marker::PhantomData;

// ============================================================================
// 1. const generics：长度进入类型的数组包装
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ArrayVec<T, const N: usize> {
    data: [T; N],
}

impl<T: Default + Copy, const N: usize> ArrayVec<T, N> {
    fn new() -> Self {
        Self { data: [T::default(); N] }
    }

    const fn len(&self) -> usize {
        N
    }

    fn get(&self, i: usize) -> Option<&T> {
        if i < N { Some(&self.data[i]) } else { None }
    }
}

// ============================================================================
// 2. associated const：把常量绑定到类型，再透传 const generic
// ============================================================================

trait Dimension {
    const SIZE: usize;
}

struct Dim2;
struct Dim3;

impl Dimension for Dim2 {
    const SIZE: usize = 2;
}

impl Dimension for Dim3 {
    const SIZE: usize = 3;
}

// 稳定 Rust 中不能直接用 D::SIZE 作为数组长度，因此将 N 显式参数化，
// 并用 trait 关联常量提供语义标签。
#[derive(Debug, Clone, Copy, PartialEq)]
struct VectorN<D: Dimension, const N: usize> {
    components: [f64; N],
    _marker: PhantomData<D>,
}

impl<D: Dimension, const N: usize> VectorN<D, N> {
    fn zero() -> Self {
        Self {
            components: [0.0; N],
            _marker: PhantomData,
        }
    }

    fn dot(&self, other: &Self) -> f64 {
        let mut sum = 0.0;
        for i in 0..N {
            sum += self.components[i] * other.components[i];
        }
        sum
    }

    const fn dimension_name() -> usize {
        D::SIZE
    }
}

// ============================================================================
// 3. Phantom 类型模拟索引族 / GADT 的轻量形态
// ============================================================================

struct Unit<M>(PhantomData<M>);

struct Meter;
struct Second;

trait UnitLabel {
    const NAME: &'static str;
}

impl UnitLabel for Unit<Meter> {
    const NAME: &'static str = "meter";
}

impl UnitLabel for Unit<Second> {
    const NAME: &'static str = "second";
}

// ============================================================================
// 4. 边界：运行时值不能构造类型
// ============================================================================

fn runtime_value_cannot_become_type(n: usize) {
    // 以下代码在 Rust 1.97 stable 上无法编译，因为 `n` 是运行时值：
    // let arr: [i32; n] = [0; n];
    //
    // 依赖类型允许 `Vec Int n` 中的 `n` 来自任意值；
    // Rust 的 const generics 只允许编译期已知的常量表达式。
    let _ = n;
}

fn main() {
    // const generics
    let v = ArrayVec::<i32, 4>::new();
    assert_eq!(v.len(), 4);
    assert_eq!(v.get(0), Some(&0));

    // associated const + const generic
    let a = VectorN::<Dim3, 3>::zero();
    let b = VectorN::<Dim3, 3>::zero();
    assert_eq!(a.dot(&b), 0.0);
    assert_eq!(VectorN::<Dim3, 3>::dimension_name(), 3);

    // Phantom unit labels
    assert_eq!(<Unit<Meter> as UnitLabel>::NAME, "meter");
    assert_eq!(<Unit<Second> as UnitLabel>::NAME, "second");

    runtime_value_cannot_become_type(10);

    println!("All const-generic dependent-type fragments passed.");
}
