//! 常量泛型语义示例 / Const generics semantics demo
//!
//! 用常量泛型在类型层面编码长度，演示 Rust 的“依赖类型片段”表达力，
//! 以及 `generic_const_exprs`（nightly）未稳定时的边界。
//!
//! 权威概念页（concept prose lives there, not here）：
//! - `concept/04_formal/00_type_theory/10_dependent_refinement_types.md`
//!
//! 运行方式 / Run:
//!
//! ```bash
//! cargo run -p c04_generic --example const_generics_semantics_demo
//! ```

/// 定长向量：长度在类型层面编码 / Fixed-length vector with type-level length
#[derive(Debug, Clone, PartialEq)]
struct Vector<T, const N: usize> {
    data: [T; N],
}

impl<T: Copy + Default, const N: usize> Vector<T, N> {
    fn new() -> Self {
        Self {
            data: [T::default(); N],
        }
    }

    fn from_array(data: [T; N]) -> Self {
        Self { data }
    }

    /// 逐元素相加：类型系统静态保证两侧长度一致 / Type-checked same-length add
    fn add(&self, other: &Self) -> Self
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

/// 维度匹配检查在编译期完成 / Dimension check happens at compile time
fn dot<T, const N: usize>(a: &Vector<T, N>, b: &Vector<T, N>) -> T
where
    T: Copy + Default + std::ops::Add<Output = T> + std::ops::Mul<Output = T>,
{
    let mut acc = T::default();
    let mut i = 0;
    while i < N {
        acc = acc + a.data[i] * b.data[i];
        i += 1;
    }
    acc
}

fn main() {
    let a = Vector::<i32, 3>::from_array([1, 2, 3]);
    let b = Vector::<i32, 3>::from_array([4, 5, 6]);
    println!("a + b = {:?}", a.add(&b));
    println!("a · b = {}", dot(&a, &b));

    let zero: Vector<i32, 0> = Vector::new();
    println!("零维向量 / zero-dim vector: {:?}", zero);

    // 以下无法通过编译（长度不匹配），这正是类型级长度编码的价值：
    // The following fails to compile (length mismatch) — that is the point:
    // let c = Vector::<i32, 2>::from_array([1, 2]);
    // let _ = a.add(&c); // ERROR: expected an array with a size of 3, found one with a size of 2

    println!(
        "要点 / takeaway: const generics = 依赖类型片段；完整 `N + M` 求值需 generic_const_exprs（nightly），\
         详见 concept/04_formal/00_type_theory/10_dependent_refinement_types.md"
    );
}
