//! 原生类型：标量、复合、引用与 Sized。
//!
//! Rust 的类型系统以原生类型为基石：
//!
//! - **标量**：`i32`、`f64`、`bool`、`char` 等
//! - **复合**：`array`、`tuple`、`struct`、`enum`
//! - **引用**：`&T`、`&mut T`、切片、trait object
//! - **大小**：`Sized` / `?Sized`

pub mod compound_types;
pub mod reference_types;
pub mod scalar_types;
pub mod sized_type;

/// 汇总展示各类原生类型。
pub fn demonstrate_primitives() {
    let _n: i32 = 42;
    let _f: f64 = 1.5;
    let _b: bool = true;
    let _c: char = '中';
    let _arr: [i32; 3] = [1, 2, 3];
    let _tuple: (i32, f64, &str) = (1, 2.0, "hello");
    let _slice: &[i32] = &[1, 2, 3];
    let _s: &str = "Rust";
    let _ = (_n, _f, _b, _c, _arr, _tuple, _slice, _s);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitives_compile() {
        demonstrate_primitives();
    }
}
