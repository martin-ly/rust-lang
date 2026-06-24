//! 不变（invariance）：内部可变性使容器无法随元素子类型化。

use std::cell::Cell;

/// `Cell<T>` 对 `T` 是不变的。
///
/// 下面这种把 `Cell<&'static str>` 当作 `Cell<&'a str>` 返回的代码无法通过编译，
/// 否则就可以在较短生命周期里写入一个指向已释放数据的引用。
///
/// ```compile_fail
/// use std::cell::Cell;
///
/// fn bad<'a>(c: Cell<&'static str>) -> Cell<&'a str> {
///     c
/// }
/// ```
pub fn cell_invariance_example() {
    let c = Cell::new("static");
    // c 内部可以写入任何生命周期不超出其自身的 &str
    let local = String::from("local");
    c.set(&local);
    assert_eq!(c.get(), "local");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cell_invariance() {
        cell_invariance_example();
    }
}
