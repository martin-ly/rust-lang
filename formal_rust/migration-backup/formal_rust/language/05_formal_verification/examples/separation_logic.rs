// 分离逻辑与内存分离、帧规则示例
// 工程意义：演示Rust如何通过分离逻辑建模内存安全，适用于Prusti/Creusot等工具验证

fn swap(x: &mut i32, y: &mut i32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}

fn main() {
    let mut a = 1;
    let mut b = 2;
    swap(&mut a, &mut b);
    assert_eq!((a, b), (2, 1));
}

// 分离逻辑断言：x和y指向的内存区域互不重叠
// {x ↦ v1 * y ↦ v2} swap(x, y) {x ↦ v2 * y ↦ v1}
// 工具建议：Prusti/Creusot 可验证借用分离 