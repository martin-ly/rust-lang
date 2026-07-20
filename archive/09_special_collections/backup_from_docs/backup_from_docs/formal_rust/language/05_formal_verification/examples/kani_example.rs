// Kani模型检查示例
// 工程意义：演示如何用Kani进行边界条件与并发安全模型检查
#[kani::proof]
fn check_add() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    assert!(x.wrapping_add(y) >= x);
} 