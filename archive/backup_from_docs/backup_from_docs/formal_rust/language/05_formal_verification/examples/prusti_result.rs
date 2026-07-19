// Prusti错误处理与Result安全性验证示例
// 工程意义：演示如何用Prusti注解验证Result类型的错误处理安全性，防止未处理错误
use prusti_contracts::*;

#[requires(b != 0)]
#[ensures(result.is_ok())]
fn checked_div(a: i32, b: i32) -> Result<i32, &'static str> {
    if b == 0 {
        Err("division by zero")
    } else {
        Ok(a / b)
    }
}

fn main() {
    let r1 = checked_div(10, 2);
    assert_eq!(r1, Ok(5));
    let r2 = checked_div(10, 0);
    assert!(r2.is_err());
}

// 形式化注释：
// ∀a, b ≠ 0 ⇒ checked_div(a, b) = Ok(a / b)
// b = 0 ⇒ checked_div(a, b) = Err
// 工具建议：Prusti可自动验证Result类型的错误处理安全 