// 所有权、借用、生命周期安全性示例
// 工程意义：演示Rust所有权与借用规则如何在编译期消除悬垂指针和二次释放，适用于Prusti/Creusot等工具验证

fn main() {
    let s = String::from("hello"); // s 拥有所有权
    let r = &s; // 不可变借用
    println!("{}", r); // 合法，生命周期受限于s
    // s 离开作用域自动释放，无悬垂指针
}

// 形式化注释：
// ∀v. ∃! owner(v)
// ∀borrow. lifetime(borrow) ≤ lifetime(owner)
// 工具建议：Prusti/Creusot 可验证借用与生命周期安全 