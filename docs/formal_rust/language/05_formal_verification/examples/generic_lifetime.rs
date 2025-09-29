// 泛型与生命周期安全性示例
// 工程意义：演示Rust泛型与生命周期约束如何保证引用安全，适用于Prusti/Creusot等工具验证

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let s1 = String::from("hello");
    let s2 = String::from("world!");
    let result = longest(&s1, &s2);
    assert_eq!(result, "world!");
}

// 形式化注释：
// ∀x: &'a str, ∀y: &'a str, result = longest(x, y) ⇒ (result == x ∨ result == y) ∧ lifetime(result) ≤ 'a
// 工具建议：Prusti/Creusot 可验证泛型与生命周期安全 