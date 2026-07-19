// 泛型案例：生命周期约束与泛型
// 理论映射：对应“生命周期约束”与“泛型类型安全性”定理（见 01_formal_generics_system.md 附录）

fn longest<'a, T: AsRef<str> + 'a>(x: &'a T, y: &'a T) -> &'a T {
    if x.as_ref().len() > y.as_ref().len() { x } else { y }
}

fn main() {
    let s1 = String::from("abcd");
    let s2 = String::from("xyz");
    let result = longest(&s1, &s2);
    println!("最长: {}", result.as_ref());
} 