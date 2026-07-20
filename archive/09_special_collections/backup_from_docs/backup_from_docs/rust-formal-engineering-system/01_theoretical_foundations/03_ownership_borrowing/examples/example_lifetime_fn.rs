// 生命周期案例：函数生命周期标注
// 理论映射：对应“生命周期多态”与“生命周期推导”理论（见 02_lifetime_and_scope.md 附录）

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

fn main() {
    let s1 = String::from("abcd");
    let s2 = String::from("xyz");
    let result = longest(&s1, &s2);
    println!("最长字符串: {}", result);
} 