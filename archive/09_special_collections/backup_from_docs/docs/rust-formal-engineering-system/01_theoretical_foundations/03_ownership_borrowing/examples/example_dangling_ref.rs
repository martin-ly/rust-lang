// 所有权案例：悬垂引用与借用检查
// 理论映射：对应“悬垂引用”与“生命周期有界性”定理（见 01_formal_ownership_system.md 附录）

fn dangling_ref() -> &String {
    let s = String::from("oops");
    &s // 编译错误：s在函数结束后被释放，返回悬垂引用
}

fn main() {
    // let r = dangling_ref(); // 编译不通过，Rust借用检查器阻止悬垂引用
} 