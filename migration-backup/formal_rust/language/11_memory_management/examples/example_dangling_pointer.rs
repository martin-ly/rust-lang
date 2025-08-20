// 内存管理案例：悬垂指针检测与防护
// 理论映射：对应“悬垂指针”与“无悬垂指针”定理（见 01_formal_memory_model.md 附录）

fn dangling_ref() -> &i32 {
    let x = 10;
    &x // 编译错误：x在函数结束后被释放，返回悬垂引用
}

fn main() {
    // let r = dangling_ref(); // Rust类型系统阻止悬垂指针
} 