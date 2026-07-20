// 模块化基本示例（Philosophical & Rigorous Example for Modularity）
// 本示例展示如何用mod、pub(crate)实现模块边界与可见性控制
// This example demonstrates how to use mod and pub(crate) for module boundary and visibility control

mod core_logic {
    // 哲学：关注点分离，科学：可见性约束
    // Philosophy: separation of concerns, Science: visibility constraint
    pub(crate) fn internal_fn() -> &'static str {
        "模块内部逻辑/Module internal logic"
    }
}

pub fn use_mod() {
    println!("{} 哲科严谨", core_logic::internal_fn());
}

fn main() {
    use_mod();
} 