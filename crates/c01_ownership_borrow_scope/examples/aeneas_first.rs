//! Aeneas 首个验证示例 — 最小所有权 + 移动
//!
//! 对应定理：T-OW2（所有权唯一性）
//! 验证目标：移动后无双重所有者
//!
//! 见 docs/research_notes/AENEAS_INTEGRATION_PLAN.md

fn main() {
    let x = String::from("hello");
    let y = x; // 移动；x 不再可用
    let _ = y.len();
}
