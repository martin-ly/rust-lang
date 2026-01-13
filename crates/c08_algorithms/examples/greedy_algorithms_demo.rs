//! 贪心算法示例
//!
//! 本示例展示C08算法模块的贪心算法：
//! - 区间调度
//! - 零钱兑换
//! - 活动选择
//!
//! 运行方式:
//! ```bash
//! cargo run --example greedy_algorithms_demo
//! ```

fn main() {
    println!("🚀 贪心算法示例\n");
    println!("{}", "=".repeat(60));

    // 1. 区间调度
    println!("\n📊 区间调度:");
    println!("{}", "-".repeat(60));
    let intervals = vec![(1, 3), (2, 5), (4, 7), (6, 9), (8, 10)];
    let selected = interval_scheduling(&intervals);
    println!("所有区间: {:?}", intervals);
    println!("选择的区间: {:?}", selected);
    println!("最大不相交区间数: {}", selected.len());

    // 2. 零钱兑换（贪心版本）
    println!("\n📊 零钱兑换（贪心）:");
    println!("{}", "-".repeat(60));
    let coins = vec![1, 5, 10, 25];
    let amount = 67;
    let result = coin_change_greedy(&coins, amount);
    println!("硬币面额: {:?}", coins);
    println!("目标金额: {}", amount);
    println!("需要的硬币数: {:?}", result);

    // 3. 算法说明
    println!("\n💡 贪心算法说明:");
    println!("{}", "-".repeat(60));
    println!("  核心思想: 每一步都选择当前最优的解决方案");
    println!("  优点: 实现简单，时间复杂度低");
    println!("  缺点: 不一定能得到全局最优解");

    println!("\n✅ 贪心算法演示完成！");
}

/// 区间调度（贪心算法）
fn interval_scheduling(intervals: &[(i32, i32)]) -> Vec<(i32, i32)> {
    let mut sorted = intervals.to_vec();
    sorted.sort_by_key(|&(start, end)| (end, start)); // 按结束时间排序

    let mut selected = Vec::new();
    let mut last_end = i32::MIN;

    for (start, end) in sorted {
        if start >= last_end {
            selected.push((start, end));
            last_end = end;
        }
    }

    selected
}

/// 零钱兑换（贪心版本，适用于标准硬币系统）
fn coin_change_greedy(coins: &[usize], amount: usize) -> Option<Vec<usize>> {
    let mut sorted_coins = coins.to_vec();
    sorted_coins.sort_by(|a, b| b.cmp(a)); // 降序排列

    let mut result = Vec::new();
    let mut remaining = amount;

    for &coin in &sorted_coins {
        while remaining >= coin {
            result.push(coin);
            remaining -= coin;
        }
    }

    if remaining == 0 {
        Some(result)
    } else {
        None
    }
}
