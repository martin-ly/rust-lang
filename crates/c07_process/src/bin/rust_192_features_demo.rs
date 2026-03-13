//! Rust 1.92.0 新特性演示程序
//!
//! 这个程序展示了如何在 c07_process 项目中使用最新的 Rust 1.92.0 特性
use c07_process::rust_192_features::{
    demonstrate_rust_192_process_features,
    ProcessQueue, ProcessInfo, RoundRobinScheduler,
    calculate_process_pool_size, ProcessResourceAllocator,
    compare_process_lists, check_process_states,
};
use std::num::NonZeroUsize;

fn main() {
    println!("🚀 Rust 1.92.0 进程管理新特性演示");
    println!("===================================\n");

    // 运行综合演示
    demonstrate_rust_192_process_features();

    // 额外演示：进程队列管理
    println!("\n=== 额外演示：进程队列管理 ===");
    let mut queue = ProcessQueue::new();

    // 添加进程
    queue.push(ProcessInfo {
        pid: 1001,
        name: "worker-1".to_string(),
        priority: 10,
    });
    queue.push(ProcessInfo {
        pid: 1002,
        name: "worker-2".to_string(),
        priority: 20,
    });
    queue.push(ProcessInfo {
        pid: 1003,
        name: "worker-3".to_string(),
        priority: 30,
    });
    queue.push(ProcessInfo {
        pid: 1004,
        name: "worker-4".to_string(),
        priority: 40,
    });

    println!("初始队列顺序:");
    for (i, proc) in queue.iter().enumerate() {
        println!("  {}: PID={}, Name={}, Priority={}",
            i + 1, proc.pid, proc.name, proc.priority);
    }

    // 轮转队列
    queue.rotate(2);
    println!("\n轮转 2 个位置后:");
    for (i, proc) in queue.iter().enumerate() {
        println!("  {}: PID={}, Name={}, Priority={}",
            i + 1, proc.pid, proc.name, proc.priority);
    }

    // 额外演示：进程池大小计算
    println!("\n=== 额外演示：进程池大小计算 ===");
    let chunk_size = NonZeroUsize::new(8).unwrap();
    let total_tasks = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
    let pool_size = calculate_process_pool_size(total_tasks.len(), chunk_size);
    println!("总任务数: {}", total_tasks.len());
    println!("每进程任务数: {}", chunk_size);
    println!("需要的进程数: {}", pool_size);

    // 额外演示：资源分配
    println!("\n=== 额外演示：进程资源分配 ===");
    let allocator = ProcessResourceAllocator::new(2048, NonZeroUsize::new(128).unwrap());
    println!("总内存: 2048 MB");
    println!("每进程内存: 128 MB");
    println!("最大进程数: {}", allocator.max_processes());

    // 额外演示：进程列表比较
    println!("\n=== 额外演示：进程列表比较 ===");
    let list1 = vec![
        ProcessInfo {
            pid: 2001,
            name: "service-a".to_string(),
            priority: 50,
        },
        ProcessInfo {
            pid: 2002,
            name: "service-b".to_string(),
            priority: 60,
        },
    ];
    let list2 = list1.clone();
    let list3 = vec![
        ProcessInfo {
            pid: 2001,
            name: "service-a".to_string(),
            priority: 50,
        },
        ProcessInfo {
            pid: 2003,
            name: "service-c".to_string(),
            priority: 70,
        },
    ];

    println!("列表1 和 列表2 相等: {}", compare_process_lists(&list1, &list2));
    println!("列表1 和 列表3 相等: {}", compare_process_lists(&list1, &list3));

    // 额外演示：进程状态检查
    println!("\n=== 额外演示：进程状态检查 ===");
    let processes = vec![
        ProcessInfo {
            pid: 3001,
            name: "task-1".to_string(),
            priority: 80,
        },
        ProcessInfo {
            pid: 3002,
            name: "task-2".to_string(),
            priority: 90,
        },
    ];
    let expected_pids = vec![3001, 3002];
    let wrong_pids = vec![3001, 3003];

    println!("进程列表匹配预期PID: {}", check_process_states(&processes, &expected_pids));
    println!("进程列表匹配错误PID: {}", check_process_states(&processes, &wrong_pids));

    // 额外演示：循环调度器
    println!("\n=== 额外演示：循环调度器 ===");
    let _scheduler = RoundRobinScheduler::new(100);
    println!("创建循环调度器，时间片: 100ms");
    println!("调度器已创建，可以使用 schedule() 方法进行调度");

    println!("\n✅ 所有演示完成！");
}
