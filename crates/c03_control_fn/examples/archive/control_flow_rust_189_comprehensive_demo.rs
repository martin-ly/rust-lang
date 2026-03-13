//! Rust 1.89 综合特性演示示例
//!
//! 本示例展示了Rust 1.89版本的核心新特性的综合应用：
//! - 异步trait完全稳定化
//! - 常量泛型改进
//! - 异步控制流增强
//! - 性能优化特性
use c03_control_fn::async_control_flow::AsyncStateMachine;
use c03_control_fn::async_control_flow_189::AsyncControlFlowExecutor189;
use c03_control_fn::performance_optimization_189::{COptimizedLayout, DefaultLayout, fast_add};
use c03_control_fn::rust_189_features::{
    AsyncProcessor, FACTORIAL_10, Matrix, PRIME_17, TextProcessor, calculate_matrix_size,
    is_square_matrix,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    println!("🚀 Rust 1.89 综合特性演示");
    println!("{}", "=".repeat(50));

    // 1. 异步trait完全稳定化演示
    println!("\n1️⃣ 异步trait完全稳定化演示");
    async_trait_demo().await;

    // 2. 常量泛型改进演示
    println!("\n2️⃣ 常量泛型改进演示");
    const_generics_demo();

    // 3. 异步控制流增强演示
    println!("\n3️⃣ 异步控制流增强演示");
    async_control_flow_demo().await;

    // 4. 性能优化特性演示
    println!("\n4️⃣ 性能优化特性演示");
    performance_optimization_demo();

    // 5. 综合应用场景演示
    println!("\n5️⃣ 综合应用场景演示");
    comprehensive_application_demo().await;

    println!("\n✅ Rust 1.89 综合特性演示完成！");
    Ok(())
}

/// 异步trait完全稳定化演示
async fn async_trait_demo() {
    println!("   📡 创建异步处理器...");

    let processor = TextProcessor;

    // 测试异步处理
    let data = b"Hello Rust 1.89!";
    println!("   📥 输入数据: {:?}", String::from_utf8_lossy(data));

    let result = processor.process(data).await.unwrap();
    println!("   📤 处理结果: {:?}", result);

    // 测试异步验证
    let is_valid = processor.validate("Rust 1.89").await;
    println!("   ✅ 验证结果: {}", is_valid);
}

/// 常量泛型改进演示
fn const_generics_demo() {
    println!("   🔢 创建常量泛型矩阵...");

    // 创建2x3矩阵
    let mut matrix: Matrix<i32, 2, 3> = Matrix::new();
    println!("   📐 矩阵尺寸: {:?}", Matrix::<i32, 2, 3>::dimensions());

    // 设置矩阵元素
    matrix.set(0, 0, 1);
    matrix.set(0, 1, 2);
    matrix.set(0, 2, 3);
    matrix.set(1, 0, 4);
    matrix.set(1, 1, 5);
    matrix.set(1, 2, 6);

    println!("   📝 矩阵内容:");
    for row in 0..2 {
        for col in 0..3 {
            if let Some(value) = matrix.get(row, col) {
                print!("   {} ", value);
            }
        }
        println!();
    }

    // 测试编译时常量函数
    let size = calculate_matrix_size::<2, 3>();
    let is_square = is_square_matrix::<2, 3>();
    println!("   📏 矩阵大小: {}", size);
    println!("   🔲 是否为方阵: {}", is_square);
}

/// 异步控制流增强演示
async fn async_control_flow_demo() {
    println!("   🔄 异步控制流演示...");

    let executor = AsyncControlFlowExecutor189;

    // 测试异步if-else
    println!("   🔀 测试异步if-else...");
    let result = executor
        .async_if_else(true, async { "if分支执行" }, async {
            "else分支执行"
        })
        .await;
    println!("   📍 结果: {}", result);

    // 测试异步状态机
    println!("   🎯 测试异步状态机...");
    let mut state_machine: AsyncStateMachine<&str, ()> = AsyncStateMachine::new("初始状态");
    println!("   🚦 初始状态: {:?}", state_machine.get_state());

    // 更新状态
    state_machine.set_state("处理中");
    println!("   🚦 更新后状态: {:?}", state_machine.get_state());
}

/// 性能优化特性演示
fn performance_optimization_demo() {
    println!("   ⚡ 性能优化特性演示...");

    // 测试零成本抽象增强
    println!("   🚀 测试零成本抽象增强...");
    let result = fast_add(10, 20);
    println!("   ➕ 快速加法: {}", result);

    // 测试内存布局优化
    println!("   🏗️ 测试内存布局优化...");
    let default_size = std::mem::size_of::<DefaultLayout>();
    let optimized_size = std::mem::size_of::<COptimizedLayout>();
    println!("   📏 默认布局大小: {} 字节", default_size);
    println!("   📏 优化布局大小: {} 字节", optimized_size);

    // 测试编译时计算增强
    println!("   🧮 测试编译时计算增强...");
    println!("   📊 10的阶乘: {}", FACTORIAL_10);
    println!("   🔢 17是否为素数: {}", PRIME_17);
}

/// 综合应用场景演示
async fn comprehensive_application_demo() {
    println!("   🌟 综合应用场景演示...");

    // 模拟高性能数据处理管道
    println!("   🔄 创建高性能数据处理管道...");

    // 1. 创建异步处理器
    let processor = TextProcessor;

    // 2. 创建异步状态机
    let mut pipeline_state: AsyncStateMachine<&str, ()> = AsyncStateMachine::new("就绪");

    // 3. 执行综合处理流程
    println!("   📥 开始数据处理...");

    // 并行处理多个数据块
    let data_chunks = vec![
        b"data_chunk_1".to_vec(),
        b"data_chunk_2".to_vec(),
        b"data_chunk_3".to_vec(),
    ];

    let processing_futures: Vec<_> = data_chunks
        .iter()
        .map(|chunk| processor.process(chunk))
        .collect();

    let results = futures::future::join_all(processing_futures).await;
    println!("   📤 并行处理完成，结果数量: {}", results.len());

    // 状态机处理
    pipeline_state.set_state("处理完成");
    println!("   🚦 管道状态: {:?}", pipeline_state.get_state());

    // 使用常量泛型进行编译时优化
    let mut optimized_matrix: Matrix<u8, 4, 4> = Matrix::new();
    for row in 0..4 {
        for col in 0..4 {
            optimized_matrix.set(row, col, (row * 4 + col) as u8);
        }
    }

    println!("   📐 4x4优化矩阵创建完成");
    println!("   📏 矩阵大小: {} 元素", calculate_matrix_size::<4, 4>());

    println!("   ✅ 综合应用场景演示完成！");
}
