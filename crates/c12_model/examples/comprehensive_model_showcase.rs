//! 综合模型展示示例
//! 
//! 本示例展示了 c12_model 中各种模型的使用方法和相互关系

use c12_model::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== C12 Model 综合展示 ===\n");

    // 1. 语义模型示例
    semantic_models_demo()?;
    
    // 2. 异步模型示例
    // async_models_demo().await?;
    
    // 3. 算法模型示例
    algorithm_models_demo()?;
    
    // 4. 分布式模型示例
    distributed_models_demo()?;
    
    // 5. 并发模型示例
    concurrent_models_demo()?;
    
    // 6. 程序设计模型示例
    programming_models_demo()?;
    
    // 7. 架构设计模型示例
    architecture_models_demo()?;

    println!("\n=== 所有示例完成 ===");
    Ok(())
}

/// 1. 语义模型示例
fn semantic_models_demo() -> SemanticResult<()> {
    println!("--- 1. 语义模型 ---");
    
    // 操作语义: 大步语义求值
    let expr = Expression::BinOp {
        op: BinaryOperator::Mul,
        left: Box::new(Expression::BinOp {
            op: BinaryOperator::Add,
            left: Box::new(Expression::Int(2)),
            right: Box::new(Expression::Int(3)),
        }),
        right: Box::new(Expression::Int(4)),
    };
    
    let env = Environment::new();
    let result = BigStepSemantics::eval_expr(&expr, &env)?;
    println!("大步语义求值: (2 + 3) * 4 = {:?}", result);
    
    // Lambda 演算
    let lambda_expr = Expression::App {
        func: Box::new(Expression::Lambda {
            param: "x".to_string(),
            body: Box::new(Expression::BinOp {
                op: BinaryOperator::Add,
                left: Box::new(Expression::Var("x".to_string())),
                right: Box::new(Expression::Int(10)),
            }),
        }),
        arg: Box::new(Expression::Int(5)),
    };
    
    let lambda_result = BigStepSemantics::eval_expr(&lambda_expr, &env)?;
    println!("Lambda 计算: (λx. x + 10) 5 = {:?}", lambda_result);
    
    // 指称语义
    let denotation = DenotationalSemantics::denote_expr(&expr);
    let denot_result = denotation(&env)?;
    println!("指称语义结果: {:?}", denot_result);
    
    // 验证操作语义和指称语义等价
    let equivalent = SemanticEquivalenceAnalyzer::prove_operational_denotational_equivalence(
        &expr, &env
    )?;
    println!("操作语义 ≡ 指称语义: {}\n", equivalent);
    
    Ok(())
}

/// 3. 算法模型示例
fn algorithm_models_demo() -> AlgorithmResult<()> {
    println!("--- 3. 算法模型 ---");
    
    // 排序算法
    let mut data = vec![64, 34, 25, 12, 22, 11, 90];
    let mut metrics = AlgorithmMetrics::new();
    
    SortingAlgorithms::quicksort(&mut data, &mut metrics)?;
    println!("快速排序结果: {:?}", data);
    println!("比较次数: {}, 交换次数: {}", 
             metrics.comparison_count, metrics.swap_count);
    
    // 图算法: Floyd-Warshall
    let vertices = vec!["A", "B", "C", "D"];
    let edges = vec![
        ("A", "B", 1.0),
        ("A", "C", 4.0),
        ("B", "C", 2.0),
        ("B", "D", 5.0),
        ("C", "D", 1.0),
    ];
    
    let mut graph_metrics = AlgorithmMetrics::new();
    let distances = GreedyAlgorithms::floyd_warshall(&vertices, &edges, &mut graph_metrics)?;
    println!("全源最短路径计算完成");
    println!("A 到 D 的最短距离: {:?}", distances.get(&("A", "D")));
    
    // 字符串算法: KMP
    let text = "ABABDABACDABABCABAB";
    let pattern = "ABABCABAB";
    let mut string_metrics = AlgorithmMetrics::new();
    let positions = StringAlgorithms::kmp_search(text, pattern, &mut string_metrics)?;
    println!("KMP 搜索: 在位置 {:?} 找到模式", positions);
    
    // 数学算法
    let mut math_metrics = AlgorithmMetrics::new();
    let gcd = MathematicalAlgorithms::gcd(48, 18, &mut math_metrics)?;
    println!("GCD(48, 18) = {}", gcd);
    
    let primes = MathematicalAlgorithms::sieve_of_eratosthenes(30, &mut math_metrics)?;
    println!("30以内的素数: {:?}\n", primes);
    
    Ok(())
}

/// 4. 分布式模型示例
fn distributed_models_demo() -> DistributedResult<()> {
    println!("--- 4. 分布式模型 ---");
    
    // 创建分布式系统
    let config = DistributedSystemConfig::default();
    let system = DistributedSystemManager::new(config);
    
    let node1 = DistributedNode::new("node1".to_string(), "127.0.0.1:8001".parse().unwrap());
    let node2 = DistributedNode::new("node2".to_string(), "127.0.0.1:8002".parse().unwrap());
    let node3 = DistributedNode::new("node3".to_string(), "127.0.0.1:8003".parse().unwrap());
    
    system.add_node(node1)?;
    system.add_node(node2)?;
    system.add_node(node3)?;
    
    let status = system.get_system_status();
    println!("分布式系统节点数: {}", status.total_nodes);
    
    // CAP 定理分析
    let analysis = CAPTheoremAnalyzer::analyze_tradeoffs(&[
        CAPProperty::Consistency,
        CAPProperty::PartitionTolerance
    ]);
    
    println!("CAP 分析:");
    println!("  选择的属性: {:?}", analysis.selected_properties);
    println!("  牺牲的属性: {:?}", analysis.sacrificed_property);
    println!("  权衡建议: {:?}", analysis.tradeoffs.first().unwrap_or(&"".to_string()));
    
    // Paxos 共识
    let paxos = PaxosProtocol::new("proposer1".to_string());
    paxos.add_participant("acceptor1".to_string())?;
    paxos.add_participant("acceptor2".to_string())?;
    paxos.add_participant("acceptor3".to_string())?;
    
    println!("Paxos 协议初始化完成");
    println!("节点ID: {}\n", paxos.node_id());
    
    Ok(())
}

/// 5. 并发模型示例
fn concurrent_models_demo() -> ConcurrentResult<()> {
    println!("--- 5. 并发模型 ---");
    
    // Actor 模型
    let _actor_system = ActorSystem::new("MainSystem".to_string());
    println!("Actor 系统创建完成");
    
    // CSP 模型
    let _csp_system = CSPSystem::new();
    println!("CSP 系统创建完成");
    
    // 任务并行
    let _executor = TaskParallelExecutor::new(4);
    println!("任务并行执行器 (4线程) 创建完成");
    
    // 工作窃取调度器
    let _scheduler = WorkStealingScheduler::new(4);
    println!("工作窃取调度器 (4工作线程) 创建完成");
    
    // 并行模式分析
    let patterns = vec![
        ParallelPattern::DataParallel,
        ParallelPattern::TaskParallel,
        ParallelPattern::Pipeline,
        ParallelPattern::DivideAndConquer,
        ParallelPattern::MapReduce,
    ];
    
    println!("\n并行模式特征:");
    for pattern in patterns {
        let characteristics = ParallelPatternAnalyzer::analyze_pattern(&pattern);
        println!("  {:?}:", characteristics.pattern);
        println!("    描述: {}", characteristics.description);
        println!("    可扩展性: {:?}", characteristics.scalability);
    }
    
    println!();
    Ok(())
}

/// 6. 程序设计模型示例
fn programming_models_demo() -> ProgramResult<()> {
    println!("--- 6. 程序设计模型 ---");
    
    // 函数式编程: Functor trait (使用 Option 作为示例)
    use Functor as FunctorTrait;
    let functor = Some(42);
    let mapped = functor.fmap(|x| x * 2);
    println!("Functor map: 42 * 2 = {:?}", mapped);
    
    // Monad trait (Option 本身实现了 Monad trait，但没有 bind 方法，使用 and_then)
    let monad = Some(10);
    let result = monad.and_then(|x| Some(x + 5));
    println!("Monad (Option) flatMap: 10 + 5 = {:?}", result);
    
    // 不可变列表 (ImmutableList 实现了 map 和 fold)
    let numbers = ImmutableList::from_vec(vec![1, 2, 3, 4, 5]);
    let doubled = numbers.map(|x| x * 2);
    println!("ImmutableList map: [1,2,3,4,5] -> 长度 {}", doubled.len());
    
    let sum: i32 = numbers.fold(0, |acc, x| acc + x);
    println!("ImmutableList fold: sum = {}", sum);
    
    // 反应式流
    let _stream = ReactiveStream::<i32>::new(100);
    println!("反应式流创建完成 (缓冲区: 100)");
    
    // 数据流编程
    let mut _graph: DataflowGraph<i32> = DataflowGraph::new();
    println!("数据流图创建完成");
    
    // 数据流管道
    let mut pipeline = DataflowPipeline::new();
    pipeline
        .add_stage(|x: i32| Ok(x * 2))
        .add_stage(|x: i32| Ok(x + 10))
        .add_stage(|x: i32| Ok(x / 2));
    
    let pipeline_result = pipeline.execute(5)?;
    println!("数据流管道: ((5 * 2) + 10) / 2 = {}\n", pipeline_result);
    
    Ok(())
}

/// 7. 架构设计模型示例
fn architecture_models_demo() -> ArchitectureResult<()> {
    println!("--- 7. 架构设计模型 ---");
    
    // 事件驱动架构 (需要具体的事件类型)
    // EventBus 是泛型，需要指定事件类型，这里简化展示
    println!("事件总线 (EventBus<E>) 可用于发布-订阅模式");
    
    // CQRS 模型 (需要具体的读写模型类型)
    // 示例：使用简单的类型
    let write_model = Vec::<String>::new();
    let read_model = Vec::<String>::new();
    let _cqrs = CQRSModel::new(write_model, read_model);
    println!("CQRS 模型创建完成");
    
    // 管道过滤器架构
    let _pipeline = PipelineArchitecture::<i32>::new();
    println!("管道架构创建完成");
    
    // P2P 网络
    let _p2p_network = P2PNetwork::new();
    println!("P2P 网络创建完成");
    
    // 架构模式分析
    let patterns = vec![
        ArchitecturePattern::Layered,
        ArchitecturePattern::Hexagonal,
        ArchitecturePattern::EventDriven,
        ArchitecturePattern::CQRS,
        ArchitecturePattern::Microservices,
    ];
    
    println!("\n架构模式特征:");
    for pattern in patterns {
        let characteristics = ArchitecturePatternAnalyzer::analyze(&pattern);
        println!("  {:?}:", characteristics.pattern);
        println!("    耦合度: {:?}", characteristics.coupling);
        println!("    可扩展性: {:?}", characteristics.scalability);
        println!("    可测试性: {:?}", characteristics.testability);
        println!("    用例: {:?}", characteristics.use_cases.first().unwrap_or(&"".to_string()));
    }
    
    println!();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semantic_equivalence() {
        let e1 = Expression::BinOp {
            op: BinaryOperator::Add,
            left: Box::new(Expression::Int(2)),
            right: Box::new(Expression::Int(3)),
        };
        
        let e2 = Expression::BinOp {
            op: BinaryOperator::Add,
            left: Box::new(Expression::Int(3)),
            right: Box::new(Expression::Int(2)),
        };
        
        let env = Environment::new();
        let equivalent = SemanticEquivalenceAnalyzer::are_expressions_equivalent(&e1, &e2, &env).unwrap();
        assert!(equivalent);
    }

    #[test]
    fn test_algorithm_complexity() {
        let mut data = vec![5, 2, 8, 1, 9];
        let mut metrics = AlgorithmMetrics::new();
        
        SortingAlgorithms::quick_sort(&mut data, &mut metrics).unwrap();
        
        assert!(metrics.comparisons > 0);
        assert_eq!(data, vec![1, 2, 5, 8, 9]);
    }

    #[test]
    fn test_distributed_cap() {
        let analyzer = CAPTheoremAnalyzer::new();
        let analysis = analyzer.analyze_system(
            ConsistencyLevel::Strong,
            vec![CAPProperty::Consistency, CAPProperty::Availability],
        ).unwrap();
        
        assert_eq!(analysis.selected_properties.len(), 2);
        assert_eq!(analysis.sacrificed_property, Some(CAPProperty::PartitionTolerance));
    }

    #[test]
    fn test_parallel_patterns() {
        let characteristics = ParallelPatternAnalyzer::analyze_pattern(&ParallelPattern::MapReduce);
        assert_eq!(characteristics.pattern, ParallelPattern::MapReduce);
        assert!(!characteristics.description.is_empty());
    }

    #[test]
    fn test_programming_paradigms() {
        use Functor as FunctorTrait;
        let functor = Some(42);
        let result = functor.fmap(|x| x * 2);
        assert_eq!(result, Some(84));
    }
}

