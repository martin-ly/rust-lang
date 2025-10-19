# C12_Model 综合使用指南

## 📚 目录

- [C12_Model 综合使用指南](#c12_model-综合使用指南)

---

## 1. 异步模型与流量控制

### 1.1 令牌桶限流器

令牌桶允许突发流量，适合API限流场景。

```rust
use c12_model::{TokenBucket, AsyncResult};

async fn api_rate_limiting() -> AsyncResult<()> {
    // 创建令牌桶: 每秒生成100个令牌，桶容量200
    let rate_limiter = TokenBucket::new(100.0, 200);
    
    // 处理请求
    for i in 0..150 {
        match rate_limiter.try_acquire(1) {
            Ok(()) => {
                println!("Request {} accepted", i);
                // 处理请求...
            }
            Err(e) => {
                println!("Request {} rejected: {}", i, e);
                // 等待令牌补充
                #[cfg(feature = "tokio-adapter")]
                rate_limiter.acquire(1).await?;
            }
        }
    }
    
    Ok(())
}

// 批量操作
async fn batch_processing() -> AsyncResult<()> {
    let rate_limiter = TokenBucket::new(50.0, 100);
    
    // 一次性获取10个令牌处理批量任务
    rate_limiter.try_acquire(10)?;
    println!("Processing batch of 10 items");
    
    Ok(())
}
```

### 1.2 漏桶流量整形

漏桶强制恒定输出速率，适合网络流量整形。

```rust
use c12_model::{LeakyBucket, AsyncResult};

async fn network_traffic_shaping() -> AsyncResult<()> {
    // 创建漏桶: 每秒漏出50个数据包，容量1000
    let shaper = LeakyBucket::new(50.0, 1000);
    
    // 突发流量
    let burst_packets = vec![100, 200, 300, 400];
    
    for packet_count in burst_packets {
        match shaper.try_add(packet_count) {
            Ok(()) => {
                println!("Added {} packets, current size: {}", 
                         packet_count, shaper.size());
            }
            Err(e) => {
                println!("Bucket full: {}", e);
                // 等待桶漏出
                #[cfg(feature = "tokio-adapter")]
                shaper.add(packet_count).await?;
            }
        }
    }
    
    Ok(())
}
```

### 1.3 滑动窗口限流

精确的时间窗口控制，适合精确限流场景。

```rust
use c12_model::SlidingWindowRateLimiter;
use std::time::Duration;

fn sliding_window_demo() -> AsyncResult<()> {
    // 1分钟内最多100个请求
    let limiter = SlidingWindowRateLimiter::new(
        Duration::from_secs(60),
        100
    );
    
    for i in 0..120 {
        match limiter.try_acquire() {
            Ok(()) => {
                println!("Request {} passed, current count: {}", 
                         i, limiter.current_count());
            }
            Err(e) => {
                println!("Request {} blocked: {}", i, e);
            }
        }
    }
    
    Ok(())
}
```

### 1.4 自适应限流

根据系统负载动态调整限流策略。

```rust
use c12_model::AdaptiveRateLimiter;
use std::time::Duration;

fn adaptive_rate_limiting() -> AsyncResult<()> {
    // 基础速率100，范围10-500，每5秒调整一次
    let limiter = AdaptiveRateLimiter::new(
        100.0,  // base_rate
        10.0,   // min_rate
        500.0,  // max_rate
        Duration::from_secs(5)
    );
    
    // 模拟请求处理
    for _ in 0..1000 {
        if process_request().is_ok() {
            limiter.record_success()?;
        } else {
            limiter.record_failure()?;
        }
        
        println!("Current rate: {}", limiter.current_rate());
    }
    
    Ok(())
}

fn process_request() -> Result<(), ()> {
    // 模拟请求处理
    use fastrand::Rng;
    let rng = Rng::new();
    if rng.f64() > 0.1 { Ok(()) } else { Err(()) }
}
```

---

## 2. 算法模型应用

### 2.1 排序算法性能对比

```rust
use c12_model::{SortingAlgorithms, AlgorithmMetrics, AlgorithmResult};

fn sorting_benchmark() -> AlgorithmResult<()> {
    let mut data = vec![64, 34, 25, 12, 22, 11, 90, 88, 45, 50, 23, 36, 18];
    
    // 快速排序
    let mut quicksort_metrics = AlgorithmMetrics::new();
    let mut qs_data = data.clone();
    SortingAlgorithms::quicksort(&mut qs_data, &mut quicksort_metrics)?;
    
    println!("QuickSort:");
    println!("  Comparisons: {}", quicksort_metrics.comparison_count);
    println!("  Swaps: {}", quicksort_metrics.swap_count);
    println!("  Time: {:?}", quicksort_metrics.execution_time);
    
    // 归并排序
    let mut mergesort_metrics = AlgorithmMetrics::new();
    let mut ms_data = data.clone();
    SortingAlgorithms::mergesort(&mut ms_data, &mut mergesort_metrics)?;
    
    println!("MergeSort:");
    println!("  Comparisons: {}", mergesort_metrics.comparison_count);
    println!("  Time: {:?}", mergesort_metrics.execution_time);
    
    // 堆排序
    let mut heapsort_metrics = AlgorithmMetrics::new();
    let mut hs_data = data.clone();
    SortingAlgorithms::heapsort(&mut hs_data, &mut heapsort_metrics)?;
    
    println!("HeapSort:");
    println!("  Comparisons: {}", heapsort_metrics.comparison_count);
    println!("  Time: {:?}", heapsort_metrics.execution_time);
    
    Ok(())
}
```

### 2.2 动态规划算法

```rust
use c12_model::{DynamicProgrammingAlgorithms, AlgorithmMetrics};

fn dynamic_programming_examples() -> AlgorithmResult<()> {
    let mut metrics = AlgorithmMetrics::new();
    
    // 斐波那契数列
    let fib_result = DynamicProgrammingAlgorithms::fibonacci_dp(20, &mut metrics)?;
    println!("Fibonacci(20) = {}", fib_result);
    
    // 0-1背包问题
    let weights = vec![2, 3, 4, 5];
    let values = vec![3, 4, 5, 6];
    let capacity = 8;
    
    let knapsack_result = DynamicProgrammingAlgorithms::knapsack_01(
        &weights, &values, capacity, &mut metrics
    )?;
    println!("Knapsack max value: {}", knapsack_result);
    
    // 最长公共子序列
    let seq1 = "ABCDGH";
    let seq2 = "AEDFHR";
    let lcs_len = DynamicProgrammingAlgorithms::longest_common_subsequence(
        seq1, seq2, &mut metrics
    )?;
    println!("LCS length: {}", lcs_len);
    
    // 编辑距离
    let str1 = "kitten";
    let str2 = "sitting";
    let distance = DynamicProgrammingAlgorithms::edit_distance(
        str1, str2, &mut metrics
    )?;
    println!("Edit distance: {}", distance);
    
    Ok(())
}
```

### 2.3 算法关系分析

```rust
use c12_model::{AlgorithmRelationshipAnalyzer, AlgorithmCategory};

fn algorithm_analysis() -> AlgorithmResult<()> {
    let analyzer = AlgorithmRelationshipAnalyzer::new();
    
    // 分析排序算法关系
    let sorting_analysis = analyzer.analyze_category(AlgorithmCategory::Sorting)?;
    println!("Sorting algorithms analysis:");
    for (name, complexity) in sorting_analysis.iter() {
        println!("  {}: {:?}", name, complexity);
    }
    
    // 比较两个算法
    let comparison = analyzer.compare_algorithms("quicksort", "mergesort")?;
    println!("\nQuickSort vs MergeSort:");
    println!("  Time complexity: {:?} vs {:?}", 
             comparison.first_time, comparison.second_time);
    println!("  Space complexity: {:?} vs {:?}", 
             comparison.first_space, comparison.second_space);
    
    // 获取优化建议
    let suggestions = analyzer.suggest_optimizations("bubblesort")?;
    println!("\nOptimization suggestions for BubbleSort:");
    for suggestion in suggestions {
        println!("  - {}", suggestion);
    }
    
    Ok(())
}
```

---

## 3. 分布式系统模型

### 3.1 一致性模型

```rust
use c12_model::{DistributedSystemManager, DistributedSystemConfig, ConsistencyLevel};

fn distributed_consistency() -> AsyncResult<()> {
    let config = DistributedSystemConfig {
        node_count: 5,
        replication_factor: 3,
        consistency_level: ConsistencyLevel::Strong,
        ..Default::default()
    };
    
    let mut manager = DistributedSystemManager::new(config);
    
    // 强一致性写入
    manager.write("key1", "value1", ConsistencyLevel::Strong)?;
    
    // 读取数据
    let value = manager.read("key1", ConsistencyLevel::Strong)?;
    println!("Read value: {:?}", value);
    
    // 最终一致性写入（更快但可能短暂不一致）
    manager.write("key2", "value2", ConsistencyLevel::Eventual)?;
    
    Ok(())
}
```

### 3.2 CAP定理分析

```rust
use c12_model::{CAPTheoremAnalyzer, CAPProperty};

fn cap_theorem_demo() -> AsyncResult<()> {
    let analyzer = CAPTheoremAnalyzer::new();
    
    // 分析CP系统（一致性+分区容错）
    let cp_tradeoffs = analyzer.analyze_tradeoffs(
        vec![CAPProperty::Consistency, CAPProperty::PartitionTolerance]
    )?;
    println!("CP System tradeoffs: {:?}", cp_tradeoffs);
    
    // 分析AP系统（可用性+分区容错）
    let ap_tradeoffs = analyzer.analyze_tradeoffs(
        vec![CAPProperty::Availability, CAPProperty::PartitionTolerance]
    )?;
    println!("AP System tradeoffs: {:?}", ap_tradeoffs);
    
    // 模拟网络分区
    analyzer.simulate_partition()?;
    
    Ok(())
}
```

### 3.3 共识算法（简化Raft）

```rust
use c12_model::{ConsensusAlgorithm, DistributedNode};

async fn raft_consensus() -> AsyncResult<()> {
    let nodes = vec![
        DistributedNode::new("node1".to_string()),
        DistributedNode::new("node2".to_string()),
        DistributedNode::new("node3".to_string()),
    ];
    
    let mut consensus = ConsensusAlgorithm::new(nodes);
    
    // 领导者选举
    let leader = consensus.elect_leader().await?;
    println!("Elected leader: {}", leader);
    
    // 提交日志条目
    consensus.append_entry("SET x = 10".to_string()).await?;
    consensus.append_entry("SET y = 20".to_string()).await?;
    
    // 等待复制完成
    consensus.wait_for_replication().await?;
    
    println!("Log replicated successfully");
    
    Ok(())
}
```

### 3.4 负载均衡

```rust
use c12_model::{LoadBalancer, DistributedLoadBalancer};

fn load_balancing() -> AsyncResult<()> {
    let servers = vec![
        "server1:8080".to_string(),
        "server2:8080".to_string(),
        "server3:8080".to_string(),
    ];
    
    let mut lb = DistributedLoadBalancer::new(servers);
    
    // 轮询策略
    lb.set_strategy("round_robin");
    for _ in 0..10 {
        let server = lb.select_server()?;
        println!("Selected: {}", server);
    }
    
    // 最少连接策略
    lb.set_strategy("least_connections");
    lb.record_connection("server1:8080", 5);
    lb.record_connection("server2:8080", 3);
    lb.record_connection("server3:8080", 7);
    
    let server = lb.select_server()?;
    println!("Least connections server: {}", server);
    
    // 一致性哈希
    lb.set_strategy("consistent_hashing");
    let server = lb.select_server_for_key("user:12345")?;
    println!("Consistent hash server: {}", server);
    
    Ok(())
}
```

---

## 4. 微服务架构模型

### 4.1 服务发现

```rust
use c12_model::{ServiceRegistry, ServiceInstance};

fn service_discovery() -> AsyncResult<()> {
    let mut registry = ServiceRegistry::new();
    
    // 注册服务
    let service1 = ServiceInstance {
        id: "user-service-1".to_string(),
        name: "user-service".to_string(),
        host: "localhost".to_string(),
        port: 8081,
        metadata: Default::default(),
    };
    
    registry.register(service1.clone())?;
    
    // 发现服务
    let instances = registry.discover("user-service")?;
    println!("Found {} instances of user-service", instances.len());
    
    // 健康检查
    registry.health_check(&service1.id)?;
    
    // 注销服务
    registry.deregister(&service1.id)?;
    
    Ok(())
}
```

### 4.2 熔断器模式

```rust
use c12_model::CircuitBreaker;
use std::time::Duration;

async fn circuit_breaker_pattern() -> AsyncResult<()> {
    let mut breaker = CircuitBreaker::new(
        5,                          // 失败阈值
        Duration::from_secs(30),    // 超时时间
        Duration::from_secs(60),    // 恢复时间
    );
    
    // 正常调用
    match breaker.call(|| external_service_call()).await {
        Ok(result) => println!("Success: {}", result),
        Err(e) => println!("Failed: {}", e),
    }
    
    // 模拟多次失败
    for _ in 0..6 {
        let _ = breaker.call(|| failing_service_call()).await;
    }
    
    // 此时熔断器打开，快速失败
    match breaker.call(|| external_service_call()).await {
        Ok(_) => unreachable!(),
        Err(e) => println!("Circuit open: {}", e),
    }
    
    // 等待恢复时间后进入半开状态
    tokio::time::sleep(Duration::from_secs(61)).await;
    
    match breaker.call(|| external_service_call()).await {
        Ok(result) => println!("Half-open success: {}", result),
        Err(e) => println!("Half-open failed: {}", e),
    }
    
    Ok(())
}

async fn external_service_call() -> Result<String, String> {
    Ok("Success".to_string())
}

async fn failing_service_call() -> Result<String, String> {
    Err("Service unavailable".to_string())
}
```

### 4.3 API网关

```rust
use c12_model::{ApiGateway, RateLimiter};

async fn api_gateway_demo() -> AsyncResult<()> {
    let mut gateway = ApiGateway::new();
    
    // 配置路由
    gateway.add_route("/api/users", "http://user-service:8081")?;
    gateway.add_route("/api/orders", "http://order-service:8082")?;
    
    // 添加限流
    let rate_limiter = RateLimiter::new(100, Duration::from_secs(1));
    gateway.add_middleware("rate_limit", Box::new(rate_limiter))?;
    
    // 处理请求
    let response = gateway.handle_request("/api/users", "GET", None).await?;
    println!("Response: {:?}", response);
    
    Ok(())
}
```

---

## 5. 并行并发模型

### 5.1 Actor模型

```rust
use c12_model::{ActorSystem, ActorMessage, ActorBehavior};

async fn actor_model_demo() -> AsyncResult<()> {
    let mut system = ActorSystem::new();
    
    // 创建Actor
    let actor_ref = system.spawn_actor(
        "counter".to_string(),
        MyCounterBehavior::new()
    ).await?;
    
    // 发送消息
    actor_ref.send(ActorMessage::new("increment".to_string())).await?;
    actor_ref.send(ActorMessage::new("increment".to_string())).await?;
    actor_ref.send(ActorMessage::new("get".to_string())).await?;
    
    Ok(())
}

struct MyCounterBehavior {
    count: i32,
}

impl MyCounterBehavior {
    fn new() -> Self {
        Self { count: 0 }
    }
}

impl ActorBehavior for MyCounterBehavior {
    fn receive(&mut self, msg: ActorMessage) -> AsyncResult<()> {
        match msg.content.as_str() {
            "increment" => {
                self.count += 1;
                println!("Count incremented to {}", self.count);
            }
            "get" => {
                println!("Current count: {}", self.count);
            }
            _ => {}
        }
        Ok(())
    }
}
```

### 5.2 CSP模型

```rust
use c12_model::{CSPChannel, CSPProcess, CSPSystem};

async fn csp_model_demo() -> AsyncResult<()> {
    let system = CSPSystem::new();
    
    // 创建通道
    let (tx, rx) = CSPChannel::new(10);
    
    // 生产者进程
    let producer = CSPProcess::new("producer", async move {
        for i in 0..5 {
            tx.send(i).await?;
            println!("Produced: {}", i);
        }
        Ok(())
    });
    
    // 消费者进程
    let consumer = CSPProcess::new("consumer", async move {
        while let Ok(value) = rx.recv().await {
            println!("Consumed: {}", value);
        }
        Ok(())
    });
    
    // 运行进程
    system.run_process(producer).await?;
    system.run_process(consumer).await?;
    
    Ok(())
}
```

### 5.3 数据并行

```rust
use c12_model::DataParallelExecutor;

fn data_parallel_demo() -> AsyncResult<()> {
    let executor = DataParallelExecutor::new(4); // 4个工作线程
    
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 并行映射
    let results = executor.parallel_map(&data, |x| x * x)?;
    println!("Squared: {:?}", results);
    
    // 并行归约
    let sum = executor.parallel_reduce(&data, 0, |acc, x| acc + x)?;
    println!("Sum: {}", sum);
    
    Ok(())
}
```

---

## 6. 程序设计模型

### 6.1 函数式编程

```rust
use c12_model::{Functor, Monad, HigherOrderFunctions};

fn functional_programming() -> AsyncResult<()> {
    // Functor示例
    let nums = vec![1, 2, 3, 4, 5];
    let squared = Functor::map(nums, |x| x * x);
    println!("Squared: {:?}", squared);
    
    // Monad示例
    let result = Monad::pure(10)
        .bind(|x| Monad::pure(x + 5))
        .bind(|x| Monad::pure(x * 2));
    println!("Result: {:?}", result);
    
    // 高阶函数
    let add = |x: i32, y: i32| x + y;
    let add_five = HigherOrderFunctions::partial_application(add, 5);
    println!("5 + 3 = {}", add_five(3));
    
    // 函数组合
    let double = |x: i32| x * 2;
    let add_ten = |x: i32| x + 10;
    let composed = HigherOrderFunctions::compose(double, add_ten);
    println!("compose(double, add_ten)(5) = {}", composed(5));
    
    Ok(())
}
```

### 6.2 面向对象编程

```rust
use c12_model::{Observer, Subject, Observable};

fn object_oriented_demo() -> AsyncResult<()> {
    let mut subject = Subject::new();
    
    // 添加观察者
    let observer1 = MyObserver::new("Observer1".to_string());
    let observer2 = MyObserver::new("Observer2".to_string());
    
    subject.attach(Box::new(observer1));
    subject.attach(Box::new(observer2));
    
    // 通知所有观察者
    subject.notify("Important event occurred!")?;
    
    Ok(())
}

struct MyObserver {
    name: String,
}

impl MyObserver {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Observer for MyObserver {
    fn update(&self, message: &str) {
        println!("{} received: {}", self.name, message);
    }
}
```

---

## 7. 架构设计模型

### 7.1 分层架构

```rust
use c12_model::{ArchitectureLayer, LayeredComponent, LayerDependencyRules};

fn layered_architecture() -> AsyncResult<()> {
    let mut rules = LayerDependencyRules::new();
    
    // 定义层次
    rules.add_layer(ArchitectureLayer::Presentation);
    rules.add_layer(ArchitectureLayer::Business);
    rules.add_layer(ArchitectureLayer::Data);
    
    // 定义依赖规则
    rules.allow_dependency(
        ArchitectureLayer::Presentation,
        ArchitectureLayer::Business
    )?;
    rules.allow_dependency(
        ArchitectureLayer::Business,
        ArchitectureLayer::Data
    )?;
    
    // 验证组件
    let component = LayeredComponent::new(
        "UserController".to_string(),
        ArchitectureLayer::Presentation
    );
    
    rules.validate_component(&component)?;
    
    Ok(())
}
```

### 7.2 六边形架构

```rust
use c12_model::{HexagonalCore, InboundPort, OutboundPort, Adapter};

fn hexagonal_architecture() -> AsyncResult<()> {
    let mut core = HexagonalCore::new();
    
    // 定义入站端口
    let user_service_port = InboundPort::new("UserService".to_string());
    core.register_inbound_port(user_service_port)?;
    
    // 定义出站端口
    let db_port = OutboundPort::new("DatabasePort".to_string());
    core.register_outbound_port(db_port)?;
    
    // 添加适配器
    let rest_adapter = Adapter::new("RestAdapter".to_string());
    let postgres_adapter = Adapter::new("PostgresAdapter".to_string());
    
    core.connect_adapter("UserService", rest_adapter)?;
    core.connect_adapter("DatabasePort", postgres_adapter)?;
    
    Ok(())
}
```

### 7.3 事件驱动架构

```rust
use c12_model::{EventBus, Event, EventHandler};

async fn event_driven_architecture() -> AsyncResult<()> {
    let mut event_bus = EventBus::new();
    
    // 注册事件处理器
    event_bus.subscribe("UserCreated", Box::new(UserCreatedHandler))?;
    event_bus.subscribe("OrderPlaced", Box::new(OrderPlacedHandler))?;
    
    // 发布事件
    let user_event = Event::new(
        "UserCreated".to_string(),
        serde_json::json!({"user_id": 123, "email": "user@example.com"})
    );
    
    event_bus.publish(user_event).await?;
    
    let order_event = Event::new(
        "OrderPlaced".to_string(),
        serde_json::json!({"order_id": 456, "amount": 99.99})
    );
    
    event_bus.publish(order_event).await?;
    
    Ok(())
}

struct UserCreatedHandler;
struct OrderPlacedHandler;

impl EventHandler for UserCreatedHandler {
    fn handle(&self, event: &Event) -> AsyncResult<()> {
        println!("Handling UserCreated: {:?}", event.data);
        // 发送欢迎邮件、创建默认设置等
        Ok(())
    }
}

impl EventHandler for OrderPlacedHandler {
    fn handle(&self, event: &Event) -> AsyncResult<()> {
        println!("Handling OrderPlaced: {:?}", event.data);
        // 处理支付、更新库存等
        Ok(())
    }
}
```

---

## 8. 模型组合与集成

### 8.1 微服务 + 事件驱动 + 熔断器

```rust
use c12_model::*;

async fn microservice_with_resilience() -> AsyncResult<()> {
    // 服务注册
    let mut registry = ServiceRegistry::new();
    let service = ServiceInstance {
        id: "payment-service".to_string(),
        name: "payment".to_string(),
        host: "localhost".to_string(),
        port: 8083,
        metadata: Default::default(),
    };
    registry.register(service)?;
    
    // 熔断器保护
    let mut breaker = CircuitBreaker::new(
        3,
        Duration::from_secs(10),
        Duration::from_secs(30)
    );
    
    // 事件总线
    let mut event_bus = EventBus::new();
    event_bus.subscribe("PaymentCompleted", Box::new(PaymentHandler))?;
    
    // 处理支付请求（带熔断保护）
    match breaker.call(|| process_payment(100.0)).await {
        Ok(result) => {
            let event = Event::new(
                "PaymentCompleted".to_string(),
                serde_json::json!({"amount": 100.0, "status": "success"})
            );
            event_bus.publish(event).await?;
        }
        Err(e) => {
            println!("Payment failed: {}", e);
        }
    }
    
    Ok(())
}

async fn process_payment(amount: f64) -> Result<String, String> {
    // 模拟支付处理
    Ok(format!("Payment of ${} processed", amount))
}

struct PaymentHandler;

impl EventHandler for PaymentHandler {
    fn handle(&self, event: &Event) -> AsyncResult<()> {
        println!("Payment completed: {:?}", event.data);
        Ok(())
    }
}
```

### 8.2 分布式算法 + 限流

```rust
use c12_model::*;

async fn distributed_rate_limited_processing() -> AsyncResult<()> {
    // 分布式系统配置
    let config = DistributedSystemConfig {
        node_count: 3,
        replication_factor: 2,
        consistency_level: ConsistencyLevel::Eventual,
        ..Default::default()
    };
    
    let mut system = DistributedSystemManager::new(config);
    
    // 令牌桶限流
    let rate_limiter = TokenBucket::new(10.0, 50);
    
    // 处理分布式任务（带限流）
    for i in 0..100 {
        if rate_limiter.try_acquire(1).is_ok() {
            let key = format!("task_{}", i);
            let value = format!("data_{}", i);
            system.write(&key, &value, ConsistencyLevel::Eventual)?;
            println!("Task {} processed", i);
        } else {
            println!("Rate limit exceeded for task {}", i);
            #[cfg(feature = "tokio-adapter")]
            rate_limiter.acquire(1).await?;
        }
    }
    
    Ok(())
}
```

### 8.3 函数式 + 并行 + 算法

```rust
use c12_model::*;

fn functional_parallel_algorithms() -> AsyncResult<()> {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 并行执行器
    let executor = DataParallelExecutor::new(4);
    
    // 函数式转换
    let processed = executor.parallel_map(&data, |x| {
        let squared = x * x;
        let plus_ten = squared + 10;
        plus_ten
    })?;
    
    println!("Processed data: {:?}", processed);
    
    // 并行排序
    let mut to_sort = vec![64, 34, 25, 12, 22, 11, 90];
    let mut metrics = AlgorithmMetrics::new();
    
    SortingAlgorithms::quicksort(&mut to_sort, &mut metrics)?;
    println!("Sorted: {:?}", to_sort);
    println!("Metrics: {:?}", metrics);
    
    Ok(())
}
```

---

## 🎯 最佳实践总结

### 1. 选择合适的限流策略

- **API限流**: 令牌桶（允许突发）
- **网络流量**: 漏桶（平滑流量）
- **精确控制**: 滑动窗口
- **动态调整**: 自适应限流器

### 2. 分布式系统设计

- **强一致性**: 使用Raft/Paxos，牺牲性能
- **高可用**: 使用最终一致性，接受短暂不一致
- **负载均衡**: 根据场景选择策略

### 3. 微服务容错

- **熔断器**: 防止级联故障
- **限流器**: 保护服务过载
- **重试**: 提高可靠性（带指数退避）

### 4. 并发模型选择

- **无共享状态**: Actor模型
- **结构化并发**: CSP模型
- **高性能计算**: 共享内存 + 无锁结构

### 5. 架构模式

- **单体应用**: 分层架构
- **可测试性**: 六边形架构
- **事件驱动**: EDA + CQRS
- **插件化**: 微内核架构

---

**版本**: 1.0.0  
**Rust版本**: 1.90+  
**最后更新**: 2025-10-01
