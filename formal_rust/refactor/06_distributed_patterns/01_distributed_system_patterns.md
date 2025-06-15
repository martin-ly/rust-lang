# 06. 分布式系统模式

## 目录

### 1. 分布式系统基础
#### 1.1 分布式系统概念
#### 1.2 一致性模型
#### 1.3 故障模式

### 2. 服务发现模式
#### 2.1 服务注册
#### 2.2 服务发现
#### 2.3 健康检查
#### 2.4 Rust实现

### 3. 熔断器模式
#### 3.1 熔断器状态机
#### 3.2 故障检测
#### 3.3 恢复机制
#### 3.4 Rust实现

### 4. API网关模式
#### 4.1 路由功能
#### 4.2 负载均衡
#### 4.3 认证授权
#### 4.4 Rust实现

### 5. Saga模式
#### 5.1 分布式事务
#### 5.2 补偿机制
#### 5.3 协调策略
#### 5.4 Rust实现

---

## 1. 分布式系统基础

### 1.1 分布式系统概念

**分布式系统定义**：
```
DistributedSystem : [Node] → System
∀nodes ∈ [Node] | DistributedSystem(nodes) = {
  nodes: nodes,
  communication: Network,
  coordination: Protocol
}
```

**系统属性**：
```
SystemProperties : DistributedSystem → Properties
∀system ∈ DistributedSystem | SystemProperties(system) = {
  scalability: horizontal_scaling(system),
  fault_tolerance: fault_handling(system),
  consistency: data_consistency(system)
}
```

### 1.2 一致性模型

**强一致性**：
```
StrongConsistency : System → Boolean
∀system ∈ System | StrongConsistency(system) = 
  ∀read, write ∈ Operation | read_after_write(read, write) → read.value = write.value
```

**最终一致性**：
```
EventualConsistency : System → Boolean
∀system ∈ System | EventualConsistency(system) = 
  ∀replicas ∈ [Replica] | eventually_converge(replicas)
```

### 1.3 故障模式

**故障类型**：
```
FaultTypes : Node → FaultType
∀node ∈ Node | FaultTypes(node) ∈ {
  Crash, Byzantine, Network, Performance
}
```

---

## 2. 服务发现模式

### 2.1 服务注册

**服务注册模型**：
```
ServiceRegistration : Service → Registration
∀service ∈ Service | ServiceRegistration(service) = {
  service_id: service.id,
  endpoint: service.endpoint,
  metadata: service.metadata,
  health_status: service.health
}
```

**注册中心**：
```
Registry : [Service] → Registry
∀services ∈ [Service] | Registry(services) = {
  services: services,
  register: λ(service) → add_service(service),
  deregister: λ(service_id) → remove_service(service_id)
}
```

### 2.2 服务发现

**发现机制**：
```
ServiceDiscovery : (Client, Registry) → [Service]
∀client ∈ Client, ∀registry ∈ Registry | 
  ServiceDiscovery(client, registry) = 
    registry.find_services(client.requirements)
```

**负载均衡**：
```
LoadBalancing : [Service] → Service
∀services ∈ [Service] | LoadBalancing(services) = 
  select_best_service(services)
```

### 2.3 健康检查

**健康检查**：
```
HealthCheck : Service → Health
∀service ∈ Service | HealthCheck(service) = {
  status: check_health(service),
  last_check: current_time(),
  response_time: measure_response(service)
}
```

### 2.4 Rust实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[derive(Clone, Debug)]
struct ServiceInfo {
    id: String,
    endpoint: String,
    metadata: HashMap<String, String>,
    health_status: HealthStatus,
    last_heartbeat: Instant,
}

#[derive(Clone, Debug)]
enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

struct ServiceRegistry {
    services: Arc<Mutex<HashMap<String, ServiceInfo>>>,
}

impl ServiceRegistry {
    fn new() -> Self {
        ServiceRegistry {
            services: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn register(&self, service: ServiceInfo) {
        let mut services = self.services.lock().unwrap();
        services.insert(service.id.clone(), service);
    }
    
    fn deregister(&self, service_id: &str) {
        let mut services = self.services.lock().unwrap();
        services.remove(service_id);
    }
    
    fn discover(&self, filter: impl Fn(&ServiceInfo) -> bool) -> Vec<ServiceInfo> {
        let services = self.services.lock().unwrap();
        services.values()
            .filter(|service| filter(service))
            .cloned()
            .collect()
    }
    
    fn health_check(&self) {
        let mut services = self.services.lock().unwrap();
        let now = Instant::now();
        
        for service in services.values_mut() {
            if now.duration_since(service.last_heartbeat) > Duration::from_secs(30) {
                service.health_status = HealthStatus::Unhealthy;
            }
        }
    }
}
```

---

## 3. 熔断器模式

### 3.1 熔断器状态机

**状态定义**：
```
CircuitBreakerState : CircuitBreaker → State
∀cb ∈ CircuitBreaker | CircuitBreakerState(cb) ∈ {
  Closed, Open, HalfOpen
}
```

**状态转换**：
```
StateTransition : (CircuitBreaker, Event) → State
∀cb ∈ CircuitBreaker, ∀event ∈ Event | 
  StateTransition(cb, event) = match (cb.state, event) {
    (Closed, Failure) → if failure_count > threshold then Open else Closed,
    (Open, Timeout) → HalfOpen,
    (HalfOpen, Success) → Closed,
    (HalfOpen, Failure) → Open
  }
```

### 3.2 故障检测

**故障计数**：
```
FailureCounting : CircuitBreaker → Count
∀cb ∈ CircuitBreaker | FailureCounting(cb) = 
  count_recent_failures(cb.failure_window)
```

**阈值检查**：
```
ThresholdCheck : (CircuitBreaker, Count) → Boolean
∀cb ∈ CircuitBreaker, ∀count ∈ Count | 
  ThresholdCheck(cb, count) = count > cb.failure_threshold
```

### 3.3 恢复机制

**超时恢复**：
```
TimeoutRecovery : CircuitBreaker → Boolean
∀cb ∈ CircuitBreaker | TimeoutRecovery(cb) = 
  time_since_open > cb.timeout_duration
```

### 3.4 Rust实现

```rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[derive(Debug, Clone, PartialEq)]
enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

struct CircuitBreaker {
    state: Arc<Mutex<CircuitBreakerState>>,
    failure_count: Arc<Mutex<u32>>,
    failure_threshold: u32,
    timeout_duration: Duration,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    success_threshold: u32,
    success_count: Arc<Mutex<u32>>,
}

impl CircuitBreaker {
    fn new(failure_threshold: u32, timeout_duration: Duration) -> Self {
        CircuitBreaker {
            state: Arc::new(Mutex::new(CircuitBreakerState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            failure_threshold,
            timeout_duration,
            last_failure_time: Arc::new(Mutex::new(None)),
            success_threshold: 5,
            success_count: Arc::new(Mutex::new(0)),
        }
    }
    
    fn call<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Result<T, E>,
    {
        let state = *self.state.lock().unwrap();
        
        match state {
            CircuitBreakerState::Open => {
                if self.should_attempt_reset() {
                    self.transition_to_half_open();
                    self.call(operation)
                } else {
                    Err(CircuitBreakerError::Open)
                }
            }
            CircuitBreakerState::HalfOpen => {
                match operation() {
                    Ok(result) => {
                        self.record_success();
                        Ok(result)
                    }
                    Err(e) => {
                        self.record_failure();
                        Err(CircuitBreakerError::Operation(e))
                    }
                }
            }
            CircuitBreakerState::Closed => {
                match operation() {
                    Ok(result) => {
                        self.reset_failure_count();
                        Ok(result)
                    }
                    Err(e) => {
                        self.record_failure();
                        if self.should_open() {
                            self.transition_to_open();
                        }
                        Err(CircuitBreakerError::Operation(e))
                    }
                }
            }
        }
    }
    
    fn should_attempt_reset(&self) -> bool {
        if let Some(last_failure) = *self.last_failure_time.lock().unwrap() {
            Instant::now().duration_since(last_failure) >= self.timeout_duration
        } else {
            false
        }
    }
    
    fn should_open(&self) -> bool {
        *self.failure_count.lock().unwrap() >= self.failure_threshold
    }
    
    fn record_failure(&self) {
        let mut count = self.failure_count.lock().unwrap();
        *count += 1;
        *self.last_failure_time.lock().unwrap() = Some(Instant::now());
    }
    
    fn record_success(&self) {
        let mut count = self.success_count.lock().unwrap();
        *count += 1;
        if *count >= self.success_threshold {
            self.transition_to_closed();
        }
    }
    
    fn transition_to_open(&self) {
        *self.state.lock().unwrap() = CircuitBreakerState::Open;
    }
    
    fn transition_to_half_open(&self) {
        *self.state.lock().unwrap() = CircuitBreakerState::HalfOpen;
        *self.success_count.lock().unwrap() = 0;
    }
    
    fn transition_to_closed(&self) {
        *self.state.lock().unwrap() = CircuitBreakerState::Closed;
        *self.failure_count.lock().unwrap() = 0;
        *self.success_count.lock().unwrap() = 0;
    }
    
    fn reset_failure_count(&self) {
        *self.failure_count.lock().unwrap() = 0;
    }
}

#[derive(Debug)]
enum CircuitBreakerError<E> {
    Open,
    Operation(E),
}
```

---

## 4. API网关模式

### 4.1 路由功能

**路由规则**：
```
RoutingRule : Request → Route
∀request ∈ Request | RoutingRule(request) = 
  match request.path {
    "/api/v1/users" → user_service,
    "/api/v1/orders" → order_service,
    _ → default_service
  }
```

**路由表**：
```
RoutingTable : [Route] → Table
∀routes ∈ [Route] | RoutingTable(routes) = {
  routes: routes,
  match_route: λ(request) → find_matching_route(request)
}
```

### 4.2 负载均衡

**负载均衡策略**：
```
LoadBalancingStrategy : [Service] → Service
∀services ∈ [Service] | LoadBalancingStrategy(services) ∈ {
  RoundRobin(services),
  LeastConnections(services),
  WeightedRoundRobin(services)
}
```

### 4.3 认证授权

**认证机制**：
```
Authentication : Request → AuthResult
∀request ∈ Request | Authentication(request) = 
  validate_token(request.token)
```

**授权检查**：
```
Authorization : (User, Resource) → Boolean
∀user ∈ User, ∀resource ∈ Resource | 
  Authorization(user, resource) = 
    check_permissions(user, resource)
```

### 4.4 Rust实现

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

#[derive(Clone)]
struct Route {
    path: String,
    service_url: String,
    methods: Vec<String>,
}

struct ApiGateway {
    routes: Arc<Mutex<HashMap<String, Route>>>,
    load_balancer: Arc<LoadBalancer>,
    auth_service: Arc<AuthService>,
}

impl ApiGateway {
    fn new() -> Self {
        ApiGateway {
            routes: Arc::new(Mutex::new(HashMap::new())),
            load_balancer: Arc::new(LoadBalancer::new()),
            auth_service: Arc::new(AuthService::new()),
        }
    }
    
    async fn handle_request(&self, request: Request) -> Response {
        // 1. 认证
        if let Err(_) = self.auth_service.authenticate(&request).await {
            return Response::unauthorized();
        }
        
        // 2. 路由
        let route = self.route_request(&request).await;
        if let None = route {
            return Response::not_found();
        }
        
        // 3. 负载均衡
        let service_url = self.load_balancer.select_service(&route.unwrap().service_url).await;
        
        // 4. 转发请求
        self.forward_request(request, service_url).await
    }
    
    async fn route_request(&self, request: &Request) -> Option<Route> {
        let routes = self.routes.lock().await;
        routes.get(&request.path).cloned()
    }
}

struct LoadBalancer {
    services: Arc<Mutex<Vec<String>>>,
    current_index: Arc<Mutex<usize>>,
}

impl LoadBalancer {
    fn new() -> Self {
        LoadBalancer {
            services: Arc::new(Mutex::new(Vec::new())),
            current_index: Arc::new(Mutex::new(0)),
        }
    }
    
    async fn select_service(&self, service_name: &str) -> String {
        let services = self.services.lock().await;
        let mut index = self.current_index.lock().await;
        
        if services.is_empty() {
            return service_name.to_string();
        }
        
        let service = services[*index].clone();
        *index = (*index + 1) % services.len();
        service
    }
}

struct AuthService;

impl AuthService {
    fn new() -> Self {
        AuthService
    }
    
    async fn authenticate(&self, request: &Request) -> Result<(), AuthError> {
        // 实现认证逻辑
        Ok(())
    }
}

#[derive(Debug)]
struct Request {
    path: String,
    method: String,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

#[derive(Debug)]
struct Response {
    status_code: u16,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

impl Response {
    fn unauthorized() -> Self {
        Response {
            status_code: 401,
            headers: HashMap::new(),
            body: Vec::new(),
        }
    }
    
    fn not_found() -> Self {
        Response {
            status_code: 404,
            headers: HashMap::new(),
            body: Vec::new(),
        }
    }
}

#[derive(Debug)]
enum AuthError {
    InvalidToken,
    ExpiredToken,
    MissingToken,
}
```

---

## 5. Saga模式

### 5.1 分布式事务

**Saga定义**：
```
Saga : [Transaction] → Saga
∀transactions ∈ [Transaction] | Saga(transactions) = {
  transactions: transactions,
  compensations: [Compensation],
  coordinator: Coordinator
}
```

**事务步骤**：
```
TransactionStep : Step → Transaction
∀step ∈ Step | TransactionStep(step) = {
  action: step.action,
  compensation: step.compensation,
  status: step.status
}
```

### 5.2 补偿机制

**补偿操作**：
```
Compensation : Transaction → Compensation
∀transaction ∈ Transaction | Compensation(transaction) = 
  reverse_effects(transaction)
```

**补偿链**：
```
CompensationChain : [Transaction] → [Compensation]
∀transactions ∈ [Transaction] | CompensationChain(transactions) = 
  reverse(transactions).map(compensation)
```

### 5.3 协调策略

**协调器**：
```
Coordinator : Saga → Coordinator
∀saga ∈ Saga | Coordinator(saga) = {
  saga: saga,
  execute: λ() → execute_saga(),
  compensate: λ() → compensate_saga()
}
```

### 5.4 Rust实现

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

#[derive(Debug, Clone)]
enum StepStatus {
    Pending,
    Completed,
    Failed,
    Compensated,
}

#[derive(Debug)]
struct SagaStep {
    id: String,
    action: Box<dyn Fn() -> Result<(), String> + Send + Sync>,
    compensation: Box<dyn Fn() -> Result<(), String> + Send + Sync>,
    status: StepStatus,
}

struct Saga {
    steps: Vec<SagaStep>,
    coordinator: Arc<SagaCoordinator>,
}

impl Saga {
    fn new() -> Self {
        Saga {
            steps: Vec::new(),
            coordinator: Arc::new(SagaCoordinator::new()),
        }
    }
    
    fn add_step<A, C>(&mut self, id: String, action: A, compensation: C)
    where
        A: Fn() -> Result<(), String> + Send + Sync + 'static,
        C: Fn() -> Result<(), String> + Send + Sync + 'static,
    {
        let step = SagaStep {
            id,
            action: Box::new(action),
            compensation: Box::new(compensation),
            status: StepStatus::Pending,
        };
        self.steps.push(step);
    }
    
    async fn execute(&mut self) -> Result<(), String> {
        for step in &mut self.steps {
            step.status = StepStatus::Pending;
            
            match (step.action)() {
                Ok(_) => {
                    step.status = StepStatus::Completed;
                }
                Err(e) => {
                    step.status = StepStatus::Failed;
                    self.compensate().await?;
                    return Err(e);
                }
            }
        }
        Ok(())
    }
    
    async fn compensate(&mut self) -> Result<(), String> {
        for step in self.steps.iter_mut().rev() {
            if step.status == StepStatus::Completed {
                match (step.compensation)() {
                    Ok(_) => {
                        step.status = StepStatus::Compensated;
                    }
                    Err(e) => {
                        return Err(format!("Compensation failed for step {}: {}", step.id, e));
                    }
                }
            }
        }
        Ok(())
    }
}

struct SagaCoordinator {
    sagas: Arc<Mutex<Vec<Saga>>>,
}

impl SagaCoordinator {
    fn new() -> Self {
        SagaCoordinator {
            sagas: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    async fn execute_saga(&self, mut saga: Saga) -> Result<(), String> {
        let result = saga.execute().await;
        
        let mut sagas = self.sagas.lock().await;
        sagas.push(saga);
        
        result
    }
}

// 示例：订单处理Saga
async fn create_order_saga() -> Result<(), String> {
    let mut saga = Saga::new();
    
    // 步骤1：创建订单
    saga.add_step(
        "create_order".to_string(),
        || {
            println!("Creating order...");
            Ok(())
        },
        || {
            println!("Compensating order creation...");
            Ok(())
        },
    );
    
    // 步骤2：扣减库存
    saga.add_step(
        "reduce_inventory".to_string(),
        || {
            println!("Reducing inventory...");
            Ok(())
        },
        || {
            println!("Compensating inventory reduction...");
            Ok(())
        },
    );
    
    // 步骤3：扣减余额
    saga.add_step(
        "deduct_balance".to_string(),
        || {
            println!("Deducting balance...");
            Ok(())
        },
        || {
            println!("Compensating balance deduction...");
            Ok(())
        },
    );
    
    saga.execute().await
}
```

---

## 结论

分布式系统模式为构建可扩展、高可用的分布式应用提供了重要的设计模式。通过Rust的类型安全和并发安全特性，这些模式能够以更可靠的方式实现。

**核心分布式原则**：
1. 容错性：通过熔断器、重试等机制处理故障
2. 可扩展性：通过服务发现、负载均衡支持水平扩展
3. 一致性：通过Saga等模式保证分布式事务的一致性
4. 安全性：通过API网关提供统一的认证授权
5. 可观测性：通过健康检查、监控等机制提供系统可见性

这些模式为构建复杂的分布式系统提供了坚实的基础，确保系统的可靠性、可扩展性和可维护性。 