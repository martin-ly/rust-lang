# 通用架构模式 - Rust最佳实践

## 概述

本文档提供了在Rust中实现常见架构模式的通用指南，这些模式可以应用于各个软件行业领域。

## 1. 微服务架构模式

### 服务发现

```rust
pub trait ServiceRegistry {
    async fn register(&self, service: ServiceInfo) -> Result<(), RegistryError>;
    async fn deregister(&self, service_id: &ServiceId) -> Result<(), RegistryError>;
    async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInfo>, RegistryError>;
}

pub struct ConsulServiceRegistry {
    client: consul::Client,
}

#[async_trait]
impl ServiceRegistry for ConsulServiceRegistry {
    async fn register(&self, service: ServiceInfo) -> Result<(), RegistryError> {
        let registration = consul::ServiceRegistration {
            id: service.id.to_string(),
            name: service.name,
            address: service.address,
            port: service.port,
            tags: service.tags,
        };
        
        self.client.register_service(&registration).await?;
        Ok(())
    }
    
    async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInfo>, RegistryError> {
        let services = self.client.get_service(service_name).await?;
        
        let service_infos: Vec<ServiceInfo> = services
            .into_iter()
            .map(|s| ServiceInfo {
                id: ServiceId::new(&s.id),
                name: s.name,
                address: s.address,
                port: s.port,
                tags: s.tags,
            })
            .collect();
        
        Ok(service_infos)
    }
}
```

### 负载均衡

```rust
pub trait LoadBalancer {
    async fn select_service(&self, services: &[ServiceInfo]) -> Result<ServiceInfo, LoadBalancerError>;
}

pub struct RoundRobinLoadBalancer {
    current_index: AtomicUsize,
}

#[async_trait]
impl LoadBalancer for RoundRobinLoadBalancer {
    async fn select_service(&self, services: &[ServiceInfo]) -> Result<ServiceInfo, LoadBalancerError> {
        if services.is_empty() {
            return Err(LoadBalancerError::NoServicesAvailable);
        }
        
        let index = self.current_index.fetch_add(1, Ordering::Relaxed) % services.len();
        Ok(services[index].clone())
    }
}

pub struct HealthCheckLoadBalancer {
    health_checker: Box<dyn HealthChecker>,
}

#[async_trait]
impl LoadBalancer for HealthCheckLoadBalancer {
    async fn select_service(&self, services: &[ServiceInfo]) -> Result<ServiceInfo, LoadBalancerError> {
        let healthy_services: Vec<ServiceInfo> = futures::future::join_all(
            services.iter().map(|service| self.health_checker.check(service))
        ).await
            .into_iter()
            .filter_map(|result| result.ok())
            .collect();
        
        if healthy_services.is_empty() {
            return Err(LoadBalancerError::NoHealthyServices);
        }
        
        // 随机选择健康服务
        let index = rand::random::<usize>() % healthy_services.len();
        Ok(healthy_services[index].clone())
    }
}
```

## 2. 事件驱动架构模式

### 事件总线

```rust
pub struct EventBus {
    handlers: HashMap<TypeId, Vec<Box<dyn EventHandler>>>,
    event_queue: Arc<Mutex<VecDeque<Box<dyn Event>>>>,
}

impl EventBus {
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
            event_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    pub fn subscribe<T: Event + 'static>(&mut self, handler: Box<dyn EventHandler>) {
        let type_id = TypeId::of::<T>();
        self.handlers.entry(type_id).or_insert_with(Vec::new).push(handler);
    }
    
    pub async fn publish<T: Event + 'static>(&self, event: T) -> Result<(), EventError> {
        let type_id = TypeId::of::<T>();
        
        if let Some(handlers) = self.handlers.get(&type_id) {
            for handler in handlers {
                handler.handle(&event).await?;
            }
        }
        
        Ok(())
    }
    
    pub async fn publish_async<T: Event + 'static>(&self, event: T) -> Result<(), EventError> {
        let event_box = Box::new(event);
        {
            let mut queue = self.event_queue.lock().await;
            queue.push_back(event_box);
        }
        
        // 异步处理事件
        tokio::spawn(self.process_event_queue());
        
        Ok(())
    }
    
    async fn process_event_queue(&self) {
        loop {
            let event = {
                let mut queue = self.event_queue.lock().await;
                queue.pop_front()
            };
            
            if let Some(event) = event {
                // 处理事件
                self.process_event(event).await;
            } else {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }
}
```

### 事件溯源

```rust
pub trait EventStore {
    async fn append_events(&self, aggregate_id: &str, events: Vec<Event>) -> Result<(), EventStoreError>;
    async fn get_events(&self, aggregate_id: &str) -> Result<Vec<Event>, EventStoreError>;
}

pub struct EventSourcedAggregate<T> {
    id: String,
    version: u64,
    state: T,
    uncommitted_events: Vec<Event>,
}

impl<T: Aggregate> EventSourcedAggregate<T> {
    pub fn new(id: String) -> Self {
        Self {
            id,
            version: 0,
            state: T::default(),
            uncommitted_events: Vec::new(),
        }
    }
    
    pub fn apply_event(&mut self, event: Event) {
        self.state.apply(event.clone());
        self.version += 1;
        self.uncommitted_events.push(event);
    }
    
    pub async fn save(&self, event_store: &dyn EventStore) -> Result<(), EventStoreError> {
        if !self.uncommitted_events.is_empty() {
            event_store.append_events(&self.id, self.uncommitted_events.clone()).await?;
        }
        Ok(())
    }
    
    pub async fn load(id: &str, event_store: &dyn EventStore) -> Result<Self, EventStoreError> {
        let events = event_store.get_events(id).await?;
        
        let mut aggregate = Self::new(id.to_string());
        for event in events {
            aggregate.apply_event(event);
        }
        
        Ok(aggregate)
    }
}
```

## 3. CQRS模式

### 命令处理

```rust
pub trait CommandHandler<C: Command> {
    async fn handle(&self, command: C) -> Result<(), CommandError>;
}

pub struct CommandBus {
    handlers: HashMap<TypeId, Box<dyn CommandHandler<dyn Command>>>,
}

impl CommandBus {
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }
    
    pub fn register<C: Command + 'static>(&mut self, handler: Box<dyn CommandHandler<C>>) {
        let type_id = TypeId::of::<C>();
        self.handlers.insert(type_id, Box::new(handler));
    }
    
    pub async fn dispatch<C: Command + 'static>(&self, command: C) -> Result<(), CommandError> {
        let type_id = TypeId::of::<C>();
        
        if let Some(handler) = self.handlers.get(&type_id) {
            handler.handle(command).await
        } else {
            Err(CommandError::NoHandlerFound)
        }
    }
}
```

### 查询处理

```rust
pub trait QueryHandler<Q: Query, R> {
    async fn handle(&self, query: Q) -> Result<R, QueryError>;
}

pub struct QueryBus {
    handlers: HashMap<TypeId, Box<dyn QueryHandler<dyn Query, Box<dyn std::any::Any>>>>,
}

impl QueryBus {
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }
    
    pub fn register<Q: Query + 'static, R: 'static>(&mut self, handler: Box<dyn QueryHandler<Q, R>>) {
        let type_id = TypeId::of::<Q>();
        self.handlers.insert(type_id, Box::new(handler));
    }
    
    pub async fn dispatch<Q: Query + 'static, R: 'static>(&self, query: Q) -> Result<R, QueryError> {
        let type_id = TypeId::of::<Q>();
        
        if let Some(handler) = self.handlers.get(&type_id) {
            // 类型转换和调用
            // 实际实现需要更复杂的类型处理
            todo!()
        } else {
            Err(QueryError::NoHandlerFound)
        }
    }
}
```

## 4. 仓储模式

### 通用仓储接口

```rust
pub trait Repository<T: Aggregate> {
    async fn save(&self, aggregate: &T) -> Result<(), RepositoryError>;
    async fn find_by_id(&self, id: &T::Id) -> Result<Option<T>, RepositoryError>;
    async fn delete(&self, id: &T::Id) -> Result<(), RepositoryError>;
}

pub trait Aggregate {
    type Id: Clone + Eq + Hash;
    
    fn id(&self) -> &Self::Id;
    fn version(&self) -> u64;
}
```

### 缓存仓储

```rust
pub struct CachedRepository<T: Aggregate> {
    cache: Cache<T::Id, T>,
    repository: Box<dyn Repository<T>>,
}

#[async_trait]
impl<T: Aggregate> Repository<T> for CachedRepository<T> {
    async fn save(&self, aggregate: &T) -> Result<(), RepositoryError> {
        // 先保存到主存储
        self.repository.save(aggregate).await?;
        
        // 更新缓存
        self.cache.insert(aggregate.id().clone(), aggregate.clone()).await;
        
        Ok(())
    }
    
    async fn find_by_id(&self, id: &T::Id) -> Result<Option<T>, RepositoryError> {
        // 先查缓存
        if let Some(aggregate) = self.cache.get(id).await {
            return Ok(Some(aggregate));
        }
        
        // 缓存未命中，查主存储
        if let Some(aggregate) = self.repository.find_by_id(id).await? {
            // 更新缓存
            self.cache.insert(id.clone(), aggregate.clone()).await;
            Ok(Some(aggregate))
        } else {
            Ok(None)
        }
    }
}
```

## 5. 工厂模式

### 抽象工厂

```rust
pub trait AbstractFactory {
    type ProductA: ProductA;
    type ProductB: ProductB;
    
    fn create_product_a(&self) -> Self::ProductA;
    fn create_product_b(&self) -> Self::ProductB;
}

pub struct ConcreteFactory1;

impl AbstractFactory for ConcreteFactory1 {
    type ProductA = ConcreteProductA1;
    type ProductB = ConcreteProductB1;
    
    fn create_product_a(&self) -> Self::ProductA {
        ConcreteProductA1::new()
    }
    
    fn create_product_b(&self) -> Self::ProductB {
        ConcreteProductB1::new()
    }
}
```

### 对象池

```rust
pub struct ObjectPool<T> {
    objects: Vec<T>,
    available: Vec<usize>,
    factory: Box<dyn Fn() -> T>,
    max_size: usize,
}

impl<T> ObjectPool<T> {
    pub fn new(max_size: usize, factory: impl Fn() -> T + 'static) -> Self {
        let mut objects = Vec::with_capacity(max_size);
        let mut available = Vec::with_capacity(max_size);
        
        for i in 0..max_size {
            objects.push(factory());
            available.push(i);
        }
        
        Self {
            objects,
            available,
            factory: Box::new(factory),
            max_size,
        }
    }
    
    pub fn acquire(&mut self) -> Option<&mut T> {
        self.available.pop().map(|index| &mut self.objects[index])
    }
    
    pub fn release(&mut self, index: usize) {
        if index < self.max_size {
            self.available.push(index);
        }
    }
}
```

## 6. 观察者模式

### 事件观察者

```rust
pub trait Observer {
    async fn update(&self, event: &Event) -> Result<(), ObserverError>;
}

pub struct Subject {
    observers: Vec<Box<dyn Observer>>,
}

impl Subject {
    pub fn new() -> Self {
        Self {
            observers: Vec::new(),
        }
    }
    
    pub fn attach(&mut self, observer: Box<dyn Observer>) {
        self.observers.push(observer);
    }
    
    pub fn detach(&mut self, observer_id: &str) {
        self.observers.retain(|obs| obs.id() != observer_id);
    }
    
    pub async fn notify(&self, event: &Event) -> Result<(), ObserverError> {
        for observer in &self.observers {
            observer.update(event).await?;
        }
        Ok(())
    }
}
```

## 7. 策略模式

### 可插拔策略

```rust
pub trait Strategy {
    async fn execute(&self, context: &Context) -> Result<StrategyResult, StrategyError>;
}

pub struct Context {
    data: HashMap<String, String>,
    strategy: Box<dyn Strategy>,
}

impl Context {
    pub fn new(strategy: Box<dyn Strategy>) -> Self {
        Self {
            data: HashMap::new(),
            strategy,
        }
    }
    
    pub fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }
    
    pub async fn execute_strategy(&self) -> Result<StrategyResult, StrategyError> {
        self.strategy.execute(self).await
    }
}
```

## 8. 装饰器模式

### 功能装饰器

```rust
pub trait Component {
    async fn operation(&self) -> Result<String, ComponentError>;
}

pub struct ConcreteComponent;

#[async_trait]
impl Component for ConcreteComponent {
    async fn operation(&self) -> Result<String, ComponentError> {
        Ok("ConcreteComponent".to_string())
    }
}

pub struct Decorator {
    component: Box<dyn Component>,
}

impl Decorator {
    pub fn new(component: Box<dyn Component>) -> Self {
        Self { component }
    }
}

#[async_trait]
impl Component for Decorator {
    async fn operation(&self) -> Result<String, ComponentError> {
        let result = self.component.operation().await?;
        Ok(format!("Decorated({})", result))
    }
}
```

## 9. 适配器模式

### 接口适配

```rust
pub trait Target {
    async fn request(&self) -> Result<String, AdapterError>;
}

pub struct Adaptee;

impl Adaptee {
    pub async fn specific_request(&self) -> Result<String, AdapterError> {
        Ok("Adaptee specific request".to_string())
    }
}

pub struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    pub fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

#[async_trait]
impl Target for Adapter {
    async fn request(&self) -> Result<String, AdapterError> {
        self.adaptee.specific_request().await
    }
}
```

## 10. 模板方法模式

### 算法模板

```rust
pub trait AlgorithmTemplate {
    async fn template_method(&self) -> Result<String, AlgorithmError> {
        let step1 = self.step1().await?;
        let step2 = self.step2().await?;
        let step3 = self.step3().await?;
        
        Ok(format!("{} -> {} -> {}", step1, step2, step3))
    }
    
    async fn step1(&self) -> Result<String, AlgorithmError>;
    async fn step2(&self) -> Result<String, AlgorithmError>;
    async fn step3(&self) -> Result<String, AlgorithmError>;
}

pub struct ConcreteAlgorithm;

#[async_trait]
impl AlgorithmTemplate for ConcreteAlgorithm {
    async fn step1(&self) -> Result<String, AlgorithmError> {
        Ok("Concrete step 1".to_string())
    }
    
    async fn step2(&self) -> Result<String, AlgorithmError> {
        Ok("Concrete step 2".to_string())
    }
    
    async fn step3(&self) -> Result<String, AlgorithmError> {
        Ok("Concrete step 3".to_string())
    }
}
```

## 总结

这些通用架构模式为Rust项目提供了可复用的设计解决方案：

1. **微服务模式**: 服务发现、负载均衡、健康检查
2. **事件驱动**: 事件总线、事件溯源、异步处理
3. **CQRS**: 命令查询分离、读写模型分离
4. **仓储模式**: 数据访问抽象、缓存策略
5. **设计模式**: 工厂、观察者、策略、装饰器等

通过组合这些模式，可以构建出灵活、可维护、可扩展的系统架构。
