use anyhow::Result;
use c06_async::utils::metrics;
use once_cell::sync::Lazy;
use prometheus::{Histogram, HistogramOpts, IntCounter, Opts, Registry};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, RwLock};
use tokio::time::sleep;
use tracing::{info, instrument};

/// 2025年高级异步设计模式演示
/// 包含最新的异步编程模式和最佳实践

/// 1. 异步状态机模式
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AsyncState {
    Idle,
    Loading,
    Ready,
    Processing,
    Error,
    Completed,
}

pub struct AsyncStateMachine {
    state: Arc<RwLock<AsyncState>>,
    transitions: Arc<Mutex<Vec<(AsyncState, AsyncState, String)>>>,
    state_handlers: Arc<
        RwLock<std::collections::HashMap<AsyncState, Box<dyn Fn() -> Result<()> + Send + Sync>>>,
    >,
}

impl AsyncStateMachine {
    pub fn new(initial_state: AsyncState) -> Self {
        Self {
            state: Arc::new(RwLock::new(initial_state)),
            transitions: Arc::new(Mutex::new(Vec::new())),
            state_handlers: Arc::new(RwLock::new(std::collections::HashMap::new())),
        }
    }

    pub async fn transition(&self, from: AsyncState, to: AsyncState, reason: String) -> Result<()> {
        let current_state = self.state.read().await.clone();

        if current_state != from {
            return Err(anyhow::anyhow!(
                "Invalid transition from {:?} to {:?}",
                current_state,
                to
            ));
        }

        // 记录转换
        {
            let mut transitions = self.transitions.lock().await;
            transitions.push((from.clone(), to.clone(), reason));
        }

        // 执行状态转换
        {
            let mut state = self.state.write().await;
            *state = to.clone();
        }

        // 执行状态处理器
        if let Some(handler) = self.state_handlers.read().await.get(&to) {
            handler()?;
        }

        info!("状态转换: {:?} -> {:?}", from, to);
        Ok(())
    }

    pub async fn get_state(&self) -> AsyncState {
        self.state.read().await.clone()
    }

    pub async fn set_handler<F>(&self, state: AsyncState, handler: F)
    where
        F: Fn() -> Result<()> + Send + Sync + 'static,
    {
        self.state_handlers
            .write()
            .await
            .insert(state, Box::new(handler));
    }

    pub async fn get_transitions(&self) -> Vec<(AsyncState, AsyncState, String)> {
        self.transitions.lock().await.clone()
    }
}

/// 2. 异步观察者模式
pub enum AsyncObserver {
    EventLogger(AsyncEventLogger),
}

impl AsyncObserver {
    pub async fn notify(&self, event: &str) -> Result<()> {
        match self {
            AsyncObserver::EventLogger(logger) => logger.notify(event).await,
        }
    }
}

pub struct AsyncSubject {
    observers: Arc<RwLock<Vec<AsyncObserver>>>,
}

impl AsyncSubject {
    pub fn new() -> Self {
        Self {
            observers: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn subscribe(&self, observer: AsyncObserver) {
        self.observers.write().await.push(observer);
    }

    pub async fn unsubscribe(&self, index: usize) -> Result<()> {
        let mut observers = self.observers.write().await;
        if index < observers.len() {
            observers.remove(index);
            Ok(())
        } else {
            Err(anyhow::anyhow!("Invalid observer index"))
        }
    }

    pub async fn notify_all(&self, event: &str) -> Result<()> {
        let observers = self.observers.read().await;
        let mut errors = Vec::new();

        for (i, observer) in observers.iter().enumerate() {
            if let Err(e) = observer.notify(event).await {
                errors.push(format!("Observer {} error: {}", i, e));
            }
        }

        if !errors.is_empty() {
            return Err(anyhow::anyhow!("Observer errors: {}", errors.join(", ")));
        }

        Ok(())
    }

    pub async fn observer_count(&self) -> usize {
        self.observers.read().await.len()
    }
}

/// 3. 异步命令模式
pub enum AsyncCommand {
    LogCommand(AsyncLogCommand),
}

impl AsyncCommand {
    pub async fn execute(&self) -> Result<()> {
        match self {
            AsyncCommand::LogCommand(cmd) => cmd.execute().await,
        }
    }

    pub async fn undo(&self) -> Result<()> {
        match self {
            AsyncCommand::LogCommand(cmd) => cmd.undo().await,
        }
    }

    pub fn description(&self) -> String {
        match self {
            AsyncCommand::LogCommand(cmd) => cmd.description(),
        }
    }
}

pub struct AsyncCommandInvoker {
    history: Arc<RwLock<Vec<AsyncCommand>>>,
    current_index: Arc<RwLock<isize>>,
}

impl AsyncCommandInvoker {
    pub fn new() -> Self {
        Self {
            history: Arc::new(RwLock::new(Vec::new())),
            current_index: Arc::new(RwLock::new(-1)),
        }
    }

    pub async fn execute_command(&self, command: AsyncCommand) -> Result<()> {
        let description = command.description();
        command.execute().await?;

        let mut history = self.history.write().await;
        let mut index = self.current_index.write().await;

        // 移除当前位置之后的历史记录
        *index += 1;
        history.truncate(*index as usize);
        history.push(command);

        info!("执行命令: {}", description);
        Ok(())
    }

    pub async fn undo(&self) -> Result<()> {
        let mut index = self.current_index.write().await;
        if *index >= 0 {
            let history = self.history.read().await;
            if let Some(command) = history.get(*index as usize) {
                let description = command.description();
                command.undo().await?;
                *index -= 1;
                info!("撤销命令: {}", description);
                return Ok(());
            }
        }
        Err(anyhow::anyhow!("Nothing to undo"))
    }

    pub async fn redo(&self) -> Result<()> {
        let mut index = self.current_index.write().await;
        let history = self.history.read().await;

        if (*index + 1) < history.len() as isize {
            *index += 1;
            if let Some(command) = history.get(*index as usize) {
                let description = command.description();
                command.execute().await?;
                info!("重做命令: {}", description);
                return Ok(());
            }
        }
        Err(anyhow::anyhow!("Nothing to redo"))
    }

    pub async fn can_undo(&self) -> bool {
        *self.current_index.read().await >= 0
    }

    pub async fn can_redo(&self) -> bool {
        let index = *self.current_index.read().await;
        let history_len = self.history.read().await.len();
        (index + 1) < history_len as isize
    }
}

/// 4. 异步责任链模式
pub enum AsyncHandler {
    Validation(AsyncValidationHandler),
    Processing(AsyncProcessingHandler),
    Logging(AsyncLoggingHandler),
}

impl AsyncHandler {
    pub async fn handle(&self, request: &str) -> Result<Option<String>> {
        match self {
            AsyncHandler::Validation(handler) => handler.handle(request).await,
            AsyncHandler::Processing(handler) => handler.handle(request).await,
            AsyncHandler::Logging(handler) => handler.handle(request).await,
        }
    }
}

pub struct AsyncChainBuilder {
    handlers: Vec<AsyncHandler>,
}

impl AsyncChainBuilder {
    pub fn new() -> Self {
        Self {
            handlers: Vec::new(),
        }
    }

    pub fn add_handler(mut self, handler: AsyncHandler) -> Self {
        self.handlers.push(handler);
        self
    }

    pub fn build(self) -> AsyncChain {
        AsyncChain {
            handlers: self.handlers,
        }
    }
}

pub struct AsyncChain {
    handlers: Vec<AsyncHandler>,
}

impl AsyncChain {
    pub async fn process(&self, mut request: String) -> Result<String> {
        for handler in &self.handlers {
            match handler.handle(&request).await? {
                Some(new_request) => request = new_request,
                None => break,
            };
        }
        Ok(request)
    }
}

/// 5. 异步适配器模式
pub trait AsyncTarget {
    fn async_request(&self) -> impl std::future::Future<Output = Result<String>> + Send;
}

pub struct AsyncAdapter {
    adaptee: Arc<dyn AsyncAdaptee + Send + Sync>,
}

pub trait AsyncAdaptee {
    fn sync_request(&self) -> Result<String>;
}

impl AsyncAdapter {
    pub fn new(adaptee: Arc<dyn AsyncAdaptee + Send + Sync>) -> Self {
        Self { adaptee }
    }
}

impl AsyncTarget for AsyncAdapter {
    async fn async_request(&self) -> Result<String> {
        // 将同步调用适配为异步调用
        let result = tokio::task::spawn_blocking({
            let adaptee = self.adaptee.clone();
            move || adaptee.sync_request()
        })
        .await??;

        Ok(result)
    }
}

/// 6. 异步装饰器模式
pub enum AsyncComponent {
    Concrete(AsyncConcreteComponent),
    Decorator(AsyncDecorator),
}

impl AsyncComponent {
    pub async fn operation(&self) -> Result<String> {
        match self {
            AsyncComponent::Concrete(component) => component.operation().await,
            AsyncComponent::Decorator(decorator) => Box::pin(decorator.operation()).await,
        }
    }
}

pub struct AsyncConcreteComponent;

impl AsyncConcreteComponent {
    pub async fn operation(&self) -> Result<String> {
        Ok("ConcreteComponent".to_string())
    }
}

pub struct AsyncDecorator {
    component: Box<AsyncComponent>,
    additional_data: String,
}

impl AsyncDecorator {
    pub fn new(component: AsyncComponent, additional_data: String) -> Self {
        Self {
            component: Box::new(component),
            additional_data,
        }
    }

    pub async fn operation(&self) -> Result<String> {
        let base_result = self.component.operation().await?;
        Ok(format!("{}[{}]", base_result, self.additional_data))
    }
}

/// 7. 异步门面模式
pub struct AsyncFacade {
    subsystem_a: Arc<AsyncSubsystemA>,
    subsystem_b: Arc<AsyncSubsystemB>,
    subsystem_c: Arc<AsyncSubsystemC>,
}

pub struct AsyncSubsystemA;
pub struct AsyncSubsystemB;
pub struct AsyncSubsystemC;

impl AsyncSubsystemA {
    pub async fn operation_a(&self) -> Result<String> {
        sleep(Duration::from_millis(100)).await;
        Ok("SubsystemA".to_string())
    }
}

impl AsyncSubsystemB {
    pub async fn operation_b(&self) -> Result<String> {
        sleep(Duration::from_millis(150)).await;
        Ok("SubsystemB".to_string())
    }
}

impl AsyncSubsystemC {
    pub async fn operation_c(&self) -> Result<String> {
        sleep(Duration::from_millis(200)).await;
        Ok("SubsystemC".to_string())
    }
}

impl AsyncFacade {
    pub fn new() -> Self {
        Self {
            subsystem_a: Arc::new(AsyncSubsystemA),
            subsystem_b: Arc::new(AsyncSubsystemB),
            subsystem_c: Arc::new(AsyncSubsystemC),
        }
    }

    pub async fn complex_operation(&self) -> Result<String> {
        // 协调多个子系统的操作
        let result_a = self.subsystem_a.operation_a().await?;
        let result_b = self.subsystem_b.operation_b().await?;
        let result_c = self.subsystem_c.operation_c().await?;

        Ok(format!(
            "Facade: {} + {} + {}",
            result_a, result_b, result_c
        ))
    }
}

/// 8. 异步单例模式
pub struct AsyncSingleton {
    data: Arc<RwLock<String>>,
}

impl AsyncSingleton {
    pub async fn get_instance() -> Arc<Self> {
        static INSTANCE: tokio::sync::OnceCell<Arc<AsyncSingleton>> =
            tokio::sync::OnceCell::const_new();

        INSTANCE
            .get_or_init(|| async {
                Arc::new(Self {
                    data: Arc::new(RwLock::new("Singleton Data".to_string())),
                })
            })
            .await
            .clone()
    }

    pub async fn get_data(&self) -> String {
        self.data.read().await.clone()
    }

    pub async fn set_data(&self, data: String) {
        *self.data.write().await = data;
    }
}

/// 9. 异步建造者模式
pub struct AsyncProduct {
    part_a: String,
    part_b: String,
    part_c: String,
}

pub struct AsyncBuilder {
    part_a: Option<String>,
    part_b: Option<String>,
    part_c: Option<String>,
}

impl AsyncBuilder {
    pub fn new() -> Self {
        Self {
            part_a: None,
            part_b: None,
            part_c: None,
        }
    }

    pub async fn build_part_a(mut self, data: String) -> Self {
        // 模拟异步构建过程
        sleep(Duration::from_millis(50)).await;
        self.part_a = Some(format!("AsyncPartA: {}", data));
        self
    }

    pub async fn build_part_b(mut self, data: String) -> Self {
        sleep(Duration::from_millis(75)).await;
        self.part_b = Some(format!("AsyncPartB: {}", data));
        self
    }

    pub async fn build_part_c(mut self, data: String) -> Self {
        sleep(Duration::from_millis(100)).await;
        self.part_c = Some(format!("AsyncPartC: {}", data));
        self
    }

    pub fn build(self) -> Result<AsyncProduct> {
        Ok(AsyncProduct {
            part_a: self
                .part_a
                .ok_or_else(|| anyhow::anyhow!("Missing part_a"))?,
            part_b: self
                .part_b
                .ok_or_else(|| anyhow::anyhow!("Missing part_b"))?,
            part_c: self
                .part_c
                .ok_or_else(|| anyhow::anyhow!("Missing part_c"))?,
        })
    }
}

/// 10. 异步策略模式
pub enum AsyncStrategy {
    StrategyA(AsyncStrategyA),
    StrategyB(AsyncStrategyB),
    StrategyC(AsyncStrategyC),
}

impl AsyncStrategy {
    pub async fn execute(&self, input: String) -> Result<String> {
        match self {
            AsyncStrategy::StrategyA(strategy) => strategy.execute(input).await,
            AsyncStrategy::StrategyB(strategy) => strategy.execute(input).await,
            AsyncStrategy::StrategyC(strategy) => strategy.execute(input).await,
        }
    }
}

pub struct AsyncStrategyA;
pub struct AsyncStrategyB;
pub struct AsyncStrategyC;

impl AsyncStrategyA {
    pub async fn execute(&self, input: String) -> Result<String> {
        sleep(Duration::from_millis(100)).await;
        Ok(format!("StrategyA: {}", input.to_uppercase()))
    }
}

impl AsyncStrategyB {
    pub async fn execute(&self, input: String) -> Result<String> {
        sleep(Duration::from_millis(150)).await;
        Ok(format!("StrategyB: {}", input.to_lowercase()))
    }
}

impl AsyncStrategyC {
    pub async fn execute(&self, input: String) -> Result<String> {
        sleep(Duration::from_millis(200)).await;
        Ok(format!(
            "StrategyC: {}",
            input.chars().rev().collect::<String>()
        ))
    }
}

pub struct AsyncContext {
    strategy: AsyncStrategy,
}

impl AsyncContext {
    pub fn new(strategy: AsyncStrategy) -> Self {
        Self { strategy }
    }

    pub fn set_strategy(&mut self, strategy: AsyncStrategy) {
        self.strategy = strategy;
    }

    pub async fn execute_strategy(&self, input: String) -> Result<String> {
        self.strategy.execute(input).await
    }
}

/// 演示所有高级异步设计模式
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt().with_env_filter("info").init();

    // 启动基础 /metrics 服务（仅用于本文件演示期间的观测，可选）
    let registry = Registry::new();
    // 注册通用 demo 指标（示例）：执行计数与耗时直方图
    static DEMO_EXEC_TOTAL: Lazy<IntCounter> = Lazy::new(|| {
        IntCounter::with_opts(Opts::new("demo_exec_total", "demo 执行总次数")).unwrap()
    });
    static DEMO_EXEC_SECONDS: Lazy<Histogram> = Lazy::new(|| {
        Histogram::with_opts(HistogramOpts::new("demo_exec_seconds", "demo 执行耗时(秒)")).unwrap()
    });
    let _ = registry.register(Box::new(DEMO_EXEC_TOTAL.clone()));
    let _ = registry.register(Box::new(DEMO_EXEC_SECONDS.clone()));
    let metrics_handle = tokio::spawn(metrics::serve_metrics(registry.clone(), "127.0.0.1:9899"));

    info!("🚀 开始 2025 年高级异步设计模式演示");

    // 1. 异步状态机演示
    {
        let _t = std::time::Instant::now();
        demo_async_state_machine().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 2. 异步观察者演示
    {
        let _t = std::time::Instant::now();
        demo_async_observer().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 3. 异步命令模式演示
    {
        let _t = std::time::Instant::now();
        demo_async_command().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 4. 异步责任链演示
    {
        let _t = std::time::Instant::now();
        demo_async_chain_of_responsibility().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 5. 异步适配器演示
    {
        let _t = std::time::Instant::now();
        demo_async_adapter().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 6. 异步装饰器演示
    {
        let _t = std::time::Instant::now();
        demo_async_decorator().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 7. 异步门面演示
    {
        let _t = std::time::Instant::now();
        demo_async_facade().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 8. 异步单例演示
    {
        let _t = std::time::Instant::now();
        demo_async_singleton().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 9. 异步建造者演示
    {
        let _t = std::time::Instant::now();
        demo_async_builder().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    // 10. 异步策略演示
    {
        let _t = std::time::Instant::now();
        demo_async_strategy().await?;
        DEMO_EXEC_TOTAL.inc();
        DEMO_EXEC_SECONDS.observe(_t.elapsed().as_secs_f64());
    }

    info!("✅ 2025 年高级异步设计模式演示完成!");
    let _ = metrics_handle.abort();
    Ok(())
}

#[instrument]
async fn demo_async_state_machine() -> Result<()> {
    info!("📊 演示异步状态机模式");

    let state_machine = AsyncStateMachine::new(AsyncState::Idle);

    // 设置状态处理器
    state_machine
        .set_handler(AsyncState::Loading, || {
            info!("开始加载数据...");
            Ok(())
        })
        .await;

    state_machine
        .set_handler(AsyncState::Ready, || {
            info!("数据加载完成，准备就绪");
            Ok(())
        })
        .await;

    state_machine
        .set_handler(AsyncState::Processing, || {
            info!("开始处理数据...");
            Ok(())
        })
        .await;

    // 执行状态转换
    state_machine
        .transition(
            AsyncState::Idle,
            AsyncState::Loading,
            "开始加载".to_string(),
        )
        .await?;
    sleep(Duration::from_millis(100)).await;

    state_machine
        .transition(
            AsyncState::Loading,
            AsyncState::Ready,
            "加载完成".to_string(),
        )
        .await?;
    sleep(Duration::from_millis(50)).await;

    state_machine
        .transition(
            AsyncState::Ready,
            AsyncState::Processing,
            "开始处理".to_string(),
        )
        .await?;
    sleep(Duration::from_millis(100)).await;

    state_machine
        .transition(
            AsyncState::Processing,
            AsyncState::Completed,
            "处理完成".to_string(),
        )
        .await?;

    let final_state = state_machine.get_state().await;
    let transitions = state_machine.get_transitions().await;

    info!("最终状态: {:?}", final_state);
    info!("状态转换历史: {:?}", transitions);

    Ok(())
}

#[instrument]
async fn demo_async_observer() -> Result<()> {
    info!("👀 演示异步观察者模式");

    let subject = AsyncSubject::new();

    // 创建观察者
    let observer1 = AsyncObserver::EventLogger(AsyncEventLogger::new("Observer1".to_string()));
    let observer2 = AsyncObserver::EventLogger(AsyncEventLogger::new("Observer2".to_string()));
    let observer3 = AsyncObserver::EventLogger(AsyncEventLogger::new("Observer3".to_string()));

    // 订阅观察者
    subject.subscribe(observer1).await;
    subject.subscribe(observer2).await;
    subject.subscribe(observer3).await;

    info!("观察者数量: {}", subject.observer_count().await);

    // 发送事件
    subject.notify_all("Event1").await?;
    sleep(Duration::from_millis(50)).await;

    subject.notify_all("Event2").await?;
    sleep(Duration::from_millis(50)).await;

    subject.notify_all("Event3").await?;

    Ok(())
}

#[instrument]
async fn demo_async_command() -> Result<()> {
    info!("📝 演示异步命令模式");

    let invoker = AsyncCommandInvoker::new();

    // 执行命令
    let cmd1 = AsyncCommand::LogCommand(AsyncLogCommand::new("创建文件".to_string()));
    invoker.execute_command(cmd1).await?;

    let cmd2 = AsyncCommand::LogCommand(AsyncLogCommand::new("写入数据".to_string()));
    invoker.execute_command(cmd2).await?;

    let cmd3 = AsyncCommand::LogCommand(AsyncLogCommand::new("保存文件".to_string()));
    invoker.execute_command(cmd3).await?;

    // 撤销命令
    if invoker.can_undo().await {
        invoker.undo().await?;
    }

    // 重做命令
    if invoker.can_redo().await {
        invoker.redo().await?;
    }

    Ok(())
}

#[instrument]
async fn demo_async_chain_of_responsibility() -> Result<()> {
    info!("⛓️ 演示异步责任链模式");

    let chain = AsyncChainBuilder::new()
        .add_handler(AsyncHandler::Validation(AsyncValidationHandler::new(
            "验证".to_string(),
        )))
        .add_handler(AsyncHandler::Processing(AsyncProcessingHandler::new(
            "处理".to_string(),
        )))
        .add_handler(AsyncHandler::Logging(AsyncLoggingHandler::new(
            "日志".to_string(),
        )))
        .build();

    let result = chain.process("请求数据".to_string()).await?;
    info!("责任链处理结果: {}", result);

    Ok(())
}

#[instrument]
async fn demo_async_adapter() -> Result<()> {
    info!("🔌 演示异步适配器模式");

    let adaptee = Arc::new(SyncAdapteeImpl);
    let adapter = AsyncAdapter::new(adaptee);

    let result = adapter.async_request().await?;
    info!("适配器结果: {}", result);

    Ok(())
}

#[instrument]
async fn demo_async_decorator() -> Result<()> {
    info!("🎨 演示异步装饰器模式");

    let component = AsyncComponent::Concrete(AsyncConcreteComponent);
    let decorated =
        AsyncComponent::Decorator(AsyncDecorator::new(component, "Decorated".to_string()));
    let double_decorated = AsyncComponent::Decorator(AsyncDecorator::new(
        decorated,
        "DoubleDecorated".to_string(),
    ));

    let result = double_decorated.operation().await?;
    info!("装饰器结果: {}", result);

    Ok(())
}

#[instrument]
async fn demo_async_facade() -> Result<()> {
    info!("🏛️ 演示异步门面模式");

    let facade = AsyncFacade::new();
    let result = facade.complex_operation().await?;
    info!("门面结果: {}", result);

    Ok(())
}

#[instrument]
async fn demo_async_singleton() -> Result<()> {
    info!("🔒 演示异步单例模式");

    let singleton1 = AsyncSingleton::get_instance().await;
    let singleton2 = AsyncSingleton::get_instance().await;

    // 验证是同一个实例
    singleton1.set_data("Singleton Data 1".to_string()).await;
    let data2 = singleton2.get_data().await;

    info!("单例数据: {}", data2);
    assert_eq!(data2, "Singleton Data 1");

    Ok(())
}

#[instrument]
async fn demo_async_builder() -> Result<()> {
    info!("🔨 演示异步建造者模式");

    let product = AsyncBuilder::new()
        .build_part_a("数据A".to_string())
        .await
        .build_part_b("数据B".to_string())
        .await
        .build_part_c("数据C".to_string())
        .await
        .build()?;

    info!(
        "建造者结果: {} + {} + {}",
        product.part_a, product.part_b, product.part_c
    );

    Ok(())
}

#[instrument]
async fn demo_async_strategy() -> Result<()> {
    info!("⚡ 演示异步策略模式");

    let mut context = AsyncContext::new(AsyncStrategy::StrategyA(AsyncStrategyA));

    let result1 = context.execute_strategy("Hello World".to_string()).await?;
    info!("策略A结果: {}", result1);

    context.set_strategy(AsyncStrategy::StrategyB(AsyncStrategyB));
    let result2 = context.execute_strategy("Hello World".to_string()).await?;
    info!("策略B结果: {}", result2);

    context.set_strategy(AsyncStrategy::StrategyC(AsyncStrategyC));
    let result3 = context.execute_strategy("Hello World".to_string()).await?;
    info!("策略C结果: {}", result3);

    Ok(())
}

// 辅助结构体和实现

pub struct AsyncEventLogger {
    name: String,
}

impl AsyncEventLogger {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl AsyncEventLogger {
    pub async fn notify(&self, event: &str) -> Result<()> {
        info!("{} 收到事件: {}", self.name, event);
        Ok(())
    }
}

pub struct AsyncLogCommand {
    description: String,
}

impl AsyncLogCommand {
    fn new(description: String) -> Self {
        Self { description }
    }
}

impl AsyncLogCommand {
    pub async fn execute(&self) -> Result<()> {
        info!("执行命令: {}", self.description);
        Ok(())
    }

    pub async fn undo(&self) -> Result<()> {
        info!("撤销命令: {}", self.description);
        Ok(())
    }

    pub fn description(&self) -> String {
        self.description.clone()
    }
}

pub struct AsyncValidationHandler {
    name: String,
}

impl AsyncValidationHandler {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl AsyncValidationHandler {
    pub async fn handle(&self, request: &str) -> Result<Option<String>> {
        info!("{} 处理: {}", self.name, request);
        sleep(Duration::from_millis(50)).await;
        Ok(Some(format!("Validated: {}", request)))
    }
}

pub struct AsyncProcessingHandler {
    name: String,
}

impl AsyncProcessingHandler {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl AsyncProcessingHandler {
    pub async fn handle(&self, request: &str) -> Result<Option<String>> {
        info!("{} 处理: {}", self.name, request);
        sleep(Duration::from_millis(100)).await;
        Ok(Some(format!("Processed: {}", request)))
    }
}

pub struct AsyncLoggingHandler {
    name: String,
}

impl AsyncLoggingHandler {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl AsyncLoggingHandler {
    pub async fn handle(&self, request: &str) -> Result<Option<String>> {
        info!("{} 处理: {}", self.name, request);
        sleep(Duration::from_millis(75)).await;
        Ok(Some(format!("Logged: {}", request)))
    }
}

struct SyncAdapteeImpl;

impl AsyncAdaptee for SyncAdapteeImpl {
    fn sync_request(&self) -> Result<String> {
        Ok("Sync Adaptee Response".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_state_machine() {
        let sm = AsyncStateMachine::new(AsyncState::Idle);
        assert_eq!(sm.get_state().await, AsyncState::Idle);

        sm.transition(AsyncState::Idle, AsyncState::Loading, "test".to_string())
            .await
            .unwrap();
        assert_eq!(sm.get_state().await, AsyncState::Loading);
    }

    #[tokio::test]
    async fn test_async_singleton() {
        let s1 = AsyncSingleton::get_instance().await;
        let s2 = AsyncSingleton::get_instance().await;

        s1.set_data("test".to_string()).await;
        assert_eq!(s2.get_data().await, "test");
    }

    #[tokio::test]
    async fn test_async_builder() {
        let product = AsyncBuilder::new()
            .build_part_a("a".to_string())
            .await
            .build_part_b("b".to_string())
            .await
            .build_part_c("c".to_string())
            .await
            .build()
            .unwrap();

        assert!(product.part_a.contains("AsyncPartA"));
        assert!(product.part_b.contains("AsyncPartB"));
        assert!(product.part_c.contains("AsyncPartC"));
    }
}
