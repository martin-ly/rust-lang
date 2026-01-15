//! 组合模式工程案例
//!
//! 本模块展示了如何组合多个设计模式来解决复杂的工程问题。
//! 这些案例展示了模式之间的协作和组合使用。

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// ============================================================================
// 案例 A：Web 服务
// 组合：Facade + Builder + Strategy（路由策略）+ Circuit Breaker（并发模式）
// ============================================================================

/// HTTP 请求
#[derive(Debug, Clone)]
pub struct HttpRequest {
    pub method: String,
    pub path: String,
    pub headers: HashMap<String, String>,
    pub body: Option<String>,
}

/// HTTP 响应
#[derive(Debug, Clone)]
pub struct HttpResponse {
    pub status_code: u16,
    pub headers: HashMap<String, String>,
    pub body: String,
}

/// 路由策略 trait（Strategy 模式）
pub trait RoutingStrategy: Send + Sync {
    fn route(&self, request: &HttpRequest) -> Option<String>;
}

/// 精确匹配路由策略
pub struct ExactMatchRouting {
    routes: HashMap<String, String>,
}

impl ExactMatchRouting {
    pub fn new() -> Self {
        let mut routes = HashMap::new();
        routes.insert("/api/users".to_string(), "UserService".to_string());
        routes.insert("/api/posts".to_string(), "PostService".to_string());
        routes.insert("/api/comments".to_string(), "CommentService".to_string());
        Self { routes }
    }
}

impl RoutingStrategy for ExactMatchRouting {
    fn route(&self, request: &HttpRequest) -> Option<String> {
        self.routes.get(&request.path).cloned()
    }
}

/// 前缀匹配路由策略
pub struct PrefixMatchRouting {
    prefixes: Vec<(String, String)>,
}

impl PrefixMatchRouting {
    pub fn new() -> Self {
        let prefixes = vec![
            ("/api/users".to_string(), "UserService".to_string()),
            ("/api/posts".to_string(), "PostService".to_string()),
            ("/api".to_string(), "ApiService".to_string()),
        ];
        Self { prefixes }
    }
}

impl RoutingStrategy for PrefixMatchRouting {
    fn route(&self, request: &HttpRequest) -> Option<String> {
        self.prefixes
            .iter()
            .find(|(prefix, _)| request.path.starts_with(prefix))
            .map(|(_, service)| service.clone())
    }
}

/// HTTP 请求构建器（Builder 模式）
pub struct HttpRequestBuilder {
    method: Option<String>,
    path: Option<String>,
    headers: HashMap<String, String>,
    body: Option<String>,
}

impl HttpRequestBuilder {
    pub fn new() -> Self {
        Self {
            method: None,
            path: None,
            headers: HashMap::new(),
            body: None,
        }
    }

    pub fn method(mut self, method: impl Into<String>) -> Self {
        self.method = Some(method.into());
        self
    }

    pub fn path(mut self, path: impl Into<String>) -> Self {
        self.path = Some(path.into());
        self
    }

    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }

    pub fn body(mut self, body: impl Into<String>) -> Self {
        self.body = Some(body.into());
        self
    }

    pub fn build(self) -> Result<HttpRequest, String> {
        Ok(HttpRequest {
            method: self.method.ok_or("Method is required")?,
            path: self.path.ok_or("Path is required")?,
            headers: self.headers,
            body: self.body,
        })
    }
}

/// 断路器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    Closed,   // 正常
    Open,     // 断开（快速失败）
    HalfOpen, // 半开（尝试恢复）
}

/// 断路器（Circuit Breaker 模式）
pub struct CircuitBreaker {
    failure_threshold: u64,
    success_threshold: u64,
    timeout: Duration,
    failures: AtomicU64,
    successes: AtomicU64,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    state: Arc<Mutex<CircuitState>>,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u64, success_threshold: u64, timeout: Duration) -> Self {
        Self {
            failure_threshold,
            success_threshold,
            timeout,
            failures: AtomicU64::new(0),
            successes: AtomicU64::new(0),
            last_failure_time: Arc::new(Mutex::new(None)),
            state: Arc::new(Mutex::new(CircuitState::Closed)),
        }
    }

    pub fn call<F, T>(&self, f: F) -> Result<T, String>
    where
        F: FnOnce() -> Result<T, String>,
    {
        let state = *self.state.lock().unwrap();

        match state {
            CircuitState::Open => {
                // 检查是否可以尝试恢复
                let last_failure = self.last_failure_time.lock().unwrap();
                if let Some(time) = *last_failure {
                    if time.elapsed() > self.timeout {
                        *self.state.lock().unwrap() = CircuitState::HalfOpen;
                    } else {
                        return Err("Circuit breaker is open".to_string());
                    }
                } else {
                    return Err("Circuit breaker is open".to_string());
                }
            }
            _ => {}
        }

        // 执行调用
        match f() {
            Ok(result) => {
                self.on_success();
                Ok(result)
            }
            Err(e) => {
                self.on_failure();
                Err(e)
            }
        }
    }

    fn on_success(&self) {
        self.successes.fetch_add(1, Ordering::Relaxed);

        let state = *self.state.lock().unwrap();
        if state == CircuitState::HalfOpen {
            if self.successes.load(Ordering::Relaxed) >= self.success_threshold {
                *self.state.lock().unwrap() = CircuitState::Closed;
                self.successes.store(0, Ordering::Relaxed);
                self.failures.store(0, Ordering::Relaxed);
            }
        }
    }

    fn on_failure(&self) {
        self.failures.fetch_add(1, Ordering::Relaxed);
        *self.last_failure_time.lock().unwrap() = Some(Instant::now());

        if self.failures.load(Ordering::Relaxed) >= self.failure_threshold {
            *self.state.lock().unwrap() = CircuitState::Open;
        }
    }

    pub fn get_state(&self) -> CircuitState {
        *self.state.lock().unwrap()
    }
}

/// 服务接口
pub trait Service: Send + Sync {
    fn handle(&self, request: &HttpRequest) -> Result<HttpResponse, String>;
}

/// 用户服务
pub struct UserService;

impl Service for UserService {
    fn handle(&self, _request: &HttpRequest) -> Result<HttpResponse, String> {
        Ok(HttpResponse {
            status_code: 200,
            headers: HashMap::new(),
            body: r#"{"users": [{"id": 1, "name": "Alice"}]}"#.to_string(),
        })
    }
}

/// 文章服务
pub struct PostService;

impl Service for PostService {
    fn handle(&self, _request: &HttpRequest) -> Result<HttpResponse, String> {
        Ok(HttpResponse {
            status_code: 200,
            headers: HashMap::new(),
            body: r#"{"posts": [{"id": 1, "title": "Hello Rust"}]}"#.to_string(),
        })
    }
}

/// Web 服务器外观（Facade 模式）
/// 组合了 Builder、Strategy 和 Circuit Breaker 模式
pub struct WebServerFacade {
    routing_strategy: Box<dyn RoutingStrategy>,
    services: HashMap<String, Arc<dyn Service>>,
    circuit_breaker: Arc<CircuitBreaker>,
    request_count: AtomicU64,
    error_count: AtomicU64,
}

impl WebServerFacade {
    pub fn new(routing_strategy: Box<dyn RoutingStrategy>) -> Self {
        let mut services = HashMap::new();
        services.insert("UserService".to_string(), Arc::new(UserService) as Arc<dyn Service>);
        services.insert("PostService".to_string(), Arc::new(PostService) as Arc<dyn Service>);

        let circuit_breaker = Arc::new(CircuitBreaker::new(
            5,                              // 失败阈值
            3,                              // 成功阈值
            Duration::from_secs(10),        // 超时时间
        ));

        Self {
            routing_strategy,
            services,
            circuit_breaker,
            request_count: AtomicU64::new(0),
            error_count: AtomicU64::new(0),
        }
    }

    /// 处理 HTTP 请求（Facade 模式简化接口）
    pub fn handle_request(&self, request: HttpRequest) -> Result<HttpResponse, String> {
        self.request_count.fetch_add(1, Ordering::Relaxed);

        // 使用路由策略找到服务
        let service_name = match self.routing_strategy.route(&request) {
            Some(name) => name,
            None => {
                self.error_count.fetch_add(1, Ordering::Relaxed);
                return Err("Route not found".to_string());
            }
        };

        // 使用断路器保护服务调用
        let circuit_breaker = self.circuit_breaker.clone();
        let service = match self.services.get(&service_name) {
            Some(svc) => svc.clone(),
            None => {
                self.error_count.fetch_add(1, Ordering::Relaxed);
                return Err("Service not found".to_string());
            }
        };

        let result = circuit_breaker.call(|| service.handle(&request));

        match &result {
            Err(_) => {
                self.error_count.fetch_add(1, Ordering::Relaxed);
            }
            _ => {}
        }

        result
    }

    pub fn get_stats(&self) -> ServerStats {
        ServerStats {
            total_requests: self.request_count.load(Ordering::Relaxed),
            total_errors: self.error_count.load(Ordering::Relaxed),
            circuit_state: self.circuit_breaker.get_state(),
        }
    }
}

/// 服务器统计信息
#[derive(Debug, Clone)]
pub struct ServerStats {
    pub total_requests: u64,
    pub total_errors: u64,
    pub circuit_state: CircuitState,
}

// ============================================================================
// 案例 B：游戏引擎子系统
// 组合：Observer（事件总线）+ Command（输入映射）+ State（AI 状态机）
// ============================================================================

/// 游戏事件（Observer 模式）
#[derive(Debug, Clone)]
pub enum GameEvent {
    PlayerInput {
        input: String,
        timestamp: Instant,
    },
    StateChanged {
        from: String,
        to: String,
    },
    CommandExecuted {
        command: String,
    },
}

/// 观察者 trait
pub trait EventObserver: Send {
    fn on_event(&mut self, event: &GameEvent);
}

/// 事件总线（Observer 模式）
pub struct EventBus {
    observers: Vec<Box<dyn EventObserver>>,
}

impl EventBus {
    pub fn new() -> Self {
        Self {
            observers: Vec::new(),
        }
    }

    pub fn subscribe(&mut self, observer: Box<dyn EventObserver>) {
        self.observers.push(observer);
    }

    pub fn publish(&mut self, event: GameEvent) {
        for observer in self.observers.iter_mut() {
            observer.on_event(&event);
        }
    }
}

/// 命令 trait（Command 模式）
pub trait GameCommand: Send + Sync {
    fn execute(&self, context: &mut GameContext) -> Result<(), String>;
    fn name(&self) -> &str;
}

/// 移动命令
pub struct MoveCommand {
    direction: String,
}

impl MoveCommand {
    pub fn new(direction: String) -> Self {
        Self { direction }
    }
}

impl GameCommand for MoveCommand {
    fn execute(&self, context: &mut GameContext) -> Result<(), String> {
        context.player_position += 1;
        println!("执行移动命令: 向{}移动，新位置: {}", self.direction, context.player_position);
        Ok(())
    }

    fn name(&self) -> &str {
        "Move"
    }
}

/// 攻击命令
pub struct AttackCommand;

impl GameCommand for AttackCommand {
    fn execute(&self, context: &mut GameContext) -> Result<(), String> {
        context.enemy_health = context.enemy_health.saturating_sub(10);
        println!("执行攻击命令，敌人剩余血量: {}", context.enemy_health);
        Ok(())
    }

    fn name(&self) -> &str {
        "Attack"
    }
}

/// 游戏上下文
pub struct GameContext {
    pub player_position: i32,
    pub enemy_health: u32,
}

impl GameContext {
    pub fn new() -> Self {
        Self {
            player_position: 0,
            enemy_health: 100,
        }
    }
}

/// 命令映射器（Command 模式）
pub struct CommandMapper {
    commands: HashMap<String, Box<dyn GameCommand>>,
}

impl CommandMapper {
    pub fn new() -> Self {
        // 先插入不同类型的命令以强制类型推断为 trait object
        let mut commands: HashMap<String, Box<dyn GameCommand>> = {
            let mut map = HashMap::new();
            map.insert("attack".to_string(), Box::new(AttackCommand) as Box<dyn GameCommand>);
            map
        };

        commands.insert("w".to_string(), Box::new(MoveCommand::new("上".to_string())) as Box<dyn GameCommand>);
        commands.insert("s".to_string(), Box::new(MoveCommand::new("下".to_string())) as Box<dyn GameCommand>);
        commands.insert("a".to_string(), Box::new(MoveCommand::new("左".to_string())) as Box<dyn GameCommand>);
        commands.insert("d".to_string(), Box::new(MoveCommand::new("右".to_string())) as Box<dyn GameCommand>);

        Self { commands }
    }

    pub fn execute_command(&self, input: &str, context: &mut GameContext) -> Result<(), String> {
        let command = self
            .commands
            .get(input)
            .ok_or_else(|| format!("Unknown command: {}", input))?;

        command.execute(context)
    }
}

/// AI 状态（State 模式）
pub trait AiState: Send {
    fn enter(&mut self, context: &mut GameContext);
    fn update(&mut self, context: &mut GameContext) -> Option<Box<dyn AiState>>;
    fn exit(&mut self, context: &mut GameContext);
    fn name(&self) -> &str;
}

/// 巡逻状态
pub struct PatrolState {
    patrol_count: u32,
}

impl PatrolState {
    pub fn new() -> Self {
        Self { patrol_count: 0 }
    }
}

impl AiState for PatrolState {
    fn enter(&mut self, _context: &mut GameContext) {
        println!("AI 进入巡逻状态");
    }

    fn update(&mut self, context: &mut GameContext) -> Option<Box<dyn AiState>> {
        self.patrol_count += 1;
        context.player_position += 1;
        println!("AI 巡逻中... (计数: {})", self.patrol_count);

        if context.player_position > 10 {
            Some(Box::new(ChaseState::new()))
        } else {
            None
        }
    }

    fn exit(&mut self, _context: &mut GameContext) {
        println!("AI 退出巡逻状态");
    }

    fn name(&self) -> &str {
        "Patrol"
    }
}

/// 追逐状态
pub struct ChaseState {
    chase_count: u32,
}

impl ChaseState {
    pub fn new() -> Self {
        Self { chase_count: 0 }
    }
}

impl AiState for ChaseState {
    fn enter(&mut self, _context: &mut GameContext) {
        println!("AI 进入追逐状态");
    }

    fn update(&mut self, context: &mut GameContext) -> Option<Box<dyn AiState>> {
        self.chase_count += 1;
        context.player_position += 2; // 追逐时移动更快
        println!("AI 追逐中... (计数: {})", self.chase_count);

        if context.enemy_health < 50 {
            Some(Box::new(FleeState::new()))
        } else if context.player_position < 5 {
            Some(Box::new(PatrolState::new()))
        } else {
            None
        }
    }

    fn exit(&mut self, _context: &mut GameContext) {
        println!("AI 退出追逐状态");
    }

    fn name(&self) -> &str {
        "Chase"
    }
}

/// 逃跑状态
pub struct FleeState;

impl FleeState {
    pub fn new() -> Self {
        Self
    }
}

impl AiState for FleeState {
    fn enter(&mut self, _context: &mut GameContext) {
        println!("AI 进入逃跑状态");
    }

    fn update(&mut self, context: &mut GameContext) -> Option<Box<dyn AiState>> {
        context.player_position = context.player_position.saturating_sub(3);
        println!("AI 逃跑中...");

        if context.enemy_health > 80 {
            Some(Box::new(PatrolState::new()))
        } else {
            None
        }
    }

    fn exit(&mut self, _context: &mut GameContext) {
        println!("AI 退出逃跑状态");
    }

    fn name(&self) -> &str {
        "Flee"
    }
}

/// AI 状态管理器（State 模式）
pub struct AiStateManager {
    current_state: Option<Box<dyn AiState>>,
}

impl AiStateManager {
    pub fn new() -> Self {
        Self {
            current_state: Some(Box::new(PatrolState::new())),
        }
    }

    pub fn update(&mut self, context: &mut GameContext) {
        if let Some(mut state) = self.current_state.take() {
            if let Some(new_state) = state.update(context) {
                state.exit(context);
                let mut new_state = new_state;
                new_state.enter(context);
                self.current_state = Some(new_state);
            } else {
                self.current_state = Some(state);
            }
        }
    }

    pub fn get_current_state_name(&self) -> Option<String> {
        self.current_state.as_ref().map(|s| s.name().to_string())
    }
}

/// 日志观察者
pub struct LoggingObserver {
    logs: Vec<String>,
}

impl LoggingObserver {
    pub fn new() -> Self {
        Self { logs: Vec::new() }
    }

    pub fn get_logs(&self) -> &[String] {
        &self.logs
    }
}

impl EventObserver for LoggingObserver {
    fn on_event(&mut self, event: &GameEvent) {
        let log = format!("[LOG] {:?}", event);
        self.logs.push(log.clone());
        println!("{}", log);
    }
}

/// 游戏引擎（组合 Observer + Command + State）
pub struct GameEngine {
    event_bus: EventBus,
    command_mapper: CommandMapper,
    ai_state_manager: AiStateManager,
    context: GameContext,
}

impl GameEngine {
    pub fn new() -> Self {
        let mut event_bus = EventBus::new();
        event_bus.subscribe(Box::new(LoggingObserver::new()));

        Self {
            event_bus,
            command_mapper: CommandMapper::new(),
            ai_state_manager: AiStateManager::new(),
            context: GameContext::new(),
        }
    }

    pub fn process_input(&mut self, input: &str) -> Result<(), String> {
        // 发布输入事件
        self.event_bus.publish(GameEvent::PlayerInput {
            input: input.to_string(),
            timestamp: Instant::now(),
        });

        // 执行命令
        self.command_mapper
            .execute_command(input, &mut self.context)?;

        // 发布命令执行事件
        self.event_bus.publish(GameEvent::CommandExecuted {
            command: input.to_string(),
        });

        Ok(())
    }

    pub fn update_ai(&mut self) {
        let old_state = self.ai_state_manager.get_current_state_name();
        self.ai_state_manager.update(&mut self.context);
        let new_state = self.ai_state_manager.get_current_state_name();

        if old_state != new_state {
            self.event_bus.publish(GameEvent::StateChanged {
                from: old_state.unwrap_or_default(),
                to: new_state.unwrap_or_default(),
            });
        }
    }

    pub fn get_context(&self) -> &GameContext {
        &self.context
    }

    pub fn get_ai_state_name(&self) -> Option<String> {
        self.ai_state_manager.get_current_state_name()
    }
}

// ============================================================================
// 单元测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_web_server_facade() {
        let routing_strategy = Box::new(ExactMatchRouting::new());
        let server = WebServerFacade::new(routing_strategy);

        let request = HttpRequestBuilder::new()
            .method("GET")
            .path("/api/users")
            .build()
            .unwrap();

        let response = server.handle_request(request).unwrap();
        assert_eq!(response.status_code, 200);
        assert!(response.body.contains("users"));

        let stats = server.get_stats();
        assert_eq!(stats.total_requests, 1);
    }

    #[test]
    fn test_circuit_breaker() {
        let breaker = CircuitBreaker::new(3, 2, Duration::from_secs(1));

        // 模拟失败
        for _ in 0..3 {
            let _: Result<(), String> = breaker.call(|| Err("Error".to_string()));
        }

        assert_eq!(breaker.get_state(), CircuitState::Open);

        // 断路器打开时应该快速失败
        let result: Result<i32, String> = breaker.call(|| Ok(42));
        assert!(result.is_err());
    }

    #[test]
    fn test_game_engine() {
        let mut engine = GameEngine::new();

        // 处理输入
        engine.process_input("w").unwrap();
        assert_eq!(engine.get_context().player_position, 1);

        // 更新 AI
        engine.update_ai();
        assert!(engine.ai_state_manager.get_current_state_name().is_some());
    }

    #[test]
    fn test_command_mapper() {
        let mapper = CommandMapper::new();
        let mut context = GameContext::new();

        mapper.execute_command("w", &mut context).unwrap();
        assert_eq!(context.player_position, 1);

        mapper.execute_command("attack", &mut context).unwrap();
        assert_eq!(context.enemy_health, 90);
    }

    #[test]
    fn test_ai_state_transitions() {
        let mut manager = AiStateManager::new();
        let mut context = GameContext::new();

        // 初始状态应该是 Patrol
        assert_eq!(manager.get_current_state_name(), Some("Patrol".to_string()));

        // 更新直到状态转换
        for _ in 0..15 {
            manager.update(&mut context);
        }

        // 应该转换到 Chase 状态
        let state_name = manager.get_current_state_name();
        assert!(state_name.is_some());
    }
}
