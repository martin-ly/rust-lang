//! P10-3 惯用法、设计模式与架构模式实现集合。
//!
//! 对应 `concept/05_comparative/05_idioms_patterns_architecture/` 权威页代码示例。

use std::collections::HashMap;
use std::sync::mpsc::{channel, Sender};

// ===========================================================================
// 一、惯用法（Idioms）
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Into / From / AsRef 转换惯用法
// ---------------------------------------------------------------------------

/// 领域用户名，演示 `From` / `Into` 的零成本转换。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UserName(String);

impl From<String> for UserName {
    fn from(value: String) -> Self {
        UserName(value.trim().to_lowercase())
    }
}

impl From<&str> for UserName {
    fn from(value: &str) -> Self {
        UserName(value.trim().to_lowercase())
    }
}

impl AsRef<str> for UserName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

/// 通过泛型边界接受任何可转换为 `UserName` 的类型。
pub fn greet<N: Into<UserName>>(name: N) -> String {
    format!("Hello, {}!", name.into().as_ref())
}

// ---------------------------------------------------------------------------
// 2. Newtype 惯用法
// ---------------------------------------------------------------------------

/// 用 Newtype 包装原始类型，避免单位混淆。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Kilometers(u32);

impl Kilometers {
    pub fn new(value: u32) -> Self {
        Self(value)
    }

    pub fn value(&self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Miles(u32);

impl Miles {
    pub fn new(value: u32) -> Self {
        Self(value)
    }

    pub fn to_kilometers(&self) -> Kilometers {
        Kilometers(self.0 * 161 / 100)
    }
}

// ---------------------------------------------------------------------------
// 3. Typestate 惯用法
// ---------------------------------------------------------------------------

/// 尚未启动的构建器状态。
pub struct Idle;
/// 已配置的状态。
pub struct Configured;
/// 已启动并运行中的状态。
pub struct Running;

/// Typestate 状态机：编译期保证状态转换合法。
pub struct Workflow<S> {
    name: String,
    _state: std::marker::PhantomData<S>,
}

impl Workflow<Idle> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            _state: std::marker::PhantomData,
        }
    }

    pub fn configure(self) -> Workflow<Configured> {
        Workflow {
            name: self.name,
            _state: std::marker::PhantomData,
        }
    }
}

impl Workflow<Configured> {
    pub fn start(self) -> Workflow<Running> {
        Workflow {
            name: self.name,
            _state: std::marker::PhantomData,
        }
    }
}

impl Workflow<Running> {
    pub fn status(&self) -> String {
        format!("{} is running", self.name)
    }
}

// ---------------------------------------------------------------------------
// 4. Builder 惯用法
// ---------------------------------------------------------------------------

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct HttpRequest {
    method: String,
    url: String,
    headers: HashMap<String, String>,
    body: Option<String>,
}

#[derive(Debug, Default)]
pub struct HttpRequestBuilder {
    method: Option<String>,
    url: Option<String>,
    headers: HashMap<String, String>,
    body: Option<String>,
}

impl HttpRequestBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn method(mut self, method: impl Into<String>) -> Self {
        self.method = Some(method.into());
        self
    }

    pub fn url(mut self, url: impl Into<String>) -> Self {
        self.url = Some(url.into());
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
            method: self.method.ok_or("method is required")?,
            url: self.url.ok_or("url is required")?,
            headers: self.headers,
            body: self.body,
        })
    }
}

// ---------------------------------------------------------------------------
// 5. Defer / Cleanup 惯用法（基于 Drop 的 RAII 封装）
// ---------------------------------------------------------------------------

/// 在作用域退出时执行回调。
pub struct ScopeGuard<F: FnOnce()> {
    callback: Option<F>,
}

impl<F: FnOnce()> ScopeGuard<F> {
    pub fn new(callback: F) -> Self {
        Self {
            callback: Some(callback),
        }
    }

    /// 主动释放 guard，阻止回调执行。
    pub fn dismiss(mut self) {
        self.callback.take();
    }
}

impl<F: FnOnce()> Drop for ScopeGuard<F> {
    fn drop(&mut self) {
        if let Some(callback) = self.callback.take() {
            callback();
        }
    }
}

/// 创建 defer guard 的宏。
#[macro_export]
macro_rules! defer {
    ($body:expr) => {
        let _guard = $crate::p10_idioms_patterns::ScopeGuard::new(|| $body);
    };
}

// ===========================================================================
// 二、设计模式（Design Patterns）
// ===========================================================================

// ---------------------------------------------------------------------------
// 6. Strategy 策略模式
// ---------------------------------------------------------------------------

pub trait PaymentStrategy: Send + Sync {
    fn pay(&self, amount: u64) -> String;
}

pub struct CreditCard;
impl PaymentStrategy for CreditCard {
    fn pay(&self, amount: u64) -> String {
        format!("Paid {} via credit card", amount)
    }
}

pub struct PayPal;
impl PaymentStrategy for PayPal {
    fn pay(&self, amount: u64) -> String {
        format!("Paid {} via PayPal", amount)
    }
}

pub struct Checkout<'a> {
    strategy: &'a dyn PaymentStrategy,
}

impl<'a> Checkout<'a> {
    pub fn new(strategy: &'a dyn PaymentStrategy) -> Self {
        Self { strategy }
    }

    pub fn execute(&self, amount: u64) -> String {
        self.strategy.pay(amount)
    }
}

// ---------------------------------------------------------------------------
// 7. Command 命令模式
// ---------------------------------------------------------------------------

pub trait Command: Send + Sync {
    fn execute(&self) -> String;
    fn undo(&self) -> String;
}

pub struct Light;
impl Light {
    pub fn turn_on(&self) -> &'static str {
        "Light is on"
    }
    pub fn turn_off(&self) -> &'static str {
        "Light is off"
    }
}

pub struct TurnOnCommand {
    light: Light,
}
impl TurnOnCommand {
    pub fn new(light: Light) -> Self {
        Self { light }
    }
}
impl Command for TurnOnCommand {
    fn execute(&self) -> String {
        self.light.turn_on().to_string()
    }
    fn undo(&self) -> String {
        self.light.turn_off().to_string()
    }
}

pub struct RemoteControl {
    history: Vec<Box<dyn Command>>,
}

impl RemoteControl {
    pub fn new() -> Self {
        Self { history: Vec::new() }
    }

    pub fn press(&mut self, command: Box<dyn Command>) -> String {
        let result = command.execute();
        self.history.push(command);
        result
    }

    pub fn undo_last(&mut self) -> Option<String> {
        self.history.pop().map(|c| c.undo())
    }
}

// ---------------------------------------------------------------------------
// 8. Visitor 访问者模式
// ---------------------------------------------------------------------------

pub trait ShapeVisitor {
    fn visit_circle(&mut self, circle: &Circle);
    fn visit_rectangle(&mut self, rectangle: &Rectangle);
}

pub trait Shape {
    fn accept(&self, visitor: &mut dyn ShapeVisitor);
}

pub struct Circle {
    pub radius: f64,
}
impl Shape for Circle {
    fn accept(&self, visitor: &mut dyn ShapeVisitor) {
        visitor.visit_circle(self);
    }
}

pub struct Rectangle {
    pub width: f64,
    pub height: f64,
}
impl Shape for Rectangle {
    fn accept(&self, visitor: &mut dyn ShapeVisitor) {
        visitor.visit_rectangle(self);
    }
}

pub struct AreaVisitor {
    pub total: f64,
}
impl ShapeVisitor for AreaVisitor {
    fn visit_circle(&mut self, circle: &Circle) {
        self.total += std::f64::consts::PI * circle.radius * circle.radius;
    }
    fn visit_rectangle(&mut self, rectangle: &Rectangle) {
        self.total += rectangle.width * rectangle.height;
    }
}

// ---------------------------------------------------------------------------
// 9. State Machine 状态机模式
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnstileState {
    Locked,
    Unlocked,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnstileEvent {
    Coin,
    Push,
}

impl TurnstileState {
    pub fn transition(&self, event: TurnstileEvent) -> (Self, &'static str) {
        match (self, event) {
            (TurnstileState::Locked, TurnstileEvent::Coin) => {
                (TurnstileState::Unlocked, "Unlocking turnstile")
            }
            (TurnstileState::Unlocked, TurnstileEvent::Push) => {
                (TurnstileState::Locked, "Locking turnstile")
            }
            (TurnstileState::Locked, TurnstileEvent::Push) => {
                (TurnstileState::Locked, "Please insert a coin")
            }
            (TurnstileState::Unlocked, TurnstileEvent::Coin) => {
                (TurnstileState::Unlocked, "Already unlocked")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 10. Adapter 适配器模式
// ---------------------------------------------------------------------------

/// 目标接口。
pub trait MediaPlayer {
    fn play(&self, filename: &str) -> String;
}

/// 第三方高级播放器。
pub struct AdvancedMediaPlayer;
impl AdvancedMediaPlayer {
    pub fn play_mp4(&self, filename: &str) -> String {
        format!("Playing mp4: {}", filename)
    }
}

/// 适配器：将第三方播放器适配到目标接口。
pub struct MediaAdapter {
    advanced: AdvancedMediaPlayer,
}

impl MediaAdapter {
    pub fn new() -> Self {
        Self {
            advanced: AdvancedMediaPlayer,
        }
    }
}

impl MediaPlayer for MediaAdapter {
    fn play(&self, filename: &str) -> String {
        if filename.ends_with(".mp4") {
            self.advanced.play_mp4(filename)
        } else {
            format!("Unsupported format: {}", filename)
        }
    }
}

// ---------------------------------------------------------------------------
// 11. Decorator 装饰器模式
// ---------------------------------------------------------------------------

pub trait Coffee {
    fn cost(&self) -> u64;
    fn description(&self) -> String;
}

pub struct SimpleCoffee;
impl Coffee for SimpleCoffee {
    fn cost(&self) -> u64 {
        10
    }
    fn description(&self) -> String {
        "Simple coffee".to_string()
    }
}

pub struct MilkDecorator<C: Coffee> {
    coffee: C,
}

impl<C: Coffee> MilkDecorator<C> {
    pub fn new(coffee: C) -> Self {
        Self { coffee }
    }
}

impl<C: Coffee> Coffee for MilkDecorator<C> {
    fn cost(&self) -> u64 {
        self.coffee.cost() + 2
    }
    fn description(&self) -> String {
        format!("{}, milk", self.coffee.description())
    }
}

// ===========================================================================
// 三、架构模式（Architecture Patterns）
// ===========================================================================

// ---------------------------------------------------------------------------
// 12. Hexagonal / Clean Architecture：端口与适配器边界
// ---------------------------------------------------------------------------

pub trait ForInventory {
    fn stock(&self, sku: &str) -> u32;
}

pub trait Notify {
    fn notify(&self, message: &str);
}

/// 应用核心：只依赖端口（trait），不依赖具体适配器。
pub struct OrderService<'a> {
    inventory: &'a dyn ForInventory,
    notifier: &'a dyn Notify,
}

impl<'a> OrderService<'a> {
    pub fn new(inventory: &'a dyn ForInventory, notifier: &'a dyn Notify) -> Self {
        Self {
            inventory,
            notifier,
        }
    }

    pub fn place_order(&self, sku: &str, qty: u32) -> Result<String, String> {
        let stock = self.inventory.stock(sku);
        if stock >= qty {
            Ok(format!("Ordered {} of {}", qty, sku))
        } else {
            self.notifier.notify(&format!("Out of stock for {}", sku));
            Err(format!("Insufficient stock for {}", sku))
        }
    }
}

// ---------------------------------------------------------------------------
// 13. CQRS / Event Sourcing：命令与事件分离
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InventoryCommand {
    AddStock(String, u32),
    RemoveStock(String, u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InventoryEvent {
    StockAdded(String, u32),
    StockRemoved(String, u32),
}

pub struct InventoryAggregate;

impl InventoryAggregate {
    pub fn handle(command: InventoryCommand) -> Vec<InventoryEvent> {
        match command {
            InventoryCommand::AddStock(sku, qty) => vec![InventoryEvent::StockAdded(sku, qty)],
            InventoryCommand::RemoveStock(sku, qty) => vec![InventoryEvent::StockRemoved(sku, qty)],
        }
    }

    pub fn project(events: &[InventoryEvent]) -> HashMap<String, u32> {
        let mut state = HashMap::new();
        for event in events {
            match event {
                InventoryEvent::StockAdded(sku, qty) => {
                    *state.entry(sku.clone()).or_insert(0) += qty;
                }
                InventoryEvent::StockRemoved(sku, qty) => {
                    state.entry(sku.clone()).and_modify(|v| *v -= qty);
                }
            }
        }
        state
    }
}

// ---------------------------------------------------------------------------
// 14. Microservices：服务边界抽象
// ---------------------------------------------------------------------------

pub trait Service {
    type Request;
    type Response;
    fn handle(&self, req: Self::Request) -> Self::Response;
}

#[derive(Debug)]
pub struct UserRequest {
    pub user_id: u64,
}

#[derive(Debug)]
pub struct UserProfile {
    pub user_id: u64,
    pub name: String,
}

pub struct UserService;

impl Service for UserService {
    type Request = UserRequest;
    type Response = UserProfile;

    fn handle(&self, req: Self::Request) -> Self::Response {
        UserProfile {
            user_id: req.user_id,
            name: format!("User {}", req.user_id),
        }
    }
}

// ---------------------------------------------------------------------------
// 15. Actor 模式（基于 std::sync::mpsc 的简化实现）
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CounterMessage {
    Increment(u64),
    Get,
}

pub struct CounterActor;

impl CounterActor {
    pub fn spawn() -> Sender<CounterMessage> {
        let (tx, rx) = channel::<CounterMessage>();
        std::thread::spawn(move || {
            let mut count = 0u64;
            for msg in rx {
                match msg {
                    CounterMessage::Increment(n) => count += n,
                    CounterMessage::Get => println!("current count: {}", count),
                }
            }
        });
        tx
    }
}

// ---------------------------------------------------------------------------
// 16. Plugin System 插件系统（静态注册表）
// ---------------------------------------------------------------------------

pub trait Plugin: Send + Sync {
    fn name(&self) -> &'static str;
    fn execute(&self, input: &str) -> String;
}

pub struct PluginRegistry {
    plugins: Vec<Box<dyn Plugin>>,
}

impl PluginRegistry {
    pub fn new() -> Self {
        Self { plugins: Vec::new() }
    }

    pub fn register(&mut self, plugin: Box<dyn Plugin>) {
        self.plugins.push(plugin);
    }

    pub fn run_all(&self, input: &str) -> Vec<String> {
        self.plugins
            .iter()
            .map(|p| format!("[{}] {}", p.name(), p.execute(input)))
            .collect()
    }
}

pub struct UpperPlugin;
impl Plugin for UpperPlugin {
    fn name(&self) -> &'static str {
        "upper"
    }
    fn execute(&self, input: &str) -> String {
        input.to_uppercase()
    }
}

// ---------------------------------------------------------------------------
// 17. Event Bus 事件总线（发布-订阅）
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AppEvent {
    UserLoggedIn(u64),
    OrderPlaced(String),
}

pub struct EventBus {
    subscribers: HashMap<AppEvent, Vec<Sender<AppEvent>>>,
}

impl EventBus {
    pub fn new() -> Self {
        Self {
            subscribers: HashMap::new(),
        }
    }

    pub fn subscribe(&mut self, event: AppEvent, sender: Sender<AppEvent>) {
        self.subscribers.entry(event).or_default().push(sender);
    }

    pub fn publish(&self, event: AppEvent) {
        if let Some(subs) = self.subscribers.get(&event) {
            for sender in subs {
                // 忽略已关闭的接收者。
                let _ = sender.send(event.clone());
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn into_from_asref() {
        assert_eq!(greet("Alice"), "Hello, alice!");
        assert_eq!(greet(String::from("Bob")), "Hello, bob!");
    }

    #[test]
    fn newtype_units() {
        let miles = Miles::new(100);
        let km = miles.to_kilometers();
        assert_eq!(km.value(), 161);
    }

    #[test]
    fn typestate_workflow() {
        let workflow = Workflow::new("etl").configure().start();
        assert_eq!(workflow.status(), "etl is running");
    }

    #[test]
    fn builder_pattern() {
        let req = HttpRequestBuilder::new()
            .method("GET")
            .url("https://example.com")
            .header("Accept", "application/json")
            .build()
            .unwrap();
        assert_eq!(req.method, "GET");
        assert!(req.headers.contains_key("Accept"));
    }

    #[test]
    fn defer_guard() {
        use std::cell::Cell;
        let flag = Cell::new(false);
        {
            let f = &flag;
            let _guard = ScopeGuard::new(move || f.set(true));
            assert!(!f.get());
        }
        assert!(flag.get());
    }

    #[test]
    fn strategy_pattern() {
        let paypal = PayPal;
        let checkout = Checkout::new(&paypal);
        assert_eq!(checkout.execute(100), "Paid 100 via PayPal");
    }

    #[test]
    fn command_pattern() {
        let mut remote = RemoteControl::new();
        let cmd = Box::new(TurnOnCommand::new(Light));
        assert_eq!(remote.press(cmd), "Light is on");
        assert_eq!(remote.undo_last(), Some("Light is off".to_string()));
    }

    #[test]
    fn visitor_pattern() {
        let shapes: Vec<Box<dyn Shape>> = vec![
            Box::new(Circle { radius: 1.0 }),
            Box::new(Rectangle {
                width: 2.0,
                height: 3.0,
            }),
        ];
        let mut visitor = AreaVisitor { total: 0.0 };
        for shape in &shapes {
            shape.accept(&mut visitor);
        }
        assert!((visitor.total - (std::f64::consts::PI + 6.0)).abs() < 1e-9);
    }

    #[test]
    fn state_machine_pattern() {
        let state = TurnstileState::Locked;
        let (state, msg) = state.transition(TurnstileEvent::Coin);
        assert_eq!(state, TurnstileState::Unlocked);
        assert_eq!(msg, "Unlocking turnstile");
    }

    #[test]
    fn adapter_pattern() {
        let player = MediaAdapter::new();
        assert_eq!(player.play("video.mp4"), "Playing mp4: video.mp4");
    }

    #[test]
    fn decorator_pattern() {
        let coffee = MilkDecorator::new(SimpleCoffee);
        assert_eq!(coffee.cost(), 12);
        assert_eq!(coffee.description(), "Simple coffee, milk");
    }

    #[test]
    fn hexagonal_ports() {
        struct FakeInventory;
        impl ForInventory for FakeInventory {
            fn stock(&self, _sku: &str) -> u32 {
                10
            }
        }
        struct FakeNotify;
        impl Notify for FakeNotify {
            fn notify(&self, _message: &str) {}
        }
        let service = OrderService::new(&FakeInventory, &FakeNotify);
        assert!(service.place_order("SKU-1", 5).is_ok());
    }

    #[test]
    fn cqrs_event_sourcing() {
        let events = InventoryAggregate::handle(InventoryCommand::AddStock("A".to_string(), 5));
        let state = InventoryAggregate::project(&events);
        assert_eq!(state.get("A"), Some(&5));
    }

    #[test]
    fn microservice_trait() {
        let svc = UserService;
        let profile = svc.handle(UserRequest { user_id: 42 });
        assert_eq!(profile.user_id, 42);
    }

    #[test]
    fn plugin_system() {
        let mut registry = PluginRegistry::new();
        registry.register(Box::new(UpperPlugin));
        let results = registry.run_all("hello");
        assert_eq!(results, vec!["[upper] HELLO"]);
    }

    #[test]
    fn event_bus() {
        let mut bus = EventBus::new();
        let (tx, rx) = channel();
        bus.subscribe(AppEvent::OrderPlaced("X".to_string()), tx);
        bus.publish(AppEvent::OrderPlaced("X".to_string()));
        assert_eq!(rx.recv().unwrap(), AppEvent::OrderPlaced("X".to_string()));
    }
}
