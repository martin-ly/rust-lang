//! 设计模式实现
//! 
//! 本模块实现了各种设计模式在Rust中的具体应用，
//! 包括创建型、结构型、行为型模式以及并发和函数式模式。

use std::sync::Once;
use std::sync::atomic::{AtomicPtr, Ordering};

/// 单例模式实现
pub mod singleton {
    use super::*;

    /// 线程安全的单例模式实现
    pub struct Singleton {
        data: String,
    }

    static INIT: Once = Once::new();
    static mut INSTANCE: *mut Singleton = 0 as *mut _;

    impl Singleton {
        pub fn get_instance() -> &'static Singleton {
            unsafe {
                INIT.call_once(|| {
                    let instance = Box::new(Singleton {
                        data: "Singleton instance".to_string(),
                    });
                    INSTANCE = Box::into_raw(instance);
                });
                &*INSTANCE
            }
        }

        pub fn get_data(&self) -> &str {
            &self.data
        }
    }

    impl AtomicSingleton {
        pub fn get_data(&self) -> &str {
            &self.data
        }
    }

    /// 使用AtomicPtr的线程安全单例
    pub struct AtomicSingleton {
        data: String,
    }

    static ATOMIC_INSTANCE: AtomicPtr<AtomicSingleton> = AtomicPtr::new(std::ptr::null_mut());

    impl AtomicSingleton {
        pub fn get_instance() -> &'static AtomicSingleton {
            let instance = ATOMIC_INSTANCE.load(Ordering::Acquire);
            if instance.is_null() {
                let new_instance = Box::new(AtomicSingleton {
                    data: "Atomic Singleton".to_string(),
                });
                let new_ptr = Box::into_raw(new_instance);
                
                match ATOMIC_INSTANCE.compare_exchange(
                    std::ptr::null_mut(),
                    new_ptr,
                    Ordering::Release,
                    Ordering::Acquire,
                ) {
                    Ok(_) => unsafe { &*new_ptr },
                    Err(_) => {
                        // 其他线程已经创建了实例
                        unsafe {
                            let _ = Box::from_raw(new_ptr);
                            &*ATOMIC_INSTANCE.load(Ordering::Acquire)
                        }
                    }
                }
            } else {
                unsafe { &*instance }
            }
        }
    }
}

/// 建造者模式实现
pub mod builder {

    /// 复杂对象的建造者模式
    #[derive(Debug, Clone)]
    pub struct DatabaseConfig {
        pub host: String,
        pub port: u16,
        pub username: String,
        pub password: String,
        pub database: String,
        pub max_connections: u32,
        pub timeout: u64,
        pub ssl_enabled: bool,
    }

    impl DatabaseConfig {
        pub fn new() -> DatabaseConfigBuilder {
            DatabaseConfigBuilder::new()
        }
    }

    /// 建造者
    pub struct DatabaseConfigBuilder {
        host: Option<String>,
        port: Option<u16>,
        username: Option<String>,
        password: Option<String>,
        database: Option<String>,
        max_connections: Option<u32>,
        timeout: Option<u64>,
        ssl_enabled: Option<bool>,
    }

    impl DatabaseConfigBuilder {
        pub fn new() -> Self {
            Self {
                host: None,
                port: None,
                username: None,
                password: None,
                database: None,
                max_connections: None,
                timeout: None,
                ssl_enabled: None,
            }
        }

        pub fn host(mut self, host: impl Into<String>) -> Self {
            self.host = Some(host.into());
            self
        }

        pub fn port(mut self, port: u16) -> Self {
            self.port = Some(port);
            self
        }

        pub fn username(mut self, username: impl Into<String>) -> Self {
            self.username = Some(username.into());
            self
        }

        pub fn password(mut self, password: impl Into<String>) -> Self {
            self.password = Some(password.into());
            self
        }

        pub fn database(mut self, database: impl Into<String>) -> Self {
            self.database = Some(database.into());
            self
        }

        pub fn max_connections(mut self, max_connections: u32) -> Self {
            self.max_connections = Some(max_connections);
            self
        }

        pub fn timeout(mut self, timeout: u64) -> Self {
            self.timeout = Some(timeout);
            self
        }

        pub fn ssl_enabled(mut self, ssl_enabled: bool) -> Self {
            self.ssl_enabled = Some(ssl_enabled);
            self
        }

        pub fn build(self) -> Result<DatabaseConfig, String> {
            Ok(DatabaseConfig {
                host: self.host.ok_or("Host is required")?,
                port: self.port.ok_or("Port is required")?,
                username: self.username.ok_or("Username is required")?,
                password: self.password.ok_or("Password is required")?,
                database: self.database.ok_or("Database is required")?,
                max_connections: self.max_connections.unwrap_or(10),
                timeout: self.timeout.unwrap_or(30),
                ssl_enabled: self.ssl_enabled.unwrap_or(false),
            })
        }
    }
}

/// 工厂模式实现
pub mod factory {

    /// 抽象产品
    pub trait Product {
        fn name(&self) -> &str;
        fn price(&self) -> f64;
    }

    /// 具体产品
    pub struct Book {
        name: String,
        price: f64,
    }

    impl Product for Book {
        fn name(&self) -> &str {
            &self.name
        }

        fn price(&self) -> f64 {
            self.price
        }
    }

    pub struct Electronics {
        name: String,
        price: f64,
    }

    impl Product for Electronics {
        fn name(&self) -> &str {
            &self.name
        }

        fn price(&self) -> f64 {
            self.price
        }
    }

    /// 产品类型
    #[derive(Debug, Clone)]
    pub enum ProductType {
        Book,
        Electronics,
    }

    /// 工厂trait
    pub trait ProductFactory {
        fn create_product(&self, product_type: ProductType, name: String, price: f64) -> Box<dyn Product>;
    }

    /// 具体工厂
    pub struct ConcreteProductFactory;

    impl ProductFactory for ConcreteProductFactory {
        fn create_product(&self, product_type: ProductType, name: String, price: f64) -> Box<dyn Product> {
            match product_type {
                ProductType::Book => Box::new(Book { name, price }),
                ProductType::Electronics => Box::new(Electronics { name, price }),
            }
        }
    }

    /// 使用函数式方法的工厂
    pub fn create_product(product_type: ProductType, name: String, price: f64) -> Box<dyn Product> {
        match product_type {
            ProductType::Book => Box::new(Book { name, price }),
            ProductType::Electronics => Box::new(Electronics { name, price }),
        }
    }
}

/// 观察者模式实现
pub mod observer {
    use std::cell::RefCell;
    use std::rc::{Rc, Weak};

    /// 观察者trait
    pub trait Observer {
        fn update(&self, data: &str);
    }

    /// 具体观察者
    pub struct ConcreteObserver {
        name: String,
    }

    impl ConcreteObserver {
        pub fn new(name: String) -> Self {
            Self { name }
        }
    }

    impl Observer for ConcreteObserver {
        fn update(&self, data: &str) {
            println!("Observer {} received: {}", self.name, data);
        }
    }

    /// 主题trait
    pub trait Subject {
        fn attach(&mut self, observer: Rc<RefCell<dyn Observer>>);
        fn detach(&mut self, observer: Weak<RefCell<dyn Observer>>);
        fn notify(&self, data: &str);
    }

    /// 具体主题
    pub struct ConcreteSubject {
        observers: Vec<Weak<RefCell<dyn Observer>>>,
        data: String,
    }

    impl ConcreteSubject {
        pub fn new() -> Self {
            Self {
                observers: Vec::new(),
                data: String::new(),
            }
        }

        pub fn set_data(&mut self, data: String) {
            self.data = data;
            self.notify(&self.data);
        }
    }

    impl Subject for ConcreteSubject {
        fn attach(&mut self, observer: Rc<RefCell<dyn Observer>>) {
            self.observers.push(Rc::downgrade(&observer));
        }

        fn detach(&mut self, observer: Weak<RefCell<dyn Observer>>) {
            self.observers.retain(|o| !Weak::ptr_eq(o, &observer));
        }

        fn notify(&self, data: &str) {
            for observer in &self.observers {
                if let Some(observer) = observer.upgrade() {
                    observer.borrow().update(data);
                }
            }
        }
    }
}

/// 策略模式实现
pub mod strategy {

    /// 策略trait
    pub trait Strategy {
        fn execute(&self, data: &str) -> String;
    }

    /// 具体策略A
    pub struct ConcreteStrategyA;

    impl Strategy for ConcreteStrategyA {
        fn execute(&self, data: &str) -> String {
            format!("StrategyA: {}", data.to_uppercase())
        }
    }

    /// 具体策略B
    pub struct ConcreteStrategyB;

    impl Strategy for ConcreteStrategyB {
        fn execute(&self, data: &str) -> String {
            format!("StrategyB: {}", data.to_lowercase())
        }
    }

    /// 上下文
    pub struct Context {
        strategy: Box<dyn Strategy>,
    }

    impl Context {
        pub fn new(strategy: Box<dyn Strategy>) -> Self {
            Self { strategy }
        }

        pub fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
            self.strategy = strategy;
        }

        pub fn execute_strategy(&self, data: &str) -> String {
            self.strategy.execute(data)
        }
    }
}

/// 生产者-消费者模式实现
pub mod producer_consumer {

    /// 消息类型
    #[derive(Debug, Clone)]
    pub struct Message {
        pub id: u32,
        pub data: String,
    }

    /// 生产者
    pub struct Producer {
        sender: std::sync::mpsc::Sender<Message>,
    }

    impl Producer {
        pub fn new(sender: std::sync::mpsc::Sender<Message>) -> Self {
            Self { sender }
        }

        pub fn produce(&self, id: u32, data: String) -> Result<(), std::sync::mpsc::SendError<Message>> {
            let message = Message { id, data };
            self.sender.send(message)?;
            Ok(())
        }
    }

    /// 消费者
    pub struct Consumer {
        receiver: std::sync::mpsc::Receiver<Message>,
    }

    impl Consumer {
        pub fn new(receiver: std::sync::mpsc::Receiver<Message>) -> Self {
            Self { receiver }
        }

        pub fn consume(&self) -> Result<Message, std::sync::mpsc::RecvError> {
            self.receiver.recv()
        }
    }

    /// 生产者-消费者系统
    pub struct ProducerConsumerSystem {
        sender: std::sync::mpsc::Sender<Message>,
    }

    impl ProducerConsumerSystem {
        pub fn new() -> Self {
            let (sender, _receiver) = std::sync::mpsc::channel();
            Self { sender }
        }

        pub fn run(&self) {
            let sender = self.sender.clone();

            // 生产者线程
            let producer_handle = std::thread::spawn(move || {
                for i in 0..10 {
                    let message = Message { 
                        id: i, 
                        data: format!("Message {}", i) 
                    };
                    sender.send(message).unwrap();
                    std::thread::sleep(std::time::Duration::from_millis(100));
                }
            });

            producer_handle.join().unwrap();
        }

        pub fn create_consumer(&self) -> Consumer {
            let (_sender, receiver) = std::sync::mpsc::channel();
            Consumer::new(receiver)
        }
    }

    impl Clone for Producer {
        fn clone(&self) -> Self {
            Self {
                sender: self.sender.clone(),
            }
        }
    }

    // Consumer cannot be cloned because mpsc::Receiver doesn't implement Clone
}

/// 函数式模式实现
pub mod functional {

    /// 高阶函数示例
    pub fn map<T, U, F>(items: Vec<T>, f: F) -> Vec<U>
    where
        F: Fn(T) -> U,
    {
        items.into_iter().map(f).collect()
    }

    pub fn filter<T, F>(items: Vec<T>, predicate: F) -> Vec<T>
    where
        F: Fn(&T) -> bool,
    {
        items.into_iter().filter(predicate).collect()
    }

    pub fn reduce<T, F>(items: Vec<T>, initial: T, f: F) -> T
    where
        F: Fn(T, T) -> T,
    {
        items.into_iter().fold(initial, f)
    }

    /// 函数组合
    pub fn compose<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> C
    where
        F: Fn(B) -> C,
        G: Fn(A) -> B,
    {
        move |x| f(g(x))
    }

    /// 柯里化
    pub fn curry<A, B, C, F>(f: F) -> impl Fn(A) -> Box<dyn Fn(B) -> C>
    where
        F: Fn(A, B) -> C + Clone + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        C: 'static,
    {
        move |a| {
            let f = f.clone();
            Box::new(move |b| f(a.clone(), b))
        }
    }

    /// Maybe单子
    #[derive(Debug, Clone, PartialEq)]
    pub enum Maybe<T> {
        Just(T),
        Nothing,
    }

    impl<T> Maybe<T> {
        pub fn new(value: T) -> Self {
            Maybe::Just(value)
        }

        pub fn nothing() -> Self {
            Maybe::Nothing
        }

        /// Functor的map操作
        pub fn map<U, F>(self, f: F) -> Maybe<U>
        where
            F: FnOnce(T) -> U,
        {
            match self {
                Maybe::Just(value) => Maybe::Just(f(value)),
                Maybe::Nothing => Maybe::Nothing,
            }
        }

        /// Monad的bind操作
        pub fn bind<U, F>(self, f: F) -> Maybe<U>
        where
            F: FnOnce(T) -> Maybe<U>,
        {
            match self {
                Maybe::Just(value) => f(value),
                Maybe::Nothing => Maybe::Nothing,
            }
        }

        /// 提取值或返回默认值
        pub fn unwrap_or(self, default: T) -> T {
            match self {
                Maybe::Just(value) => value,
                Maybe::Nothing => default,
            }
        }
    }
}

/// 错误处理模式
pub mod error_handling {
    use thiserror::Error;

    /// 自定义错误类型
    #[derive(Error, Debug)]
    pub enum AppError {
        #[error("IO error: {0}")]
        Io(#[from] std::io::Error),
        
        #[error("Parse error: {0}")]
        Parse(#[from] std::num::ParseIntError),
        
        #[error("Custom error: {message}")]
        Custom { message: String },
        
        #[error("Validation error: {field}")]
        Validation { field: String },
    }

    /// 结果类型别名
    pub type AppResult<T> = Result<T, AppError>;

    /// 错误处理示例
    pub struct ErrorHandler;

    impl ErrorHandler {
        pub fn handle_error(error: AppError) -> String {
            match error {
                AppError::Io(e) => format!("IO错误: {}", e),
                AppError::Parse(e) => format!("解析错误: {}", e),
                AppError::Custom { message } => format!("自定义错误: {}", message),
                AppError::Validation { field } => format!("验证错误: {}", field),
            }
        }

        pub fn process_data(data: &str) -> AppResult<i32> {
            if data.is_empty() {
                return Err(AppError::Validation {
                    field: "data".to_string(),
                });
            }

            data.parse::<i32>()
                .map_err(|e| AppError::Parse(e))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_singleton() {
        let instance1 = singleton::Singleton::get_instance();
        let instance2 = singleton::Singleton::get_instance();
        
        assert_eq!(instance1.get_data(), instance2.get_data());
    }

    #[test]
    fn test_database_config_builder() {
        let config = builder::DatabaseConfig::new()
            .host("localhost")
            .port(5432)
            .username("admin")
            .password("secret")
            .database("mydb")
            .max_connections(20)
            .timeout(60)
            .ssl_enabled(true)
            .build()
            .unwrap();

        assert_eq!(config.host, "localhost");
        assert_eq!(config.port, 5432);
        assert_eq!(config.max_connections, 20);
        assert!(config.ssl_enabled);
    }

    #[test]
    fn test_factory_pattern() {
        use factory::{ProductFactory, ProductType};
        let factory = factory::ConcreteProductFactory;
        let product = factory.create_product(
            ProductType::Book,
            "Rust Book".to_string(),
            29.99,
        );

        assert_eq!(product.name(), "Rust Book");
        assert_eq!(product.price(), 29.99);
    }

    #[test]
    fn test_strategy_pattern() {
        let strategy_a = strategy::ConcreteStrategyA;
        let strategy_b = strategy::ConcreteStrategyB;
        
        let context_a = strategy::Context::new(Box::new(strategy_a));
        let context_b = strategy::Context::new(Box::new(strategy_b));
        
        assert_eq!(context_a.execute_strategy("hello"), "StrategyA: HELLO");
        assert_eq!(context_b.execute_strategy("WORLD"), "StrategyB: world");
    }

    #[test]
    fn test_higher_order_functions() {
        let numbers = vec![1, 2, 3, 4, 5];
        
        // Map
        let doubled = functional::map(numbers.clone(), |x| x * 2);
        assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
        
        // Filter
        let evens = functional::filter(numbers.clone(), |&x| x % 2 == 0);
        assert_eq!(evens, vec![2, 4]);
        
        // Reduce
        let sum = functional::reduce(numbers, 0, |acc, x| acc + x);
        assert_eq!(sum, 15);
    }

    #[test]
    fn test_function_composition() {
        let add_one = |x: i32| x + 1;
        let multiply_by_two = |x: i32| x * 2;
        
        let composed = functional::compose(multiply_by_two, add_one);
        assert_eq!(composed(5), 12); // (5 + 1) * 2 = 12
    }

    #[test]
    fn test_maybe_monad() {
        let maybe_value = functional::Maybe::new(5);
        let doubled = maybe_value.map(|x| x * 2);
        
        assert_eq!(doubled, functional::Maybe::Just(10));
        
        let nothing = functional::Maybe::<i32>::nothing();
        let result = nothing.map(|x| x * 2);
        
        assert_eq!(result, functional::Maybe::Nothing);
    }

    #[test]
    fn test_error_handling() {
        let result = error_handling::ErrorHandler::process_data("123");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 123);
        
        let error_result = error_handling::ErrorHandler::process_data("");
        assert!(error_result.is_err());
    }
}
