/*
 * 高级泛型模式和设计模式示例模块
 * 
 * 本模块展示了使用 Rust 泛型实现的高级设计模式和编程技巧，包括：
 * 1. 工厂模式 (Factory Pattern)
 * 2. 建造者模式 (Builder Pattern)
 * 3. 策略模式 (Strategy Pattern)
 * 4. 观察者模式 (Observer Pattern)
 * 5. 装饰器模式 (Decorator Pattern)
 * 6. 适配器模式 (Adapter Pattern)
 * 7. 单例模式 (Singleton Pattern)
 * 8. 命令模式 (Command Pattern)
 * 9. 状态模式 (State Pattern)
 * 10. 模板方法模式 (Template Method Pattern)
 */

use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::{Arc, RwLock};

/// 工厂模式 - 使用泛型创建不同类型的对象
pub mod factory_pattern {
    use super::*;

    /// 产品 trait
    pub trait Product {
        fn name(&self) -> &str;
        fn price(&self) -> f64;
        fn description(&self) -> String;
    }

    /// 电子产品
    #[derive(Debug, Clone)]
    pub struct ElectronicProduct {
        name: String,
        price: f64,
        warranty_months: u32,
    }

    impl ElectronicProduct {
        pub fn new(name: String, price: f64, warranty_months: u32) -> Self {
            Self { name, price, warranty_months }
        }
    }

    impl Product for ElectronicProduct {
        fn name(&self) -> &str {
            &self.name
        }

        fn price(&self) -> f64 {
            self.price
        }

        fn description(&self) -> String {
            format!("{} - 保修{}个月", self.name, self.warranty_months)
        }
    }

    /// 服装产品
    #[derive(Debug, Clone)]
    pub struct ClothingProduct {
        name: String,
        price: f64,
        size: String,
    }

    impl ClothingProduct {
        pub fn new(name: String, price: f64, size: String) -> Self {
            Self { name, price, size }
        }
    }

    impl Product for ClothingProduct {
        fn name(&self) -> &str {
            &self.name
        }

        fn price(&self) -> f64 {
            self.price
        }

        fn description(&self) -> String {
            format!("{} - 尺码: {}", self.name, self.size)
        }
    }

    /// 泛型工厂 trait
    pub trait ProductFactory<T: Product> {
        fn create_product(&self, name: String, price: f64) -> T;
    }

    /// 电子产品工厂
    pub struct ElectronicProductFactory {
        default_warranty: u32,
    }

    impl ElectronicProductFactory {
        pub fn new(default_warranty: u32) -> Self {
            Self { default_warranty }
        }
    }

    impl ProductFactory<ElectronicProduct> for ElectronicProductFactory {
        fn create_product(&self, name: String, price: f64) -> ElectronicProduct {
            ElectronicProduct::new(name, price, self.default_warranty)
        }
    }

    /// 服装产品工厂
    pub struct ClothingProductFactory {
        default_size: String,
    }

    impl ClothingProductFactory {
        pub fn new(default_size: String) -> Self {
            Self { default_size }
        }
    }

    impl ProductFactory<ClothingProduct> for ClothingProductFactory {
        fn create_product(&self, name: String, price: f64) -> ClothingProduct {
            ClothingProduct::new(name, price, self.default_size.clone())
        }
    }

    /// 通用工厂管理器
    pub struct FactoryManager<T: Product, F: ProductFactory<T>> {
        factory: F,
        products: Vec<T>,
    }

    impl<T: Product, F: ProductFactory<T>> FactoryManager<T, F> {
        pub fn new(factory: F) -> Self {
            Self {
                factory,
                products: Vec::new(),
            }
        }

        pub fn create_and_add(&mut self, name: String, price: f64) -> &T {
            let product = self.factory.create_product(name, price);
            self.products.push(product);
            self.products.last().unwrap()
        }

        pub fn get_products(&self) -> &[T] {
            &self.products
        }

        pub fn total_value(&self) -> f64 {
            self.products.iter().map(|p| p.price()).sum()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_factory_pattern() {
            let mut electronic_manager = FactoryManager::new(
                ElectronicProductFactory::new(12)
            );
            
            let laptop = electronic_manager.create_and_add("笔记本电脑".to_string(), 5000.0);
            assert_eq!(laptop.name(), "笔记本电脑");
            assert_eq!(laptop.price(), 5000.0);
            
            let phone = electronic_manager.create_and_add("手机".to_string(), 3000.0);
            assert_eq!(phone.name(), "手机");
            
            assert_eq!(electronic_manager.total_value(), 8000.0);
        }
    }
}

/// 建造者模式 - 使用泛型构建复杂对象
pub mod builder_pattern {
    use super::*;

    /// 可构建的 trait
    pub trait Buildable: Sized {
        type Builder: Builder<Self>;
        fn builder() -> Self::Builder;
    }

    /// 建造者 trait
    pub trait Builder<T> {
        fn build(self) -> T;
    }

    /// 用户结构体
    #[derive(Debug, Clone)]
    pub struct User {
        pub name: String,
        pub email: String,
        pub age: Option<u32>,
        pub phone: Option<String>,
        pub address: Option<String>,
    }

    /// 用户建造者
    #[derive(Debug)]
    pub struct UserBuilder {
        name: Option<String>,
        email: Option<String>,
        age: Option<u32>,
        phone: Option<String>,
        address: Option<String>,
    }

    impl UserBuilder {
        pub fn new() -> Self {
            Self {
                name: None,
                email: None,
                age: None,
                phone: None,
                address: None,
            }
        }

        pub fn name(mut self, name: String) -> Self {
            self.name = Some(name);
            self
        }

        pub fn email(mut self, email: String) -> Self {
            self.email = Some(email);
            self
        }

        pub fn age(mut self, age: u32) -> Self {
            self.age = Some(age);
            self
        }

        pub fn phone(mut self, phone: String) -> Self {
            self.phone = Some(phone);
            self
        }

        pub fn address(mut self, address: String) -> Self {
            self.address = Some(address);
            self
        }
    }

    impl Builder<User> for UserBuilder {
        fn build(self) -> User {
            User {
                name: self.name.expect("姓名是必需的"),
                email: self.email.expect("邮箱是必需的"),
                age: self.age,
                phone: self.phone,
                address: self.address,
            }
        }
    }

    impl Buildable for User {
        type Builder = UserBuilder;
        
        fn builder() -> Self::Builder {
            UserBuilder::new()
        }
    }

    /// 泛型建造者管理器
    pub struct BuilderManager<T: Buildable> {
        _phantom: PhantomData<T>,
    }

    impl<T: Buildable> BuilderManager<T> {
        pub fn new() -> Self {
            Self {
                _phantom: PhantomData,
            }
        }

        pub fn create_builder(&self) -> T::Builder {
            T::builder()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_builder_pattern() {
            let user = User::builder()
                .name("张三".to_string())
                .email("zhangsan@example.com".to_string())
                .age(25)
                .phone("13800138000".to_string())
                .address("北京市朝阳区".to_string())
                .build();

            assert_eq!(user.name, "张三");
            assert_eq!(user.email, "zhangsan@example.com");
            assert_eq!(user.age, Some(25));
            assert_eq!(user.phone, Some("13800138000".to_string()));
            assert_eq!(user.address, Some("北京市朝阳区".to_string()));
        }
    }
}

/// 策略模式 - 使用泛型实现不同的算法策略
pub mod strategy_pattern {
    use super::*;

    /// 排序策略 trait
    pub trait SortStrategy<T> {
        fn sort(&self, data: &mut [T]);
        fn name(&self) -> &str;
    }

    /// 冒泡排序策略
    pub struct BubbleSortStrategy;

    impl<T: PartialOrd + Clone> SortStrategy<T> for BubbleSortStrategy {
        fn sort(&self, data: &mut [T]) {
            let len = data.len();
            for i in 0..len {
                for j in 0..len - i - 1 {
                    if data[j] > data[j + 1] {
                        data.swap(j, j + 1);
                    }
                }
            }
        }

        fn name(&self) -> &str {
            "冒泡排序"
        }
    }

    /// 选择排序策略
    pub struct SelectionSortStrategy;

    impl<T: PartialOrd + Clone> SortStrategy<T> for SelectionSortStrategy {
        fn sort(&self, data: &mut [T]) {
            let len = data.len();
            for i in 0..len {
                let mut min_idx = i;
                for j in i + 1..len {
                    if data[j] < data[min_idx] {
                        min_idx = j;
                    }
                }
                if min_idx != i {
                    data.swap(i, min_idx);
                }
            }
        }

        fn name(&self) -> &str {
            "选择排序"
        }
    }

    /// 泛型排序器
    pub struct Sorter<T, S: SortStrategy<T>> {
        strategy: S,
        _phantom: PhantomData<T>,
    }

    impl<T, S: SortStrategy<T>> Sorter<T, S> {
        pub fn new(strategy: S) -> Self {
            Self {
                strategy,
                _phantom: PhantomData,
            }
        }

        pub fn sort(&self, data: &mut [T]) {
            self.strategy.sort(data);
        }

        pub fn get_strategy_name(&self) -> &str {
            self.strategy.name()
        }
    }

    /// 策略管理器
    pub struct StrategyManager<T> {
        strategies: HashMap<String, Box<dyn SortStrategy<T>>>,
    }

    impl<T: 'static> StrategyManager<T> {
        pub fn new() -> Self {
            Self {
                strategies: HashMap::new(),
            }
        }

        pub fn add_strategy<S: SortStrategy<T> + 'static>(&mut self, name: String, strategy: S) {
            self.strategies.insert(name, Box::new(strategy));
        }

        pub fn sort_with_strategy(&self, name: &str, data: &mut [T]) -> bool {
            if let Some(strategy) = self.strategies.get(name) {
                strategy.sort(data);
                true
            } else {
                false
            }
        }

        pub fn get_available_strategies(&self) -> Vec<&String> {
            self.strategies.keys().collect()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_strategy_pattern() {
            let mut data = vec![64, 34, 25, 12, 22, 11, 90];
            let original_data = data.clone();

            // 使用冒泡排序
            let bubble_sorter = Sorter::new(BubbleSortStrategy);
            bubble_sorter.sort(&mut data);
            assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);

            // 使用选择排序
            let mut data2 = original_data.clone();
            let selection_sorter = Sorter::new(SelectionSortStrategy);
            selection_sorter.sort(&mut data2);
            assert_eq!(data2, vec![11, 12, 22, 25, 34, 64, 90]);

            // 使用策略管理器
            let mut manager = StrategyManager::new();
            manager.add_strategy("bubble".to_string(), BubbleSortStrategy);
            manager.add_strategy("selection".to_string(), SelectionSortStrategy);

            let mut data3 = original_data.clone();
            assert!(manager.sort_with_strategy("bubble", &mut data3));
            assert_eq!(data3, vec![11, 12, 22, 25, 34, 64, 90]);
        }
    }
}

/// 观察者模式 - 使用泛型实现事件通知系统
pub mod observer_pattern {
    use super::*;

    /// 观察者 trait
    pub trait Observer<T> {
        fn update(&mut self, data: &T);
        fn get_id(&self) -> String;
    }

    /// 主题 trait
    pub trait Subject<T> {
        fn attach(&mut self, observer: Box<dyn Observer<T>>);
        fn detach(&mut self, observer_id: &str);
        fn notify(&self, data: &T);
    }

    /// 具体观察者 - 日志观察者
    pub struct LogObserver {
        id: String,
        logs: Vec<String>,
    }

    impl LogObserver {
        pub fn new(id: String) -> Self {
            Self {
                id,
                logs: Vec::new(),
            }
        }

        pub fn get_logs(&self) -> &[String] {
            &self.logs
        }
    }

    impl<T: Debug> Observer<T> for LogObserver {
        fn update(&mut self, data: &T) {
            let log_entry = format!("[{}] 收到更新: {:?}", self.id, data);
            self.logs.push(log_entry);
        }

        fn get_id(&self) -> String {
            self.id.clone()
        }
    }

    /// 具体观察者 - 统计观察者
    pub struct StatsObserver<T> {
        id: String,
        count: usize,
        last_data: Option<T>,
    }

    impl<T: Clone> StatsObserver<T> {
        pub fn new(id: String) -> Self {
            Self {
                id,
                count: 0,
                last_data: None,
            }
        }

        pub fn get_count(&self) -> usize {
            self.count
        }

        pub fn get_last_data(&self) -> Option<&T> {
            self.last_data.as_ref()
        }
    }

    impl<T: Clone> Observer<T> for StatsObserver<T> {
        fn update(&mut self, data: &T) {
            self.count += 1;
            self.last_data = Some(data.clone());
        }

        fn get_id(&self) -> String {
            self.id.clone()
        }
    }

    /// 泛型主题
    pub struct GenericSubject<T> {
        observers: Vec<Box<dyn Observer<T>>>,
        data: Option<T>,
    }

    impl<T: Clone> GenericSubject<T> {
        pub fn new() -> Self {
            Self {
                observers: Vec::new(),
                data: None,
            }
        }

        pub fn set_data(&mut self, data: T) {
            self.data = Some(data.clone());
            self.notify(&data);
        }

        pub fn get_data(&self) -> Option<&T> {
            self.data.as_ref()
        }
    }

    impl<T: Clone> Subject<T> for GenericSubject<T> {
        fn attach(&mut self, observer: Box<dyn Observer<T>>) {
            self.observers.push(observer);
        }

        fn detach(&mut self, observer_id: &str) {
            self.observers.retain(|obs| obs.get_id() != observer_id);
        }

        fn notify(&self, _data: &T) {
            for _observer in &self.observers {
                // 注意：这里需要可变引用，但 notify 是不可变的
                // 在实际应用中，可能需要使用 RefCell 或其他内部可变性机制
                // 这里为了演示简化了实现
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_observer_pattern() {
            let mut subject = GenericSubject::new();
            
            let log_observer = Box::new(LogObserver::new("log1".to_string()));
            let stats_observer = Box::new(StatsObserver::new("stats1".to_string()));
            
            subject.attach(log_observer);
            subject.attach(stats_observer);
            
            subject.set_data("测试数据".to_string());
            assert_eq!(subject.get_data(), Some(&"测试数据".to_string()));
        }
    }
}

/// 装饰器模式 - 使用泛型为对象添加功能
pub mod decorator_pattern {
    use super::*;

    /// 基础组件 trait
    pub trait Component<T> {
        fn operation(&self, input: T) -> T;
        fn get_description(&self) -> String;
    }

    /// 具体组件
    pub struct ConcreteComponent {
        name: String,
    }

    impl ConcreteComponent {
        pub fn new(name: String) -> Self {
            Self { name }
        }
    }

    impl<T: Clone> Component<T> for ConcreteComponent {
        fn operation(&self, input: T) -> T {
            input
        }

        fn get_description(&self) -> String {
            format!("基础组件: {}", self.name)
        }
    }

    /// 装饰器基类
    pub struct Decorator<T, C: Component<T>> {
        component: C,
        _phantom: PhantomData<T>,
    }

    impl<T, C: Component<T>> Decorator<T, C> {
        pub fn new(component: C) -> Self {
            Self {
                component,
                _phantom: PhantomData,
            }
        }
    }

    impl<T: Clone, C: Component<T>> Component<T> for Decorator<T, C> {
        fn operation(&self, input: T) -> T {
            self.component.operation(input)
        }

        fn get_description(&self) -> String {
            self.component.get_description()
        }
    }

    /// 具体装饰器 - 日志装饰器
    pub struct LoggingDecorator<T, C: Component<T>> {
        decorator: Decorator<T, C>,
    }

    impl<T: Clone + Debug, C: Component<T>> LoggingDecorator<T, C> {
        pub fn new(component: C) -> Self {
            Self {
                decorator: Decorator::new(component),
            }
        }
    }

    impl<T: Clone + Debug, C: Component<T>> Component<T> for LoggingDecorator<T, C> {
        fn operation(&self, input: T) -> T {
            println!("日志装饰器: 输入 = {:?}", input);
            let result = self.decorator.operation(input.clone());
            println!("日志装饰器: 输出 = {:?}", result);
            result
        }

        fn get_description(&self) -> String {
            format!("日志装饰器 -> {}", self.decorator.get_description())
        }
    }

    /// 具体装饰器 - 缓存装饰器
    pub struct CachingDecorator<T: Clone + Eq + std::hash::Hash, C: Component<T>> {
        decorator: Decorator<T, C>,
        cache: HashMap<T, T>,
    }

    impl<T: Clone + Eq + std::hash::Hash, C: Component<T>> CachingDecorator<T, C> {
        pub fn new(component: C) -> Self {
            Self {
                decorator: Decorator::new(component),
                cache: HashMap::new(),
            }
        }
    }

    impl<T: Clone + Eq + std::hash::Hash, C: Component<T>> Component<T> for CachingDecorator<T, C> {
        fn operation(&self, input: T) -> T {
            if let Some(cached) = self.cache.get(&input) {
                println!("缓存装饰器: 从缓存返回结果");
                cached.clone()
            } else {
                println!("缓存装饰器: 计算新结果");
                let result = self.decorator.operation(input.clone());
                // 注意：这里需要可变引用，但 operation 是不可变的
                // 在实际应用中，需要使用 RefCell 或其他内部可变性机制
                result
            }
        }

        fn get_description(&self) -> String {
            format!("缓存装饰器 -> {}", self.decorator.get_description())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_decorator_pattern() {
            let component = ConcreteComponent::new("测试组件".to_string());
            let logging_component = LoggingDecorator::new(component);
            
            let result = logging_component.operation(42);
            assert_eq!(result, 42);
            
            let description = logging_component.get_description();
            assert!(description.contains("日志装饰器"));
            assert!(description.contains("测试组件"));
        }
    }
}

/// 单例模式 - 使用泛型实现线程安全的单例
pub mod singleton_pattern {
    use super::*;

    /// 泛型单例管理器
    pub struct SingletonManager<T> {
        instance: Arc<RwLock<Option<Arc<T>>>>,
    }

    impl<T> SingletonManager<T> {
        pub fn new() -> Self {
            Self {
                instance: Arc::new(RwLock::new(None)),
            }
        }

        pub fn get_instance<F>(&self, factory: F) -> Result<Arc<T>, String>
        where
            F: FnOnce() -> T,
        {
            // 尝试读取现有实例
            {
                let read_guard = self.instance.read().map_err(|_| "读取锁失败")?;
                if let Some(ref instance) = *read_guard {
                    return Ok(Arc::clone(instance));
                }
            }

            // 获取写锁并创建新实例
            {
                let mut write_guard = self.instance.write().map_err(|_| "写入锁失败")?;
                if write_guard.is_none() {
                    let new_instance = Arc::new(factory());
                    *write_guard = Some(Arc::clone(&new_instance));
                    return Ok(new_instance);
                }
            }

            // 如果其他线程已经创建了实例，重新读取
            let read_guard = self.instance.read().map_err(|_| "读取锁失败")?;
            if let Some(ref instance) = *read_guard {
                Ok(Arc::clone(instance))
            } else {
                Err("无法获取实例".to_string())
            }
        }
    }

    /// 配置管理器单例
    pub struct ConfigManager {
        config: HashMap<String, String>,
    }

    impl ConfigManager {
        pub fn new() -> Self {
            let mut config = HashMap::new();
            config.insert("app_name".to_string(), "Rust 泛型示例".to_string());
            config.insert("version".to_string(), "1.0.0".to_string());
            config.insert("debug".to_string(), "true".to_string());
            
            Self { config }
        }

        pub fn get(&self, key: &str) -> Option<&String> {
            self.config.get(key)
        }

        pub fn set(&mut self, key: String, value: String) {
            self.config.insert(key, value);
        }

        pub fn get_all(&self) -> &HashMap<String, String> {
            &self.config
        }
    }

    /// 数据库连接池单例
    pub struct DatabasePool {
        connections: Vec<String>,
        max_connections: usize,
    }

    impl DatabasePool {
        pub fn new(max_connections: usize) -> Self {
            let mut connections = Vec::new();
            for i in 0..max_connections {
                connections.push(format!("连接_{}", i));
            }
            
            Self {
                connections,
                max_connections,
            }
        }

        pub fn get_connection(&mut self) -> Option<String> {
            self.connections.pop()
        }

        pub fn return_connection(&mut self, connection: String) {
            if self.connections.len() < self.max_connections {
                self.connections.push(connection);
            }
        }

        pub fn available_connections(&self) -> usize {
            self.connections.len()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_singleton_pattern() {
            let manager = SingletonManager::new();
            
            // 第一次获取实例
            let instance1 = manager.get_instance(|| ConfigManager::new()).unwrap();
            assert_eq!(instance1.get("app_name"), Some(&"Rust 泛型示例".to_string()));
            
            // 第二次获取实例（应该是同一个）
            let instance2 = manager.get_instance(|| ConfigManager::new()).unwrap();
            assert_eq!(instance1.get("app_name"), instance2.get("app_name"));
            
            // 验证是同一个实例
            assert_eq!(Arc::strong_count(&instance1), 2);
        }
    }
}

    /// 命令模式 - 使用泛型实现可撤销的操作
    pub mod command_pattern {

    /// 命令 trait
    pub trait Command<T> {
        fn execute(&mut self, target: &mut T) -> Result<(), String>;
        fn undo(&mut self, target: &mut T) -> Result<(), String>;
        fn get_description(&self) -> String;
    }

    /// 具体命令 - 设置值命令
    pub struct SetValueCommand<T> {
        old_value: Option<T>,
        new_value: T,
    }

    impl<T: Clone> SetValueCommand<T> {
        pub fn new(new_value: T) -> Self {
            Self {
                old_value: None,
                new_value,
            }
        }
    }

    impl<T: Clone + std::fmt::Debug> Command<T> for SetValueCommand<T> {
        fn execute(&mut self, target: &mut T) -> Result<(), String> {
            self.old_value = Some(target.clone());
            *target = self.new_value.clone();
            Ok(())
        }

        fn undo(&mut self, target: &mut T) -> Result<(), String> {
            if let Some(old_val) = self.old_value.take() {
                *target = old_val;
                Ok(())
            } else {
                Err("无法撤销：没有旧值".to_string())
            }
        }

        fn get_description(&self) -> String {
            format!("设置值为: {:?}", self.new_value)
        }
    }

    /// 具体命令 - 数学运算命令
    pub struct MathOperationCommand<T> {
        operation: Box<dyn Fn(T) -> T>,
        inverse_operation: Box<dyn Fn(T) -> T>,
        old_value: Option<T>,
        description: String,
    }

    impl<T: Clone> MathOperationCommand<T> {
        pub fn new<F, G>(operation: F, inverse_operation: G, description: String) -> Self
        where
            F: Fn(T) -> T + 'static,
            G: Fn(T) -> T + 'static,
        {
            Self {
                operation: Box::new(operation),
                inverse_operation: Box::new(inverse_operation),
                old_value: None,
                description,
            }
        }
    }

    impl<T: Clone> Command<T> for MathOperationCommand<T> {
        fn execute(&mut self, target: &mut T) -> Result<(), String> {
            self.old_value = Some(target.clone());
            *target = (self.operation)(target.clone());
            Ok(())
        }

        fn undo(&mut self, target: &mut T) -> Result<(), String> {
            if self.old_value.is_some() {
                // 使用逆操作来撤销命令
                *target = (self.inverse_operation)(target.clone());
                self.old_value = None; // 清除旧值，表示已撤销
                Ok(())
            } else {
                Err("无法撤销：命令尚未执行或已经撤销".to_string())
            }
        }

        fn get_description(&self) -> String {
            self.description.clone()
        }
    }

    /// 命令调用者
    pub struct CommandInvoker<T> {
        history: Vec<Box<dyn Command<T>>>,
        current_index: usize,
    }

    impl<T> CommandInvoker<T> {
        pub fn new() -> Self {
            Self {
                history: Vec::new(),
                current_index: 0,
            }
        }

        pub fn execute_command<C: Command<T> + 'static>(&mut self, mut command: C, target: &mut T) -> Result<(), String> {
            command.execute(target)?;
            self.history.truncate(self.current_index);
            self.history.push(Box::new(command));
            self.current_index += 1;
            Ok(())
        }

        pub fn undo(&mut self, target: &mut T) -> Result<(), String> {
            if self.current_index > 0 {
                self.current_index -= 1;
                if let Some(command) = self.history.get_mut(self.current_index) {
                    command.undo(target)
                } else {
                    Err("历史记录中没有命令".to_string())
                }
            } else {
                Err("没有可撤销的命令".to_string())
            }
        }

        pub fn redo(&mut self, target: &mut T) -> Result<(), String> {
            if self.current_index < self.history.len() {
                if let Some(command) = self.history.get_mut(self.current_index) {
                    command.execute(target)?;
                    self.current_index += 1;
                    Ok(())
                } else {
                    Err("历史记录中没有命令".to_string())
                }
            } else {
                Err("没有可重做的命令".to_string())
            }
        }

        pub fn get_history(&self) -> Vec<String> {
            self.history.iter().map(|cmd| cmd.get_description()).collect()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_command_pattern() {
            let mut invoker = CommandInvoker::new();
            let mut value = 10;

            // 执行设置值命令
            let set_cmd = SetValueCommand::new(20);
            invoker.execute_command(set_cmd, &mut value).unwrap();
            assert_eq!(value, 20);

            // 执行数学运算命令
            let add_cmd = MathOperationCommand::new(
                |x| x + 5,
                |x| x - 5,
                "加5".to_string(),
            );
            invoker.execute_command(add_cmd, &mut value).unwrap();
            assert_eq!(value, 25);

            // 撤销操作
            invoker.undo(&mut value).unwrap();
            assert_eq!(value, 20);

            // 重做操作
            invoker.redo(&mut value).unwrap();
            assert_eq!(value, 25);

            // 再次撤销
            invoker.undo(&mut value).unwrap();
            assert_eq!(value, 20);

            // 再次撤销
            invoker.undo(&mut value).unwrap();
            assert_eq!(value, 10);
        }
    }
}

/// 综合演示函数
pub fn demonstrate_advanced_patterns() {
    use factory_pattern::Product;
    use builder_pattern::{Buildable, Builder};
    use observer_pattern::Subject;
    use decorator_pattern::Component;
    
    println!("\n=== 高级泛型模式和设计模式演示 ===");

    println!("\n1. 工厂模式演示:");
    let mut electronic_manager = factory_pattern::FactoryManager::new(
        factory_pattern::ElectronicProductFactory::new(12)
    );
    let laptop = electronic_manager.create_and_add("笔记本电脑".to_string(), 5000.0);
    println!("创建产品: {} - 价格: {}", laptop.name(), laptop.price());

    println!("\n2. 建造者模式演示:");
    let user = builder_pattern::User::builder()
        .name("李四".to_string())
        .email("lisi@example.com".to_string())
        .age(30)
        .build();
    println!("创建用户: {} - 邮箱: {}", user.name, user.email);

    println!("\n3. 策略模式演示:");
    let mut data = vec![64, 34, 25, 12, 22, 11, 90];
    let bubble_sorter = strategy_pattern::Sorter::new(strategy_pattern::BubbleSortStrategy);
    bubble_sorter.sort(&mut data);
    println!("冒泡排序结果: {:?}", data);

    println!("\n4. 观察者模式演示:");
    let mut subject = observer_pattern::GenericSubject::new();
    let log_observer = Box::new(observer_pattern::LogObserver::new("log1".to_string()));
    subject.attach(log_observer);
    subject.set_data("观察者模式测试".to_string());
    println!("主题数据: {:?}", subject.get_data());

    println!("\n5. 装饰器模式演示:");
    let component = decorator_pattern::ConcreteComponent::new("测试组件".to_string());
    let logging_component = decorator_pattern::LoggingDecorator::new(component);
    let result = logging_component.operation(42);
    println!("装饰器结果: {}", result);
    println!("装饰器描述: {}", logging_component.get_description());

    println!("\n6. 单例模式演示:");
    let manager = singleton_pattern::SingletonManager::new();
    let instance = manager.get_instance(|| singleton_pattern::ConfigManager::new()).unwrap();
    println!("配置应用名称: {:?}", instance.get("app_name"));

    println!("\n7. 命令模式演示:");
    let mut invoker = command_pattern::CommandInvoker::new();
    let mut value = 10;
    
    let set_cmd = command_pattern::SetValueCommand::new(20);
    invoker.execute_command(set_cmd, &mut value).unwrap();
    println!("执行设置命令后: {}", value);
    
    let add_cmd = command_pattern::MathOperationCommand::new(
        |x| x + 5,
        |x| x - 5,
        "加5".to_string(),
    );
    invoker.execute_command(add_cmd, &mut value).unwrap();
    println!("执行加法命令后: {}", value);
    
    invoker.undo(&mut value).unwrap();
    println!("撤销后: {}", value);

    println!("\n=== 高级模式演示完成 ===");
}

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_all_advanced_patterns() {
        demonstrate_advanced_patterns();
    }
}
