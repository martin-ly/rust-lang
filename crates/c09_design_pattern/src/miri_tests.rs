//! Miri 测试模块 - 设计模式内存安全验证

use std::cell::RefCell;
use std::rc::{Rc, Weak};
use std::sync::{Arc, Mutex};

// ==================== 单例模式 ====================

/// 测试 1: 线程不安全单例
#[test]
fn test_singleton() {
    use std::cell::UnsafeCell;
    
    struct Singleton<T> {
        data: UnsafeCell<Option<T>>,
    }
    
    impl<T> Singleton<T> {
        const fn new() -> Self {
            Self { data: UnsafeCell::new(None) }
        }
        
        fn get_or_init<F>(&self, f: F) -> &T
        where F: FnOnce() -> T {
            unsafe {
                if (*self.data.get()).is_none() {
                    *self.data.get() = Some(f());
                }
                (*self.data.get()).as_ref().unwrap()
            }
        }
    }
    
    unsafe impl<T: Send> Send for Singleton<T> {}
    unsafe impl<T: Sync> Sync for Singleton<T> {}
    
    static SINGLETON: Singleton<i32> = Singleton::new();
    let val = SINGLETON.get_or_init(|| 42);
    assert_eq!(*val, 42);
}

// ==================== 观察者模式 ====================

trait Observer {
    fn update(&self, state: i32);
}

struct Subject {
    observers: Vec<Weak<dyn Observer>>,
    state: i32,
}

impl Subject {
    fn new() -> Self {
        Self { observers: Vec::new(), state: 0 }
    }
    
    fn attach(&mut self, observer: Weak<dyn Observer>) {
        self.observers.push(observer);
    }
    
    fn notify(&self) {
        for observer in &self.observers {
            if let Some(obs) = observer.upgrade() {
                obs.update(self.state);
            }
        }
    }
}

/// 测试 2: 观察者模式内存安全
#[test]
fn test_observer_pattern() {
    struct ConcreteObserver;
    impl Observer for ConcreteObserver {
        fn update(&self, _state: i32) {}
    }
    
    let mut subject = Subject::new();
    let observer = Rc::new(ConcreteObserver);
    subject.attach(Rc::downgrade(&observer) as Weak<dyn Observer>);
    subject.notify();
}

// ==================== 代理模式 ====================

trait SubjectTrait {
    fn request(&self) -> i32;
}

struct RealSubject;
impl SubjectTrait for RealSubject {
    fn request(&self) -> i32 { 42 }
}

struct Proxy {
    real_subject: Option<Box<dyn SubjectTrait>>,
}

impl Proxy {
    fn new() -> Self {
        Self { real_subject: None }
    }
    
    fn ensure_initialized(&mut self) {
        if self.real_subject.is_none() {
            self.real_subject = Some(Box::new(RealSubject));
        }
    }
}

impl SubjectTrait for Proxy {
    fn request(&self) -> i32 {
        self.real_subject.as_ref().map(|s| s.request()).unwrap_or(0)
    }
}

/// 测试 3: 代理模式
#[test]
fn test_proxy_pattern() {
    let mut proxy = Proxy::new();
    proxy.ensure_initialized();
    assert_eq!(proxy.request(), 42);
}

// ==================== 工厂模式 ====================

trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String { "ProductA".to_string() }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String { "ProductB".to_string() }
}

enum ProductType { A, B }

struct Factory;

impl Factory {
    fn create(product_type: ProductType) -> Box<dyn Product> {
        match product_type {
            ProductType::A => Box::new(ConcreteProductA),
            ProductType::B => Box::new(ConcreteProductB),
        }
    }
}

/// 测试 4: 工厂模式
#[test]
fn test_factory_pattern() {
    let product_a = Factory::create(ProductType::A);
    let product_b = Factory::create(ProductType::B);
    
    assert_eq!(product_a.operation(), "ProductA");
    assert_eq!(product_b.operation(), "ProductB");
}

// ==================== 建造者模式 ====================

struct ProductBuilder {
    part_a: Option<String>,
    part_b: Option<i32>,
}

impl ProductBuilder {
    fn new() -> Self {
        Self { part_a: None, part_b: None }
    }
    
    fn part_a(mut self, value: String) -> Self {
        self.part_a = Some(value);
        self
    }
    
    fn part_b(mut self, value: i32) -> Self {
        self.part_b = Some(value);
        self
    }
    
    fn build(self) -> BuiltProduct {
        BuiltProduct {
            part_a: self.part_a.unwrap_or_default(),
            part_b: self.part_b.unwrap_or(0),
        }
    }
}

struct BuiltProduct {
    part_a: String,
    part_b: i32,
}

/// 测试 5: 建造者模式
#[test]
fn test_builder_pattern() {
    let product = ProductBuilder::new()
        .part_a("Test".to_string())
        .part_b(42)
        .build();
    
    assert_eq!(product.part_a, "Test");
    assert_eq!(product.part_b, 42);
}

// ==================== 适配器模式 ====================

trait Target {
    fn request(&self) -> String;
}

struct Adaptee;
impl Adaptee {
    fn specific_request(&self) -> String { "Adaptee".to_string() }
}

struct Adapter {
    adaptee: Adaptee,
}

impl Target for Adapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}

/// 测试 6: 适配器模式
#[test]
fn test_adapter_pattern() {
    let adapter = Adapter { adaptee: Adaptee };
    assert_eq!(adapter.request(), "Adaptee");
}

// ==================== 装饰器模式 ====================

trait Component {
    fn operation(&self) -> i32;
}

struct ConcreteComponent;
impl Component for ConcreteComponent {
    fn operation(&self) -> i32 { 10 }
}

struct Decorator {
    component: Box<dyn Component>,
}

impl Component for Decorator {
    fn operation(&self) -> i32 {
        self.component.operation() * 2
    }
}

/// 测试 7: 装饰器模式
#[test]
fn test_decorator_pattern() {
    let decorated = Decorator {
        component: Box::new(ConcreteComponent),
    };
    assert_eq!(decorated.operation(), 20);
}
