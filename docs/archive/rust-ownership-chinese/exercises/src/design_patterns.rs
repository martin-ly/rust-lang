//! Rust设计模式与所有权
//!
//! 常见设计模式的所有权实现

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

// ============================================
// 1. 访问者模式 (Visitor)
// ============================================

pub trait Visitor {
    fn visit_element_a(&mut self, elem: &ElementA);
    fn visit_element_b(&mut self, elem: &ElementB);
}

pub trait Element {
    fn accept(&self, visitor: &mut dyn Visitor);
}

pub struct ElementA {
    pub value: i32,
}

pub struct ElementB {
    pub name: String,
}

impl Element for ElementA {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_element_a(self);
    }
}

impl Element for ElementB {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_element_b(self);
    }
}

pub struct PrintVisitor;

impl Visitor for PrintVisitor {
    fn visit_element_a(&mut self, elem: &ElementA) {
        println!("ElementA: {}", elem.value);
    }
    fn visit_element_b(&mut self, elem: &ElementB) {
        println!("ElementB: {}", elem.name);
    }
}

// ============================================
// 2. 观察者模式 (Observer)
// ============================================

pub trait Observer {
    fn update(&self, message: &str);
}

pub struct Subject {
    observers: RefCell<Vec<Rc<dyn Observer>>>,
}

impl Subject {
    pub fn new() -> Self {
        Self {
            observers: RefCell::new(Vec::new()),
        }
    }
    
    pub fn attach(&self, observer: Rc<dyn Observer>) {
        self.observers.borrow_mut().push(observer);
    }
    
    pub fn notify(&self, message: &str) {
        for observer in self.observers.borrow().iter() {
            observer.update(message);
        }
    }
}

// ============================================
// 3. 策略模式 (Strategy)
// ============================================

pub trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}

pub struct QuickSort;
pub struct MergeSort;

impl SortStrategy for QuickSort {
    fn sort(&self, data: &mut [i32]) {
        data.sort_unstable();
    }
}

impl SortStrategy for MergeSort {
    fn sort(&self, data: &mut [i32]) {
        data.sort();
    }
}

pub struct Sorter<'a> {
    strategy: &'a dyn SortStrategy,
}

impl<'a> Sorter<'a> {
    pub fn new(strategy: &'a dyn SortStrategy) -> Self {
        Self { strategy }
    }
    
    pub fn sort(&self, data: &mut [i32]) {
        self.strategy.sort(data);
    }
}

// ============================================
// 4. 装饰器模式 (Decorator)
// ============================================

pub trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

pub struct SimpleCoffee;

impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 {
        2.0
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
    fn cost(&self) -> f64 {
        self.coffee.cost() + 0.5
    }
    fn description(&self) -> String {
        format!("{}, milk", self.coffee.description())
    }
}

// ============================================
// 5. 建造者模式 (Builder)
// ============================================

pub struct Computer {
    cpu: String,
    ram: u32,
    storage: u32,
}

pub struct ComputerBuilder {
    cpu: Option<String>,
    ram: Option<u32>,
    storage: Option<u32>,
}

impl ComputerBuilder {
    pub fn new() -> Self {
        Self {
            cpu: None,
            ram: None,
            storage: None,
        }
    }
    
    pub fn cpu(mut self, cpu: impl Into<String>) -> Self {
        self.cpu = Some(cpu.into());
        self
    }
    
    pub fn ram(mut self, ram: u32) -> Self {
        self.ram = Some(ram);
        self
    }
    
    pub fn storage(mut self, storage: u32) -> Self {
        self.storage = Some(storage);
        self
    }
    
    pub fn build(self) -> Computer {
        Computer {
            cpu: self.cpu.unwrap_or_else(|| "Intel".to_string()),
            ram: self.ram.unwrap_or(8),
            storage: self.storage.unwrap_or(256),
        }
    }
}

// ============================================
// 6. 原型模式 (Prototype)
// ============================================

pub trait Prototype {
    fn duplicate(&self) -> Box<dyn Prototype>;
}

pub struct Document {
    pub content: String,
}

impl Document {
    pub fn new(content: &str) -> Self {
        Self {
            content: content.to_string(),
        }
    }
}

impl Clone for Document {
    fn clone(&self) -> Self {
        Self {
            content: self.content.clone(),
        }
    }
}

impl Prototype for Document {
    fn duplicate(&self) -> Box<dyn Prototype> {
        Box::new(self.clone())
    }
}

// ============================================
// 7. 代理模式 (Proxy)
// ============================================

pub trait Image {
    fn display(&self);
}

pub struct RealImage {
    filename: String,
}

impl RealImage {
    fn new(filename: &str) -> Self {
        println!("Loading image: {}", filename);
        Self {
            filename: filename.to_string(),
        }
    }
}

impl Image for RealImage {
    fn display(&self) {
        println!("Displaying: {}", self.filename);
    }
}

pub struct ProxyImage {
    filename: String,
    real_image: RefCell<Option<RealImage>>,
}

impl ProxyImage {
    pub fn new(filename: &str) -> Self {
        Self {
            filename: filename.to_string(),
            real_image: RefCell::new(None),
        }
    }
}

impl Image for ProxyImage {
    fn display(&self) {
        let mut image = self.real_image.borrow_mut();
        if image.is_none() {
            *image = Some(RealImage::new(&self.filename));
        }
        image.as_ref().unwrap().display();
    }
}

// ============================================
// 8. 命令模式 (Command)
// ============================================

pub trait Command {
    fn execute(&self);
    fn undo(&self);
}

pub struct Light {
    pub is_on: RefCell<bool>,
}

impl Light {
    pub fn new() -> Self {
        Self {
            is_on: RefCell::new(false),
        }
    }
    
    pub fn turn_on(&self) {
        *self.is_on.borrow_mut() = true;
        println!("Light is on");
    }
    
    pub fn turn_off(&self) {
        *self.is_on.borrow_mut() = false;
        println!("Light is off");
    }
}

pub struct TurnOnCommand {
    light: Rc<Light>,
}

impl TurnOnCommand {
    pub fn new(light: Rc<Light>) -> Self {
        Self { light }
    }
}

impl Command for TurnOnCommand {
    fn execute(&self) {
        self.light.turn_on();
    }
    fn undo(&self) {
        self.light.turn_off();
    }
}

// ============================================
// 9. 迭代器模式 (Iterator)
// ============================================

pub struct TreeNode<T> {
    value: T,
    children: Vec<TreeNode<T>>,
}

impl<T> TreeNode<T> {
    pub fn new(value: T) -> Self {
        Self {
            value,
            children: Vec::new(),
        }
    }
    
    pub fn add_child(&mut self, child: TreeNode<T>) {
        self.children.push(child);
    }
    
    pub fn iter_dfs(&self) -> DfsIterator<T> {
        let stack = vec![self];
        DfsIterator { stack }
    }
}

pub struct DfsIterator<'a, T> {
    stack: Vec<&'a TreeNode<T>>,
}

impl<'a, T> Iterator for DfsIterator<'a, T> {
    type Item = &'a T;
    
    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        // 将子节点压入栈（逆序以保持顺序）
        for child in node.children.iter().rev() {
            self.stack.push(child);
        }
        Some(&node.value)
    }
}

// ============================================
// 10. 状态模式 (State) - 类型状态版本
// ============================================

pub struct Draft;
pub struct PendingReview;
pub struct Published;

pub struct Post<State> {
    content: String,
    state: std::marker::PhantomData<State>,
}

impl Post<Draft> {
    pub fn new() -> Self {
        Self {
            content: String::new(),
            state: std::marker::PhantomData,
        }
    }
    
    pub fn add_text(&mut self, text: &str) {
        self.content.push_str(text);
    }
    
    pub fn request_review(self) -> Post<PendingReview> {
        Post {
            content: self.content,
            state: std::marker::PhantomData,
        }
    }
}

impl Post<PendingReview> {
    pub fn approve(self) -> Post<Published> {
        Post {
            content: self.content,
            state: std::marker::PhantomData,
        }
    }
    
    pub fn reject(self) -> Post<Draft> {
        Post {
            content: self.content,
            state: std::marker::PhantomData,
        }
    }
}

impl Post<Published> {
    pub fn content(&self) -> &str {
        &self.content
    }
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_visitor() {
        let elements: Vec<Box<dyn Element>> = vec![
            Box::new(ElementA { value: 42 }),
            Box::new(ElementB { name: "test".to_string() }),
        ];
        
        let mut visitor = PrintVisitor;
        for elem in &elements {
            elem.accept(&mut visitor);
        }
    }
    
    #[test]
    fn test_strategy() {
        let mut data = vec![3, 1, 4, 1, 5];
        let sorter = Sorter::new(&QuickSort);
        sorter.sort(&mut data);
        assert_eq!(data, vec![1, 1, 3, 4, 5]);
    }
    
    #[test]
    fn test_decorator() {
        let coffee = MilkDecorator::new(SimpleCoffee);
        assert_eq!(coffee.cost(), 2.5);
        assert!(coffee.description().contains("milk"));
    }
    
    #[test]
    fn test_builder() {
        let computer = ComputerBuilder::new()
            .cpu("AMD")
            .ram(16)
            .build();
        assert_eq!(computer.ram, 16);
    }
    
    #[test]
    fn test_proxy() {
        let proxy = ProxyImage::new("photo.jpg");
        proxy.display(); // 第一次加载
        proxy.display(); // 使用缓存
    }
    
    #[test]
    fn test_tree_iterator() {
        let mut root = TreeNode::new(1);
        let mut child = TreeNode::new(2);
        child.add_child(TreeNode::new(3));
        root.add_child(child);
        
        let values: Vec<_> = root.iter_dfs().copied().collect();
        assert_eq!(values, vec![1, 2, 3]);
    }
    
    #[test]
    fn test_typestate_post() {
        let post = Post::new();
        let post = post.request_review();
        let post = post.approve();
        assert_eq!(post.content(), "");
    }
}
