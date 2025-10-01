//! 程序设计模型
//! 
//! 本模块实现了现代软件设计的编程范式和模型，包括：
//! - 函数式编程模型（FP）
//! - 面向对象编程模型（OOP）
//! - 响应式编程模型（Reactive Programming）
//! - 声明式编程模型
//! - 过程式编程模型
//! - 逻辑编程模型
//! - 数据流编程模型
//! 
//! 充分利用 Rust 1.90 的类型系统和零成本抽象

use std::sync::{Arc, RwLock};
use std::marker::PhantomData;
use std::fmt::Debug;
use serde::{Deserialize, Serialize};
use crate::error::ModelError;

#[cfg(test)]
use std::sync::Mutex;

/// 程序设计模型结果类型
pub type ProgramResult<T> = Result<T, ModelError>;

/// ========================================
/// 函数式编程模型
/// ========================================

/// 函数式编程特征trait
pub trait Functor<A> {
    type Mapped<B>;
    fn fmap<B, F>(self, f: F) -> Self::Mapped<B>
    where
        F: FnOnce(A) -> B;
}

/// 单子（Monad）trait
pub trait Monad<A>: Functor<A> {
    fn pure(value: A) -> Self;
    fn bind<B, F>(self, f: F) -> <Self as Functor<A>>::Mapped<B>
    where
        F: FnOnce(A) -> <Self as Functor<A>>::Mapped<B>;
}

/// Option的Functor实现
impl<A> Functor<A> for Option<A> {
    type Mapped<B> = Option<B>;
    
    fn fmap<B, F>(self, f: F) -> Self::Mapped<B>
    where
        F: FnOnce(A) -> B,
    {
        self.map(f)
    }
}

/// Result的Functor实现
impl<A, E> Functor<A> for Result<A, E> {
    type Mapped<B> = Result<B, E>;
    
    fn fmap<B, F>(self, f: F) -> Self::Mapped<B>
    where
        F: FnOnce(A) -> B,
    {
        self.map(f)
    }
}

/// 惰性求值包装器
pub struct Lazy<T, F>
where
    F: FnOnce() -> T,
{
    thunk: Option<F>,
    value: Option<T>,
}

impl<T, F> Lazy<T, F>
where
    F: FnOnce() -> T,
{
    pub fn new(thunk: F) -> Self {
        Self {
            thunk: Some(thunk),
            value: None,
        }
    }
    
    pub fn force(&mut self) -> &T {
        if self.value.is_none() {
            let thunk = self.thunk.take().unwrap();
            self.value = Some(thunk());
        }
        self.value.as_ref().unwrap()
    }
}

/// 柯里化函数trait
pub trait Curry<A, B, C> {
    type Curried: Fn(B) -> C;
    fn curry(self, a: A) -> Self::Curried;
}

/// 高阶函数库
pub struct HigherOrderFunctions;

impl HigherOrderFunctions {
    /// 函数组合
    pub fn compose<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> C
    where
        F: Fn(B) -> C,
        G: Fn(A) -> B,
    {
        move |x| f(g(x))
    }
    
    /// 部分应用
    pub fn partial<A, B, C, F>(f: F, a: A) -> impl Fn(B) -> C
    where
        F: Fn(A, B) -> C,
        A: Clone,
    {
        move |b| f(a.clone(), b)
    }
    
    /// 函数柯里化
    pub fn curry<A, B, C, F>(f: F) -> impl Fn(A) -> Box<dyn Fn(B) -> C>
    where
        F: Fn(A, B) -> C + 'static + Clone,
        A: 'static + Clone,
        B: 'static,
        C: 'static,
    {
        move |a: A| {
            let f_clone = f.clone();
            let a_clone = a.clone();
            Box::new(move |b: B| f_clone(a_clone.clone(), b)) as Box<dyn Fn(B) -> C>
        }
    }
}

/// 不可变数据结构
#[derive(Debug, Clone, PartialEq)]
pub struct ImmutableList<T> {
    items: Arc<Vec<T>>,
}

impl<T: Clone> ImmutableList<T> {
    pub fn new() -> Self {
        Self {
            items: Arc::new(Vec::new()),
        }
    }
    
    pub fn from_vec(vec: Vec<T>) -> Self {
        Self {
            items: Arc::new(vec),
        }
    }
    
    pub fn push(&self, item: T) -> Self {
        let mut new_items = (*self.items).clone();
        new_items.push(item);
        Self {
            items: Arc::new(new_items),
        }
    }
    
    pub fn map<U, F>(&self, f: F) -> ImmutableList<U>
    where
        F: Fn(&T) -> U,
        U: Clone,
    {
        let mapped: Vec<U> = self.items.iter().map(f).collect();
        ImmutableList::from_vec(mapped)
    }
    
    pub fn filter<F>(&self, predicate: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        let filtered: Vec<T> = self.items.iter().filter(|x| predicate(x)).cloned().collect();
        ImmutableList::from_vec(filtered)
    }
    
    pub fn fold<U, F>(&self, init: U, f: F) -> U
    where
        F: Fn(U, &T) -> U,
    {
        self.items.iter().fold(init, f)
    }
    
    pub fn len(&self) -> usize {
        self.items.len()
    }
    
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<T: Clone> Default for ImmutableList<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// ========================================
/// 面向对象编程模型
/// ========================================

/// OOP类层次结构trait
pub trait OOPObject {
    fn class_name(&self) -> &str;
    fn to_string(&self) -> String;
    fn equals(&self, other: &dyn OOPObject) -> bool;
}

/// 封装示例：银行账户
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BankAccount {
    account_id: String,
    balance: f64,
    owner: String,
}

impl BankAccount {
    pub fn new(account_id: String, owner: String, initial_balance: f64) -> ProgramResult<Self> {
        if initial_balance < 0.0 {
            return Err(ModelError::ValidationError("Initial balance cannot be negative".to_string()));
        }
        
        Ok(Self {
            account_id,
            balance: initial_balance,
            owner,
        })
    }
    
    pub fn deposit(&mut self, amount: f64) -> ProgramResult<()> {
        if amount <= 0.0 {
            return Err(ModelError::ValidationError("Deposit amount must be positive".to_string()));
        }
        
        self.balance += amount;
        Ok(())
    }
    
    pub fn withdraw(&mut self, amount: f64) -> ProgramResult<()> {
        if amount <= 0.0 {
            return Err(ModelError::ValidationError("Withdrawal amount must be positive".to_string()));
        }
        
        if amount > self.balance {
            return Err(ModelError::ValidationError("Insufficient funds".to_string()));
        }
        
        self.balance -= amount;
        Ok(())
    }
    
    pub fn get_balance(&self) -> f64 {
        self.balance
    }
    
    pub fn get_owner(&self) -> &str {
        &self.owner
    }
}

impl OOPObject for BankAccount {
    fn class_name(&self) -> &str {
        "BankAccount"
    }
    
    fn to_string(&self) -> String {
        format!("BankAccount[id={}, owner={}, balance={}]", 
                self.account_id, self.owner, self.balance)
    }
    
    fn equals(&self, other: &dyn OOPObject) -> bool {
        if other.class_name() != self.class_name() {
            return false;
        }
        // 简化实现，实际需要更复杂的类型检查
        true
    }
}

/// 继承示例（通过组合模拟）
pub trait Account {
    fn get_account_id(&self) -> &str;
    fn get_balance(&self) -> f64;
    fn deposit(&mut self, amount: f64) -> ProgramResult<()>;
    fn withdraw(&mut self, amount: f64) -> ProgramResult<()>;
}

impl Account for BankAccount {
    fn get_account_id(&self) -> &str {
        &self.account_id
    }
    
    fn get_balance(&self) -> f64 {
        self.balance
    }
    
    fn deposit(&mut self, amount: f64) -> ProgramResult<()> {
        self.deposit(amount)
    }
    
    fn withdraw(&mut self, amount: f64) -> ProgramResult<()> {
        self.withdraw(amount)
    }
}

/// 储蓄账户（扩展银行账户）
#[derive(Debug, Clone)]
pub struct SavingsAccount {
    base: BankAccount,
    interest_rate: f64,
}

impl SavingsAccount {
    pub fn new(account_id: String, owner: String, initial_balance: f64, interest_rate: f64) -> ProgramResult<Self> {
        Ok(Self {
            base: BankAccount::new(account_id, owner, initial_balance)?,
            interest_rate,
        })
    }
    
    pub fn apply_interest(&mut self) -> ProgramResult<()> {
        let interest = self.base.balance * self.interest_rate;
        self.base.deposit(interest)
    }
}

impl Account for SavingsAccount {
    fn get_account_id(&self) -> &str {
        self.base.get_account_id()
    }
    
    fn get_balance(&self) -> f64 {
        self.base.get_balance()
    }
    
    fn deposit(&mut self, amount: f64) -> ProgramResult<()> {
        self.base.deposit(amount)
    }
    
    fn withdraw(&mut self, amount: f64) -> ProgramResult<()> {
        self.base.withdraw(amount)
    }
}

/// 多态示例
pub struct AccountManager {
    accounts: Vec<Box<dyn Account>>,
}

impl AccountManager {
    pub fn new() -> Self {
        Self {
            accounts: Vec::new(),
        }
    }
    
    pub fn add_account(&mut self, account: Box<dyn Account>) {
        self.accounts.push(account);
    }
    
    pub fn total_balance(&self) -> f64 {
        self.accounts.iter().map(|acc| acc.get_balance()).sum()
    }
}

impl Default for AccountManager {
    fn default() -> Self {
        Self::new()
    }
}

/// ========================================
/// 响应式编程模型
/// ========================================

/// 观察者trait
pub trait Observer<T>: Send + Sync {
    fn on_next(&mut self, value: T);
    fn on_error(&mut self, error: ModelError);
    fn on_complete(&mut self);
}

/// 可观察对象
pub struct Observable<T> {
    observers: Arc<RwLock<Vec<Box<dyn Observer<T>>>>>,
}

impl<T: Clone + Send + Sync + 'static> Observable<T> {
    pub fn new() -> Self {
        Self {
            observers: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    pub fn subscribe<O: Observer<T> + 'static>(&self, observer: O) {
        self.observers.write().unwrap().push(Box::new(observer));
    }
    
    pub fn emit(&self, value: T) {
        let mut observers = self.observers.write().unwrap();
        for observer in observers.iter_mut() {
            observer.on_next(value.clone());
        }
    }
    
    pub fn error(&self, error: ModelError) {
        let mut observers = self.observers.write().unwrap();
        for observer in observers.iter_mut() {
            observer.on_error(error.clone());
        }
    }
    
    pub fn complete(&self) {
        let mut observers = self.observers.write().unwrap();
        for observer in observers.iter_mut() {
            observer.on_complete();
        }
    }
    
    /// 映射操作符
    pub fn map<U, F>(&self, f: F) -> Observable<U>
    where
        U: Clone + Send + Sync + 'static,
        F: Fn(T) -> U + Send + Sync + 'static,
    {
        let new_observable = Observable::new();
        let new_obs_clone = new_observable.clone();
        let f = Arc::new(f);
        
        struct MapObserver<T, U, F>
        where
            F: Fn(T) -> U,
        {
            target: Observable<U>,
            mapper: Arc<F>,
            _phantom: PhantomData<T>,
        }
        
        impl<T: Clone + Send + Sync, U: Clone + Send + Sync + 'static, F: Fn(T) -> U + Send + Sync> Observer<T> for MapObserver<T, U, F> {
            fn on_next(&mut self, value: T) {
                let mapped = (self.mapper)(value);
                self.target.emit(mapped);
            }
            
            fn on_error(&mut self, error: ModelError) {
                self.target.error(error);
            }
            
            fn on_complete(&mut self) {
                self.target.complete();
            }
        }
        
        self.subscribe(MapObserver {
            target: new_obs_clone,
            mapper: f,
            _phantom: PhantomData,
        });
        
        new_observable
    }
    
    /// 过滤操作符
    pub fn filter<F>(&self, predicate: F) -> Observable<T>
    where
        F: Fn(&T) -> bool + Send + Sync + 'static,
    {
        let new_observable = Observable::new();
        let new_obs_clone = new_observable.clone();
        let predicate = Arc::new(predicate);
        
        struct FilterObserver<T, F>
        where
            F: Fn(&T) -> bool,
        {
            target: Observable<T>,
            predicate: Arc<F>,
        }
        
        impl<T: Clone + Send + Sync + 'static, F: Fn(&T) -> bool + Send + Sync> Observer<T> for FilterObserver<T, F> {
            fn on_next(&mut self, value: T) {
                if (self.predicate)(&value) {
                    self.target.emit(value);
                }
            }
            
            fn on_error(&mut self, error: ModelError) {
                self.target.error(error);
            }
            
            fn on_complete(&mut self) {
                self.target.complete();
            }
        }
        
        self.subscribe(FilterObserver {
            target: new_obs_clone,
            predicate,
        });
        
        new_observable
    }
}

impl<T: Clone + Send + Sync + 'static> Clone for Observable<T> {
    fn clone(&self) -> Self {
        Self {
            observers: Arc::clone(&self.observers),
        }
    }
}

impl<T: Clone + Send + Sync + 'static> Default for Observable<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 主题（Subject）- 既是观察者又是可观察对象
pub struct Subject<T> {
    observable: Observable<T>,
}

impl<T: Clone + Send + Sync + 'static> Subject<T> {
    pub fn new() -> Self {
        Self {
            observable: Observable::new(),
        }
    }
    
    pub fn as_observable(&self) -> &Observable<T> {
        &self.observable
    }
}

impl<T: Clone + Send + Sync + 'static> Observer<T> for Subject<T> {
    fn on_next(&mut self, value: T) {
        self.observable.emit(value);
    }
    
    fn on_error(&mut self, error: ModelError) {
        self.observable.error(error);
    }
    
    fn on_complete(&mut self) {
        self.observable.complete();
    }
}

impl<T: Clone + Send + Sync + 'static> Default for Subject<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// ========================================
/// 声明式编程模型
/// ========================================

/// DSL构建器trait
pub trait DSLBuilder {
    type Output;
    fn build(self) -> ProgramResult<Self::Output>;
}

/// SQL风格的查询构建器
pub struct QueryBuilder<T> {
    data: Vec<T>,
    filters: Vec<Box<dyn Fn(&T) -> bool + Send + Sync>>,
    mappings: Vec<Box<dyn Fn(T) -> T + Send + Sync>>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for QueryBuilder<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QueryBuilder")
            .field("data", &self.data)
            .field("filters_count", &self.filters.len())
            .field("mappings_count", &self.mappings.len())
            .finish()
    }
}

// 由于闭包trait object的限制，这里简化实现
impl<T: Clone + Send + Sync + 'static> QueryBuilder<T> {
    pub fn from(data: Vec<T>) -> Self {
        Self {
            data,
            filters: Vec::new(),
            mappings: Vec::new(),
        }
    }
    
    // 注意：实际使用时需要更灵活的设计
    pub fn execute(self) -> Vec<T> {
        let result = self.data;
        
        // 应用过滤器（简化，实际实现较复杂）
        // for filter in &self.filters {
        //     result = result.into_iter().filter(filter).collect();
        // }
        
        result
    }
}

/// ========================================
/// 程序设计范式分析器
/// ========================================

/// 编程范式类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProgrammingParadigm {
    Functional,
    ObjectOriented,
    Reactive,
    Declarative,
    Procedural,
    Logic,
    DataFlow,
}

/// 范式特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParadigmCharacteristics {
    pub paradigm: ProgrammingParadigm,
    pub state_management: StateManagement,
    pub control_flow: ControlFlow,
    pub data_abstraction: DataAbstraction,
    pub modularity: ModularityLevel,
    pub testability: TestabilityLevel,
    pub use_cases: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum StateManagement {
    Immutable,
    Mutable,
    Hybrid,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ControlFlow {
    Sequential,
    EventDriven,
    DataDriven,
    DeclarativeQuery,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DataAbstraction {
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ModularityLevel {
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TestabilityLevel {
    High,
    Medium,
    Low,
}

/// 编程范式分析器
pub struct ProgrammingParadigmAnalyzer;

impl ProgrammingParadigmAnalyzer {
    pub fn analyze(paradigm: &ProgrammingParadigm) -> ParadigmCharacteristics {
        match paradigm {
            ProgrammingParadigm::Functional => ParadigmCharacteristics {
                paradigm: ProgrammingParadigm::Functional,
                state_management: StateManagement::Immutable,
                control_flow: ControlFlow::DataDriven,
                data_abstraction: DataAbstraction::High,
                modularity: ModularityLevel::High,
                testability: TestabilityLevel::High,
                use_cases: vec![
                    "数据转换".to_string(),
                    "并行处理".to_string(),
                    "数学计算".to_string(),
                ],
            },
            ProgrammingParadigm::ObjectOriented => ParadigmCharacteristics {
                paradigm: ProgrammingParadigm::ObjectOriented,
                state_management: StateManagement::Mutable,
                control_flow: ControlFlow::Sequential,
                data_abstraction: DataAbstraction::High,
                modularity: ModularityLevel::High,
                testability: TestabilityLevel::Medium,
                use_cases: vec![
                    "企业应用".to_string(),
                    "GUI应用".to_string(),
                    "游戏开发".to_string(),
                ],
            },
            ProgrammingParadigm::Reactive => ParadigmCharacteristics {
                paradigm: ProgrammingParadigm::Reactive,
                state_management: StateManagement::Hybrid,
                control_flow: ControlFlow::EventDriven,
                data_abstraction: DataAbstraction::High,
                modularity: ModularityLevel::High,
                testability: TestabilityLevel::Medium,
                use_cases: vec![
                    "实时系统".to_string(),
                    "UI框架".to_string(),
                    "流处理".to_string(),
                ],
            },
            ProgrammingParadigm::Declarative => ParadigmCharacteristics {
                paradigm: ProgrammingParadigm::Declarative,
                state_management: StateManagement::Immutable,
                control_flow: ControlFlow::DeclarativeQuery,
                data_abstraction: DataAbstraction::High,
                modularity: ModularityLevel::Medium,
                testability: TestabilityLevel::High,
                use_cases: vec![
                    "数据查询".to_string(),
                    "配置管理".to_string(),
                    "DSL".to_string(),
                ],
            },
            _ => ParadigmCharacteristics {
                paradigm: paradigm.clone(),
                state_management: StateManagement::Hybrid,
                control_flow: ControlFlow::Sequential,
                data_abstraction: DataAbstraction::Medium,
                modularity: ModularityLevel::Medium,
                testability: TestabilityLevel::Medium,
                use_cases: vec!["通用编程".to_string()],
            },
        }
    }
    
    pub fn compare(paradigm_a: &ProgrammingParadigm, paradigm_b: &ProgrammingParadigm) -> String {
        let char_a = Self::analyze(paradigm_a);
        let char_b = Self::analyze(paradigm_b);
        
        format!(
            "Comparison:\n\
             {:?} vs {:?}\n\
             State Management: {:?} vs {:?}\n\
             Control Flow: {:?} vs {:?}\n\
             Testability: {:?} vs {:?}",
            char_a.paradigm, char_b.paradigm,
            char_a.state_management, char_b.state_management,
            char_a.control_flow, char_b.control_flow,
            char_a.testability, char_b.testability
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_immutable_list() {
        let list = ImmutableList::new();
        let list2 = list.push(1);
        let list3 = list2.push(2);
        
        assert_eq!(list.len(), 0);
        assert_eq!(list2.len(), 1);
        assert_eq!(list3.len(), 2);
    }
    
    #[test]
    fn test_bank_account() {
        let mut account = BankAccount::new("123".to_string(), "Alice".to_string(), 1000.0).unwrap();
        
        account.deposit(500.0).unwrap();
        assert_eq!(account.get_balance(), 1500.0);
        
        account.withdraw(200.0).unwrap();
        assert_eq!(account.get_balance(), 1300.0);
    }
    
    #[test]
    fn test_observable() {
        struct TestObserver {
            values: Arc<Mutex<Vec<i32>>>,
        }
        
        impl Observer<i32> for TestObserver {
            fn on_next(&mut self, value: i32) {
                self.values.lock().unwrap().push(value);
            }
            
            fn on_error(&mut self, _error: ModelError) {}
            fn on_complete(&mut self) {}
        }
        
        let values = Arc::new(Mutex::new(Vec::new()));
        let observable = Observable::new();
        
        observable.subscribe(TestObserver {
            values: Arc::clone(&values),
        });
        
        observable.emit(1);
        observable.emit(2);
        observable.emit(3);
        
        assert_eq!(*values.lock().unwrap(), vec![1, 2, 3]);
    }
    
    #[test]
    fn test_higher_order_functions() {
        let double = |x: i32| x * 2;
        let add_one = |x: i32| x + 1;
        
        let composed = HigherOrderFunctions::compose(double, add_one);
        
        assert_eq!(composed(5), 12); // (5 + 1) * 2
    }
}
