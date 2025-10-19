//! Rust 1.90 GATs 零拷贝观察者模式高级示例
//! 
//! 本示例展示：
//! 1. 使用 GATs 实现零拷贝的观察者模式
//! 2. 借用视图（Borrowing View）避免克隆
//! 3. 多种数据类型的观察者
//! 4. 事件过滤和转换
//! 5. 性能对比：GATs vs 克隆方式
//! 
//! ## 设计说明
//! 
//! GATs（泛型关联类型）使 trait 不再 dyn-compatible（对象安全），因此不能
//! 使用 `Box<dyn Observer>` 等 trait 对象。本示例使用枚举包装不同类型的
//! 观察者来解决这个问题，这是 Rust 中处理此类情况的惯用方法。

use std::time::Instant;
use std::collections::HashMap;

// ============================================================================
// 核心 GATs 观察者 Trait
// ============================================================================

/// GATs 观察者 trait - 支持借用视图
pub trait Observer {
    /// 关联类型：借用视图（带生命周期）
    type ViewType<'a> where Self: 'a;
    
    /// 接收借用的数据（零拷贝）
    fn update<'a>(&'a mut self, view: Self::ViewType<'a>);
    
    /// 观察者名称
    fn name(&self) -> &str;
}

/// 主题 trait
pub trait Subject {
    type Item;
    type ObserverType: for<'a> Observer;
    
    fn attach(&mut self, observer: Self::ObserverType);
    fn detach(&mut self, name: &str) -> bool;
    fn notify(&mut self);
}

// ============================================================================
// 示例 1: 字符串观察者 - 统计分析
// ============================================================================

/// 字符串统计观察者
pub struct StringStatsObserver {
    name: String,
    total_chars: usize,
    total_words: usize,
    total_lines: usize,
    update_count: usize,
}

impl StringStatsObserver {
    pub fn new(name: impl Into<String>) -> Self {
        StringStatsObserver {
            name: name.into(),
            total_chars: 0,
            total_words: 0,
            total_lines: 0,
            update_count: 0,
        }
    }
    
    pub fn stats(&self) -> StatsReport {
        StatsReport {
            total_chars: self.total_chars,
            total_words: self.total_words,
            total_lines: self.total_lines,
            update_count: self.update_count,
            avg_chars_per_update: if self.update_count > 0 {
                self.total_chars / self.update_count
            } else {
                0
            },
        }
    }
}

#[derive(Debug)]
pub struct StatsReport {
    pub total_chars: usize,
    pub total_words: usize,
    pub total_lines: usize,
    pub update_count: usize,
    pub avg_chars_per_update: usize,
}

impl Observer for StringStatsObserver {
    type ViewType<'a> = &'a str;
    
    fn update<'a>(&'a mut self, view: &'a str) {
        self.total_chars += view.len();
        self.total_words += view.split_whitespace().count();
        self.total_lines += view.lines().count();
        self.update_count += 1;
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

/// 字符串模式匹配观察者
pub struct PatternObserver {
    name: String,
    patterns: Vec<String>,
    matches: HashMap<String, usize>,
}

impl PatternObserver {
    pub fn new(name: impl Into<String>, patterns: Vec<String>) -> Self {
        let mut matches = HashMap::new();
        for pattern in &patterns {
            matches.insert(pattern.clone(), 0);
        }
        
        PatternObserver {
            name: name.into(),
            patterns,
            matches,
        }
    }
    
    pub fn match_count(&self, pattern: &str) -> usize {
        self.matches.get(pattern).copied().unwrap_or(0)
    }
    
    pub fn total_matches(&self) -> usize {
        self.matches.values().sum()
    }
}

impl Observer for PatternObserver {
    type ViewType<'a> = &'a str;
    
    fn update<'a>(&'a mut self, view: &'a str) {
        for pattern in &self.patterns {
            let count = view.matches(pattern.as_str()).count();
            *self.matches.get_mut(pattern).unwrap() += count;
        }
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// ============================================================================
// 示例 2: 切片数据观察者 - 数值分析
// ============================================================================

/// 数值统计观察者
pub struct NumStatsObserver {
    name: String,
    sum: i64,
    count: usize,
    min: Option<i32>,
    max: Option<i32>,
}

impl NumStatsObserver {
    pub fn new(name: impl Into<String>) -> Self {
        NumStatsObserver {
            name: name.into(),
            sum: 0,
            count: 0,
            min: None,
            max: None,
        }
    }
    
    pub fn average(&self) -> Option<f64> {
        if self.count > 0 {
            Some(self.sum as f64 / self.count as f64)
        } else {
            None
        }
    }
    
    pub fn stats(&self) -> NumStatsReport {
        NumStatsReport {
            sum: self.sum,
            count: self.count,
            average: self.average(),
            min: self.min,
            max: self.max,
        }
    }
}

#[derive(Debug)]
pub struct NumStatsReport {
    pub sum: i64,
    pub count: usize,
    pub average: Option<f64>,
    pub min: Option<i32>,
    pub max: Option<i32>,
}

impl Observer for NumStatsObserver {
    type ViewType<'a> = &'a [i32];
    
    fn update<'a>(&'a mut self, view: &'a [i32]) {
        for &num in view {
            self.sum += num as i64;
            self.count += 1;
            
            self.min = Some(match self.min {
                Some(min) if num < min => num,
                Some(min) => min,
                None => num,
            });
            
            self.max = Some(match self.max {
                Some(max) if num > max => num,
                Some(max) => max,
                None => num,
            });
        }
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

/// 数值过滤观察者（仅记录符合条件的数值）
pub struct FilterObserver<F> 
where
    F: Fn(i32) -> bool,
{
    name: String,
    predicate: F,
    matching_values: Vec<i32>,
}

impl<F> FilterObserver<F>
where
    F: Fn(i32) -> bool,
{
    pub fn new(name: impl Into<String>, predicate: F) -> Self {
        FilterObserver {
            name: name.into(),
            predicate,
            matching_values: Vec::new(),
        }
    }
    
    pub fn matching_count(&self) -> usize {
        self.matching_values.len()
    }
    
    pub fn matching_values(&self) -> &[i32] {
        &self.matching_values
    }
}

impl<F> Observer for FilterObserver<F>
where
    F: Fn(i32) -> bool + 'static,
{
    type ViewType<'a> = &'a [i32];
    
    fn update<'a>(&'a mut self, view: &'a [i32]) {
        for &num in view {
            if (self.predicate)(num) {
                self.matching_values.push(num);
            }
        }
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// ============================================================================
// 示例 3: 结构体数据观察者 - 复杂类型
// ============================================================================

#[derive(Debug, Clone)]
pub struct User {
    pub id: u32,
    pub name: String,
    pub email: String,
    pub age: u8,
    pub active: bool,
}

/// 用户统计观察者（借用 User 引用）
pub struct UserStatsObserver {
    name: String,
    total_users: usize,
    active_users: usize,
    total_age: u64,
    email_domains: HashMap<String, usize>,
}

impl UserStatsObserver {
    pub fn new(name: impl Into<String>) -> Self {
        UserStatsObserver {
            name: name.into(),
            total_users: 0,
            active_users: 0,
            total_age: 0,
            email_domains: HashMap::new(),
        }
    }
    
    pub fn average_age(&self) -> Option<f64> {
        if self.total_users > 0 {
            Some(self.total_age as f64 / self.total_users as f64)
        } else {
            None
        }
    }
    
    pub fn stats(&self) -> UserStatsReport {
        UserStatsReport {
            total_users: self.total_users,
            active_users: self.active_users,
            average_age: self.average_age(),
            top_domain: self.email_domains.iter()
                .max_by_key(|(_, count)| *count)
                .map(|(domain, _)| domain.clone()),
        }
    }
}

#[derive(Debug)]
pub struct UserStatsReport {
    pub total_users: usize,
    pub active_users: usize,
    pub average_age: Option<f64>,
    pub top_domain: Option<String>,
}

impl Observer for UserStatsObserver {
    type ViewType<'a> = &'a User;
    
    fn update<'a>(&'a mut self, user: &'a User) {
        self.total_users += 1;
        if user.active {
            self.active_users += 1;
        }
        self.total_age += user.age as u64;
        
        if let Some(domain) = user.email.split('@').nth(1) {
            *self.email_domains.entry(domain.to_string()).or_insert(0) += 1;
        }
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// ============================================================================
// Subject 实现 - 使用枚举包装观察者以避免 trait object 问题
// ============================================================================

/// 字符串观察者枚举（因为 GATs 不支持 dyn trait）
pub enum StringObserverType {
    Stats(StringStatsObserver),
    Pattern(PatternObserver),
}

impl StringObserverType {
    fn update(&mut self, view: &str) {
        match self {
            StringObserverType::Stats(obs) => obs.update(view),
            StringObserverType::Pattern(obs) => obs.update(view),
        }
    }
    
    #[allow(dead_code)]
    fn name(&self) -> &str {
        match self {
            StringObserverType::Stats(obs) => obs.name(),
            StringObserverType::Pattern(obs) => obs.name(),
        }
    }
}

/// 字符串主题
pub struct StringSubject {
    data: String,
    observers: Vec<StringObserverType>,
}

impl StringSubject {
    pub fn new(data: String) -> Self {
        StringSubject {
            data,
            observers: Vec::new(),
        }
    }
    
    pub fn set_data(&mut self, new_data: String) {
        self.data = new_data;
        self.notify();
    }
    
    pub fn append(&mut self, text: &str) {
        self.data.push_str(text);
        self.notify();
    }
    
    fn notify(&mut self) {
        let data_ref = self.data.as_str();
        for observer in &mut self.observers {
            observer.update(data_ref);
        }
    }
    
    pub fn attach_stats(&mut self, observer: StringStatsObserver) {
        self.observers.push(StringObserverType::Stats(observer));
    }
    
    pub fn attach_pattern(&mut self, observer: PatternObserver) {
        self.observers.push(StringObserverType::Pattern(observer));
    }
    
    pub fn observer_count(&self) -> usize {
        self.observers.len()
    }
    
    pub fn get_stats_observer(&self, name: &str) -> Option<&StringStatsObserver> {
        self.observers.iter().find_map(|obs| match obs {
            StringObserverType::Stats(s) if s.name() == name => Some(s),
            _ => None,
        })
    }
    
    pub fn get_pattern_observer(&self, name: &str) -> Option<&PatternObserver> {
        self.observers.iter().find_map(|obs| match obs {
            StringObserverType::Pattern(p) if p.name() == name => Some(p),
            _ => None,
        })
    }
}

/// 数值观察者枚举
pub enum NumObserverType {
    Stats(NumStatsObserver),
    Filter(FilterObserver<fn(i32) -> bool>),
}

impl NumObserverType {
    fn update(&mut self, view: &[i32]) {
        match self {
            NumObserverType::Stats(obs) => obs.update(view),
            NumObserverType::Filter(obs) => obs.update(view),
        }
    }
}

/// 数值切片主题
pub struct NumVecSubject {
    data: Vec<i32>,
    observers: Vec<NumObserverType>,
}

impl NumVecSubject {
    pub fn new(data: Vec<i32>) -> Self {
        NumVecSubject {
            data,
            observers: Vec::new(),
        }
    }
    
    pub fn set_data(&mut self, new_data: Vec<i32>) {
        self.data = new_data;
        self.notify();
    }
    
    pub fn push(&mut self, value: i32) {
        self.data.push(value);
        self.notify();
    }
    
    fn notify(&mut self) {
        let data_slice = self.data.as_slice();
        for observer in &mut self.observers {
            observer.update(data_slice);
        }
    }
    
    pub fn attach_stats(&mut self, observer: NumStatsObserver) {
        self.observers.push(NumObserverType::Stats(observer));
    }
    
    pub fn attach_filter(&mut self, observer: FilterObserver<fn(i32) -> bool>) {
        self.observers.push(NumObserverType::Filter(observer));
    }
    
    pub fn get_stats_observer(&self, name: &str) -> Option<&NumStatsObserver> {
        self.observers.iter().find_map(|obs| match obs {
            NumObserverType::Stats(s) if s.name() == name => Some(s),
            _ => None,
        })
    }
    
    pub fn get_filter_observer(&self, name: &str) -> Option<&FilterObserver<fn(i32) -> bool>> {
        self.observers.iter().find_map(|obs| match obs {
            NumObserverType::Filter(f) if f.name() == name => Some(f),
            _ => None,
        })
    }
}

// ============================================================================
// 性能对比：GATs vs 克隆
// ============================================================================

/// 旧方式：克隆数据的观察者
pub trait CloningObserver {
    type Data: Clone;
    fn update_cloned(&mut self, data: Self::Data);
}

pub struct CloningStringObserver {
    pub last_data: String,
    pub update_count: usize,
}

impl CloningObserver for CloningStringObserver {
    type Data = String;
    
    fn update_cloned(&mut self, data: String) {
        self.last_data = data;
        self.update_count += 1;
    }
}

/// 性能基准测试
pub fn benchmark_gats_vs_cloning() {
    const ITERATIONS: usize = 10_000;
    const DATA_SIZE: usize = 1000;
    
    let test_data = "A".repeat(DATA_SIZE);
    
    println!("📊 性能对比 (数据大小: {} 字节, {}次迭代)", DATA_SIZE, ITERATIONS);
    println!("{}", "-".repeat(70));
    
    // GATs 方式（零拷贝）
    let start = Instant::now();
    {
        let mut observer = StringStatsObserver::new("bench");
        for _ in 0..ITERATIONS {
            observer.update(test_data.as_str());
        }
    }
    let gats_duration = start.elapsed();
    
    // 克隆方式
    let start = Instant::now();
    {
        let mut observer = CloningStringObserver {
            last_data: String::new(),
            update_count: 0,
        };
        for _ in 0..ITERATIONS {
            observer.update_cloned(test_data.clone());
        }
    }
    let clone_duration = start.elapsed();
    
    println!("GATs方式（零拷贝）:");
    println!("  耗时: {:?}", gats_duration);
    println!("  平均: {:.2} ns/iter", gats_duration.as_nanos() as f64 / ITERATIONS as f64);
    println!("  内存分配: 0 次");
    
    println!("\n克隆方式:");
    println!("  耗时: {:?}", clone_duration);
    println!("  平均: {:.2} ns/iter", clone_duration.as_nanos() as f64 / ITERATIONS as f64);
    println!("  内存分配: {} 次 (每次 {} 字节)", ITERATIONS, DATA_SIZE);
    
    let speedup = clone_duration.as_nanos() as f64 / gats_duration.as_nanos() as f64;
    println!("\n性能提升: {:.2}x 倍", speedup);
    
    let memory_saved = DATA_SIZE * ITERATIONS;
    println!("节省内存: {:.2} MB", memory_saved as f64 / 1_000_000.0);
}

// ============================================================================
// 主函数 - 演示所有示例
// ============================================================================

fn main() {
    println!("🦀 Rust 1.90 GATs 零拷贝观察者模式高级示例\n");
    println!("{}", "=".repeat(70));
    
    // 示例 1: 字符串观察者
    println!("\n📌 示例 1: 字符串统计和模式匹配");
    println!("{}", "-".repeat(70));
    
    let mut subject = StringSubject::new("Hello Rust World!".to_string());
    
    // 附加统计观察者
    subject.attach_stats(StringStatsObserver::new("stats"));
    
    // 附加模式匹配观察者
    subject.attach_pattern(PatternObserver::new(
        "patterns",
        vec!["Rust".to_string(), "World".to_string(), "!".to_string()],
    ));
    
    println!("初始数据: \"{}\"", "Hello Rust World!");
    println!("观察者数量: {}", subject.observer_count());
    
    // 更新数据
    subject.set_data("Rust is awesome! Rust is fast!".to_string());
    subject.append(" Programming in Rust is fun!");
    
    // 显示统计结果
    if let Some(stats_obs) = subject.get_stats_observer("stats") {
        let stats = stats_obs.stats();
        println!("\n字符串统计:");
        println!("  总字符数: {}", stats.total_chars);
        println!("  总单词数: {}", stats.total_words);
        println!("  总行数: {}", stats.total_lines);
        println!("  更新次数: {}", stats.update_count);
    }
    
    if let Some(pattern_obs) = subject.get_pattern_observer("patterns") {
        println!("\n模式匹配:");
        println!("  'Rust' 出现: {} 次", pattern_obs.match_count("Rust"));
        println!("  'World' 出现: {} 次", pattern_obs.match_count("World"));
        println!("  '!' 出现: {} 次", pattern_obs.match_count("!"));
    }
    
    // 示例 2: 数值观察者
    println!("\n📌 示例 2: 数值统计和过滤");
    println!("{}", "-".repeat(70));
    
    let mut num_subject = NumVecSubject::new(vec![10, 20, 30, 40, 50]);
    
    // 附加统计观察者
    num_subject.attach_stats(NumStatsObserver::new("num_stats"));
    
    // 附加过滤观察者（偶数）
    fn is_even(x: i32) -> bool { x % 2 == 0 }
    num_subject.attach_filter(FilterObserver::new("even_filter", is_even));
    
    // 附加过滤观察者（大于25）
    fn is_greater_than_25(x: i32) -> bool { x > 25 }
    num_subject.attach_filter(FilterObserver::new("gt25_filter", is_greater_than_25));
    
    println!("初始数据: [10, 20, 30, 40, 50]");
    
    num_subject.push(60);
    num_subject.push(15);
    num_subject.push(25);
    
    println!("添加数据: 60, 15, 25");
    
    // 显示数值统计
    if let Some(stats_obs) = num_subject.get_stats_observer("num_stats") {
        let stats = stats_obs.stats();
        println!("\n数值统计:");
        println!("  总和: {}", stats.sum);
        println!("  数量: {}", stats.count);
        println!("  平均值: {:.2}", stats.average.unwrap_or(0.0));
        println!("  最小值: {:?}", stats.min);
        println!("  最大值: {:?}", stats.max);
    }
    
    if let Some(even_obs) = num_subject.get_filter_observer("even_filter") {
        println!("\n偶数过滤:");
        println!("  匹配数量: {}", even_obs.matching_count());
        println!("  匹配值: {:?}", even_obs.matching_values());
    }
    
    if let Some(gt25_obs) = num_subject.get_filter_observer("gt25_filter") {
        println!("\n大于25过滤:");
        println!("  匹配数量: {}", gt25_obs.matching_count());
        println!("  匹配值: {:?}", gt25_obs.matching_values());
    }
    
    // 示例 3: 用户数据观察者
    println!("\n📌 示例 3: 用户数据统计");
    println!("{}", "-".repeat(70));
    
    let mut user_stats = UserStatsObserver::new("user_stats");
    
    let users = vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@gmail.com".to_string(),
            age: 25,
            active: true,
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@yahoo.com".to_string(),
            age: 30,
            active: true,
        },
        User {
            id: 3,
            name: "Charlie".to_string(),
            email: "charlie@gmail.com".to_string(),
            age: 35,
            active: false,
        },
        User {
            id: 4,
            name: "David".to_string(),
            email: "david@outlook.com".to_string(),
            age: 28,
            active: true,
        },
    ];
    
    for user in &users {
        user_stats.update(user);
    }
    
    let stats = user_stats.stats();
    println!("用户统计:");
    println!("  总用户数: {}", stats.total_users);
    println!("  活跃用户: {}", stats.active_users);
    println!("  平均年龄: {:.1} 岁", stats.average_age.unwrap_or(0.0));
    println!("  主要邮箱域: {}", stats.top_domain.unwrap_or_else(|| "N/A".to_string()));
    
    // 性能对比
    println!("\n📌 性能对比: GATs vs 克隆");
    println!("{}", "-".repeat(70));
    benchmark_gats_vs_cloning();
    
    // 总结
    println!("\n{}", "=".repeat(70));
    println!("✅ GATs 零拷贝观察者的优势:");
    println!("  1. 零拷贝：避免数据克隆，显著提升性能");
    println!("  2. 内存高效：不产生额外的堆分配");
    println!("  3. 类型安全：编译时保证借用的正确性");
    println!("  4. 灵活性高：支持任意引用类型的视图");
    println!("  5. 可组合：可以组合多个观察者");
    println!("\n⚠️ 注意事项:");
    println!("  1. 观察者更新时数据被短暂借用");
    println!("  2. 观察者不能持有数据的所有权");
    println!("  3. 需要仔细管理生命周期");
    println!("  4. trait对象需要 HRTB (for<'a>)");
    println!("{}", "=".repeat(70));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_string_stats_observer() {
        let mut observer = StringStatsObserver::new("test");
        observer.update("Hello World");
        observer.update("Rust Programming");
        
        let stats = observer.stats();
        assert_eq!(stats.update_count, 2);
        assert!(stats.total_chars > 0);
        assert!(stats.total_words > 0);
    }
    
    #[test]
    fn test_pattern_observer() {
        let mut observer = PatternObserver::new(
            "test",
            vec!["test".to_string(), "rust".to_string()],
        );
        
        observer.update("test rust test");
        assert_eq!(observer.match_count("test"), 2);
        assert_eq!(observer.match_count("rust"), 1);
        assert_eq!(observer.total_matches(), 3);
    }
    
    #[test]
    fn test_num_stats_observer() {
        let mut observer = NumStatsObserver::new("test");
        observer.update(&[1, 2, 3, 4, 5]);
        
        let stats = observer.stats();
        assert_eq!(stats.sum, 15);
        assert_eq!(stats.count, 5);
        assert_eq!(stats.average, Some(3.0));
        assert_eq!(stats.min, Some(1));
        assert_eq!(stats.max, Some(5));
    }
    
    #[test]
    fn test_filter_observer() {
        let mut observer = FilterObserver::new("test", |x| x % 2 == 0);
        observer.update(&[1, 2, 3, 4, 5, 6]);
        
        assert_eq!(observer.matching_count(), 3);
        assert_eq!(observer.matching_values(), &[2, 4, 6]);
    }
    
    #[test]
    fn test_user_stats_observer() {
        let mut observer = UserStatsObserver::new("test");
        
        let user = User {
            id: 1,
            name: "Test".to_string(),
            email: "test@example.com".to_string(),
            age: 25,
            active: true,
        };
        
        observer.update(&user);
        
        let stats = observer.stats();
        assert_eq!(stats.total_users, 1);
        assert_eq!(stats.active_users, 1);
        assert_eq!(stats.average_age, Some(25.0));
    }
}

