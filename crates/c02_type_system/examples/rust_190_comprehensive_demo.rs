//! Rust 1.90 全面示例（类型系统与基础语法纵览）
//!
//! 覆盖要点：
//! - 原生类型/字面量/溢出策略（debug/release）
//! - 所有权/借用/切片最小可用范式
//! - 结构体/枚举/模式/匹配与守卫
//! - Trait/泛型/约束/关联类型/默认方法
//! - 常量/静态/常量函数与常量泛型
//! - 模块与可见性、`use` 引入、`pub(crate)` 粒度
//! - 错误处理：`Result`、`?`、自定义错误
//! - `impl Trait`（参数/返回位置）
//! - `From`/`Into`/`TryFrom`/`AsRef`/`Deref` 常用转换
//! - 并发准备（`Send`/`Sync` 边界的直觉性示例）

use core::fmt::{Display, Formatter, Result as FmtResult};

// ---------------- 原生类型与字面量 ----------------
const ANSWER: i32 = 42;
static GLOBAL_COUNTER: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

// 常量函数（在 const 上下文可用的纯函数）
const fn square(x: i32) -> i32 { x * x }

// ---------------- 自定义类型：结构体/枚举 ----------------
#[derive(Debug, Clone, PartialEq, Eq)]
struct User { id: u64, name: String }

#[derive(Debug, Clone, PartialEq)]
enum LoginState { Anonymous, LoggedIn(User) }

impl Display for LoginState {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LoginState::Anonymous => write!(f, "Anonymous"),
            LoginState::LoggedIn(u) => write!(f, "LoggedIn({}:{})", u.id, u.name),
        }
    }
}

// ---------------- Trait / 泛型 / 关联类型 ----------------
trait Repository {
    type Item;
    fn get(&self, id: u64) -> Option<Self::Item>;
}

#[derive(Default)]
struct MemoryRepo<T> { data: Vec<(u64, T)> }

impl<T: Clone> Repository for MemoryRepo<T> {
    type Item = T;
    fn get(&self, id: u64) -> Option<Self::Item> {
        self.data.iter().find(|(k, _)| *k == id).map(|(_, v)| v.clone())
    }
}

impl<T> MemoryRepo<T> {
    fn insert(&mut self, id: u64, value: T) { self.data.push((id, value)); }
}

// ---------------- 错误处理与 From/Into ----------------
#[allow(dead_code)]
#[derive(Debug)]
enum AppError { NotFound, ParseInt(core::num::ParseIntError) }

impl From<core::num::ParseIntError> for AppError {
    fn from(e: core::num::ParseIntError) -> Self { AppError::ParseInt(e) }
}

fn parse_and_double(s: &str) -> Result<i32, AppError> {
    let n: i32 = s.parse()?; // `?` 自动从 ParseIntError 转为 AppError
    Ok(n * 2)
}

// ---------------- impl Trait（返回位置） ----------------
fn make_greeter(name: String) -> impl Fn() -> String {
    move || format!("Hello, {}!", name)
}

// ---------------- 常量泛型 ----------------
fn sum<const N: usize>(xs: [i32; N]) -> i32 { xs.iter().sum() }

// ---------------- Send/Sync 边界直觉 ----------------
// i32: Send + Sync；Rc<T>: !Send/!Sync；Arc<T>: Send + Sync（若 T: Send/Sync）

fn main() {
    // examples 默认启用标准库（std），此处直接使用 Vec 即可。
    let mut repo: MemoryRepo<User> = MemoryRepo { data: Vec::new() };
    repo.insert(1, User { id: 1, name: String::from("Alice") });
    let s = repo.get(1).map(|u| LoginState::LoggedIn(u)).unwrap_or(LoginState::Anonymous);
    println!("state: {}", s);

    // 模式匹配与守卫
    match &s {
        LoginState::LoggedIn(User { id, name }) if *id == 1 => println!("guard ok for {}", name),
        LoginState::LoggedIn(_) => println!("logged in"),
        LoginState::Anonymous => println!("guest"),
    }

    // 常量与静态
    println!("const ANSWER={}, const square(5)={}", ANSWER, square(5));
    let prev = GLOBAL_COUNTER.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
    println!("global counter: {} -> {}", prev, prev + 1);

    // 错误处理
    println!("parse_and_double('21') => {:?}", parse_and_double("21"));
    println!("parse_and_double('xx') => {:?}", parse_and_double("xx"));

    // impl Trait 返回闭包
    let hi = make_greeter(String::from("Rust 1.90"));
    println!("{}", hi());

    // 常量泛型
    let s3 = sum([1, 2, 3]);
    let s4 = sum([1, 2, 3, 4]);
    println!("sum3={}, sum4={}", s3, s4);
}


