//! Rust 特定设计惯用法与模式
//! Rust design pattern
//!
//! 本模块涵盖 Rust 生态中独特且广泛使用的设计惯用法（idioms）和模式，
//! this module Rust ecosystem in and design （idioms）and ，
//! 包括类型状态（typestate）、新类型（newtype）、访问者（visitor）模式在 Rust 中的表达，
//! type state （typestate）、type （newtype）、visitor （visitor）in Rust in express ，
//! 以及 RAII 守卫、`Into` 特质、错误累积和内部可变性等核心惯用法。
//! and RAII 、`Into` trait 、and inside etc. core 。
//!
//! 所有示例仅使用安全的稳定版 Rust，禁止 `unsafe` 代码。
//! all example Rust， `unsafe` 。

use std::cell::{Cell, RefCell};
use std::fmt;
use std::ops::Deref;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// 1. Typestate 模式 —— 将状态机编码进类型系统
// ============================================================================

/// # Typestate 模式
/// # Typestate pattern
/// Typestate Rust type system state machine design 。
/// 通过将不同的状态表示为不同的类型，并在状态转换时返回新的类型，
/// will state represent as type ，and in state conversion type ，
/// 我们可以在编译期就阻止无效的状态转换，使得「非法状态不可表示」。
/// can in ineffective state conversion ，「state represent 」。
///
/// ## 核心思想
/// ## core thought
/// - 每个状态是一个独立的类型
/// - status type
/// - 状态转换通过消耗旧值并返回新值来实现
/// - statusconversionoldvaluenewvalue implementation
/// - 只能在特定状态下调用的方法，只在该状态的类型上实现
/// - statuslowermethodstatustypeupper implementation
///
/// ## 优势
/// ## strength
/// - 编译期保证状态正确性，无需运行时检查
/// - state ，runtime
/// - 状态转换清晰明确，API 自文档化
/// - state conversion clear explicit ，API
/// - 消除大量 `unwrap` 和无效状态的分支
/// - `unwrap` and ineffective state
///
/// ## 权衡
/// ##
/// - 类型数量增加，代码量膨胀
/// - type quantity ，
/// - 学习曲线更陡峭，对初学者不够友好
/// - learn line ，to
/// - 某些场景下需要泛型参数传递，增加复杂度
/// - scenario under generic parameter ，complex
///
/// ## 真实应用
/// ## true application
/// - Rocket 框架的 Request Guards
/// - `typed-builder` crate
/// - HTTP 客户端/服务器的状态管理
/// - HTTP /state
/// - 文件句柄和网络连接的生命周期管理
/// - file handle and network lifetime
pub struct TypestatePattern;

impl TypestatePattern {
    /// 返回 typestate 模式的概念说明
    /// typestate concept explain
    pub fn description() -> &'static str {
        "Typestate 模式通过将状态机的每个状态编码为不同的类型，使得无效状态在编译期不可表示。"
    }

    /// 返回该模式的优势说明
    /// this strength explain
    pub fn benefits() -> &'static str {
        "优势：编译期状态验证、消除运行时检查、API 自文档化。"
    }

    /// 返回该模式的权衡说明
    /// this explain
    pub fn trade_offs() -> &'static str {
        "权衡：更多类型定义、更陡峭的学习曲线、可能增加代码冗余。"
    }

    /// 返回真实应用场景
    /// real application scenario
    pub fn real_world_usage() -> &'static str {
        "真实应用：Rocket request guards、typed-builder crate、数据库连接池状态管理。"
    }
}

// -------------------- 示例 A：文件句柄状态机 --------------------

/// 文件已关闭（初始状态）
/// （initial state ）
pub struct FileClosed {
    path: PathBuf,
}

/// 文件已打开（可读写）
/// （）
pub struct FileOpen {
    path: PathBuf,
    // 模拟文件描述符
    fd: usize,
}

/// 文件正在读取
/// in
pub struct FileReading {
    path: PathBuf,
    fd: usize,
    position: usize,
}

/// 文件正在写入
/// in
pub struct FileWriting {
    path: PathBuf,
    fd: usize,
    position: usize,
}

impl FileClosed {
    /// 创建新的关闭状态文件句柄
    /// Create new statusfile
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    /// 打开文件，状态从 Closed 转换为 Open
    /// ，state from Closed conversion as Open
    pub fn open(self) -> FileOpen {
        FileOpen {
            path: self.path,
            fd: 1, // 模拟分配 fd
        }
    }

    /// 获取文件路径
    /// Get filepath
    pub fn path(&self) -> &PathBuf {
        &self.path
    }
}

impl FileOpen {
    /// 进入读取状态
    /// state
    pub fn read(self) -> FileReading {
        FileReading {
            path: self.path,
            fd: self.fd,
            position: 0,
        }
    }

    /// 进入写入状态
    /// state
    pub fn write(self) -> FileWriting {
        FileWriting {
            path: self.path,
            fd: self.fd,
            position: 0,
        }
    }

    /// 关闭文件，状态从 Open 转换为 Closed
    /// ，state from Open conversion as Closed
    pub fn close(self) -> FileClosed {
        FileClosed { path: self.path }
    }
}

impl FileReading {
    /// 模拟读取数据，返回读取到的字节数
    /// ，to
    pub fn read_bytes(&mut self, buf: &mut [u8]) -> usize {
        let n = buf.len();
        self.position += n;
        n
    }

    /// 获取当前读取位置
    /// Get current
    pub fn position(&self) -> usize {
        self.position
    }

    /// 完成读取，返回 Open 状态
    /// Complete Open status
    pub fn finish(self) -> FileOpen {
        FileOpen {
            path: self.path,
            fd: self.fd,
        }
    }
}

impl FileWriting {
    /// 模拟写入数据
    pub fn write_bytes(&mut self, data: &[u8]) -> usize {
        let n = data.len();
        self.position += n;
        n
    }

    /// 完成写入，返回 Open 状态
    /// Complete Open status
    pub fn finish(self) -> FileOpen {
        FileOpen {
            path: self.path,
            fd: self.fd,
        }
    }
}

// -------------------- 示例 B：HTTP 请求构建器 --------------------

/// HTTP 请求构建器 —— 无 URL 状态
/// HTTP without URL status
pub struct HttpRequestBuilderNoUrl;

/// HTTP 请求构建器 —— 已有 URL 状态
/// HTTP has URL status
pub struct HttpRequestBuilderHasUrl {
    url: String,
}

/// HTTP 请求构建器 —— 已有 URL 和方法状态
/// HTTP has URL method status
pub struct HttpRequestBuilderHasMethod {
    url: String,
    method: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
}

/// HTTP 请求构建器 —— 就绪状态（可构建）
/// HTTP builder —— state （）
pub struct HttpRequestBuilderReady {
    url: String,
    method: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
}

/// 构建完成的 HTTP 请求
/// HTTP
#[derive(Debug, Clone, PartialEq)]
pub struct HttpRequestBuilt {
    pub url: String,
    pub method: String,
    pub headers: Vec<(String, String)>,
    pub body: Option<String>,
}

impl HttpRequestBuilderNoUrl {
    /// 创建新的请求构建器
    /// builder
    pub fn new() -> Self {
        Self
    }

    /// 设置 URL，状态从 NoUrl 转换为 HasUrl
    /// Set URLstatus NoUrl conversion HasUrl
    pub fn url(self, url: impl Into<String>) -> HttpRequestBuilderHasUrl {
        HttpRequestBuilderHasUrl { url: url.into() }
    }
}

impl HttpRequestBuilderHasUrl {
    /// 设置 HTTP 方法，状态从 HasUrl 转换为 HasMethod
    /// Set HTTP methodstatus HasUrl conversion HasMethod
    pub fn method(self, method: impl Into<String>) -> HttpRequestBuilderHasMethod {
        HttpRequestBuilderHasMethod {
            url: self.url,
            method: method.into(),
            headers: Vec::new(),
            body: None,
        }
    }
}

impl HttpRequestBuilderHasMethod {
    /// 添加请求头
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.push((key.into(), value.into()));
        self
    }

    /// 设置请求体
    /// volume
    pub fn with_body(mut self, body: impl Into<String>) -> Self {
        self.body = Some(body.into());
        self
    }

    /// 完成构建，转换为 Ready 状态
    /// Complete conversion Ready status
    pub fn build(self) -> HttpRequestBuilderReady {
        HttpRequestBuilderReady {
            url: self.url,
            method: self.method,
            headers: self.headers,
            body: self.body,
        }
    }
}

impl HttpRequestBuilderReady {
    /// 添加额外的请求头
    /// outside
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.push((key.into(), value.into()));
        self
    }

    /// 最终构建 HTTP 请求
    /// ultimately HTTP
    pub fn finalize(self) -> HttpRequestBuilt {
        HttpRequestBuilt {
            url: self.url,
            method: self.method,
            headers: self.headers,
            body: self.body,
        }
    }
}

// ============================================================================
// 2. Newtype 模式 —— 细粒度类型安全包装器
// ============================================================================

/// # Newtype 模式
/// # Newtype pattern
/// Newtype as type struct ，
/// 在 Rust 中通常表现为包含单个字段的元组结构体（如 `UserId(u64)`）。
/// in Rust in as field struct （ `UserId(u64)`）。
/// 与类型别名（type alias）不同，newtype 是一个全新的类型，
/// and type （type alias），newtype type ，
/// 不能与原类型或其他 newtype 隐式互换。
/// cannot and type or its newtype 。
///
/// ## 核心思想
/// ## core thought
/// - 用编译器区分不同语义但底层相同的类型
/// - type
/// - 在不改变运行时开销的前提下增强类型安全
/// - runtimefrontlowerstrongtype safety
/// - 为基础类型提供自定义的行为实现
/// - typeprovidecustom implementation
///
/// ## 优势
/// ## strength
/// - 防止语义不兼容的值被混用（如把用户 ID 和订单 ID 传反）
/// - is （ ID and ID ）
/// - 可为基础类型实现外部 trait（孤儿规则绕过）
/// - as foundation type outside trait（rule ）
/// - 精确控制可见性和验证逻辑
/// - and
///
/// ## 常用派生
/// ##
/// - `Deref` / `DerefMut`：允许透明地访问内部值
/// - `Deref` / `DerefMut`internal value
/// - `From<T>` / `Into<T>`：零成本转换
/// - `From<T>` / `Into<T>`：cost conversion
/// - `Display`、`Debug`：自定义输出格式
/// - `Display`、`Debug`：definition
/// - `PartialEq`、`Eq`、`Hash`：用于集合和比较
///
/// ## 与类型别名的选择
/// ## and type
/// | 场景 | 推荐 |
/// | scenario | |
/// |------|------|
/// | 需要区分不同语义 | Newtype |
/// | | Newtype |
/// | 需要自定义 trait 实现 | Newtype |
/// | definition trait | Newtype |
/// | 需要运行时验证 | Newtype |
/// | runtime | Newtype |
/// | 仅为简化长类型名 | 类型别名 |
/// | as type | type |
/// | 需要完全兼容原类型 | 类型别名 |
/// | type | type |
pub struct NewtypePattern;

impl NewtypePattern {
    /// 返回 newtype 模式的概念说明
    /// newtype concept explain
    pub fn description() -> &'static str {
        "Newtype 模式通过创建单字段元组结构体，为基础类型赋予新的语义身份，零运行时开销。"
    }

    /// 返回 newtype 与类型别名的决策树说明
    /// newtype and type tree explain
    pub fn newtype_vs_type_alias() -> &'static str {
        "需要区分语义或自定义 trait 实现时选 Newtype；仅简化类型名时选类型别名。"
    }
}

/// 用户 ID（防止与订单 ID、产品 ID 混用）
/// ID（and ID、 ID ）
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UserId(pub u64);

/// 订单 ID
/// ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OrderId(pub u64);

/// 电子邮件地址（newtype + 验证）
/// （newtype + ）
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Email(String);

impl Email {
    /// 创建新的 Email，执行基础验证
    /// Create new Emailexecutionverify
    pub fn new(addr: impl Into<String>) -> Result<Self, String> {
        let addr = addr.into();
        if addr.contains('@') && addr.len() > 3 {
            Ok(Self(addr))
        } else {
            Err(format!("无效的邮箱地址: {}", addr))
        }
    }

    /// 获取内部字符串引用
    /// Get internalstringreference
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Email {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Deref for Email {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// 摄氏度温度（防止与华氏度混用）
/// （and ）
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Celsius(pub f64);

/// 华氏度温度
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Fahrenheit(pub f64);

impl Celsius {
    /// 转换为华氏度
    /// conversion as
    pub fn to_fahrenheit(self) -> Fahrenheit {
        Fahrenheit(self.0 * 9.0 / 5.0 + 32.0)
    }
}

impl Fahrenheit {
    /// 转换为摄氏度
    /// conversion as
    pub fn to_celsius(self) -> Celsius {
        Celsius((self.0 - 32.0) * 5.0 / 9.0)
    }
}

impl fmt::Display for Celsius {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.1}°C", self.0)
    }
}

impl fmt::Display for Fahrenheit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.1}°F", self.0)
    }
}

// ============================================================================
// 3. Visitor 模式在 Rust 中的表达
// ============================================================================

/// # Rust 中的 Visitor 模式
/// # Rust Visitor pattern
/// Visitor goal in type structure prerequisite under ，as its 。
/// 在 Rust 中，由于没有传统继承，visitor 通常有两种实现方式：
/// in Rust in ，，visitor way ：
///
/// ## 方式一：枚举 + match（Rust 偏好）
/// ## way ：enum + match（Rust ）
/// - 将所有变体集中在枚举中定义
/// - will all volume in in enum in definition
/// - 通过 `match` 分派处理逻辑
/// - `match`
/// - 优点：静态分派、零开销、编译期穷尽检查
/// - advantage ：、overhead 、
/// - 缺点：添加新类型需要修改枚举定义
/// - disadvantage ：type enum definition
///
/// ## 方式二：trait 对象动态分派
/// ## way ：trait to
/// - 定义 `Visitor` trait 和 `Accept` trait
/// - 通过 `dyn Trait` 实现运行时多态
/// - `dyn Trait` runtime
/// - 优点：易于扩展新类型（不修改现有代码）
/// - advantage ：type （）
/// - 缺点：动态分派开销、失去编译期穷尽检查
/// - disadvantage ：overhead 、
///
/// ## 何时使用
/// ##
/// - 操作频繁变化，但类型结构相对稳定 → 枚举 visitor
/// - ，but type structure to → enum visitor
/// - 类型结构频繁扩展，操作相对稳定 → trait visitor
/// - type structure ，to → trait visitor
/// - Rust 社区强烈偏好枚举方式，除非有明确的动态扩展需求
/// - Rust enum way ，explicit
///
/// ## 对比传统面向对象
/// ## object
/// | 特性 | 枚举 Visitor | Trait Visitor | 继承 Visitor |
/// |------|-------------|---------------|-------------|
/// | 分派方式 | 静态 | 动态 | 动态 |
/// | way | | | |
/// | 穷尽检查 | 有 | 无 | 无 |
/// | | | | |
/// | 添加操作 | 修改 match | 新增 trait | 新增方法 |
/// | | match | trait | method |
/// | 添加类型 | 修改枚举 | 实现 trait | 继承基类 |
/// | type | enum | trait | |
pub struct VisitorPatternRust;

impl VisitorPatternRust {
    /// 返回 visitor 模式的概念说明
    /// visitor concept explain
    pub fn description() -> &'static str {
        "Visitor 模式在不改变已有类型结构的前提下，通过分离操作与数据结构来添加新行为。"
    }

    /// 返回何时使用该模式的建议
    /// this
    pub fn when_to_use() -> &'static str {
        "当需要为稳定的数据结构添加多种不同操作，且希望避免修改原始类型时使用。"
    }

    /// 返回枚举 visitor 与 trait visitor 的对比说明
    /// enum visitor and trait visitor to explain
    pub fn enum_vs_trait_visitor() -> &'static str {
        "枚举+match：静态分派、编译期穷尽检查、零开销，适合类型稳定的场景。Trait \
         对象：动态分派、易于扩展新类型，适合类型频繁增加的场景。"
    }
}

// -------------------- 示例 A：枚举 Visitor（Rust 首选）--------------------

/// 表达式抽象语法树节点（枚举定义所有类型）
/// express tree node （enum definition all type ）
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// 字面量数值
    /// surface
    Lit(f64),
    /// 加法
    Add(Box<Expr>, Box<Expr>),
    /// 减法
    Sub(Box<Expr>, Box<Expr>),
    /// 乘法
    Mul(Box<Expr>, Box<Expr>),
    /// 除法
    Div(Box<Expr>, Box<Expr>),
    /// 一元取负
    Neg(Box<Expr>),
}

impl Expr {
    /// 创建字面量表达式
    /// surface express
    pub fn lit(value: f64) -> Self {
        Self::Lit(value)
    }

    /// 创建加法表达式
    /// express
    #[allow(clippy::should_implement_trait)]
    pub fn add(lhs: Self, rhs: Self) -> Self {
        Self::Add(Box::new(lhs), Box::new(rhs))
    }

    /// 创建乘法表达式
    /// express
    #[allow(clippy::should_implement_trait)]
    pub fn mul(lhs: Self, rhs: Self) -> Self {
        Self::Mul(Box::new(lhs), Box::new(rhs))
    }

    /// 创建除法表达式
    /// express
    #[allow(clippy::should_implement_trait)]
    pub fn div(lhs: Self, rhs: Self) -> Self {
        Self::Div(Box::new(lhs), Box::new(rhs))
    }

    /// 创建取负表达式
    /// express
    #[allow(clippy::should_implement_trait)]
    pub fn neg(inner: Self) -> Self {
        Self::Neg(Box::new(inner))
    }

    /// 枚举 Visitor：求值
    /// enum Visitor value
    pub fn eval(&self) -> Result<f64, String> {
        match self {
            Self::Lit(v) => Ok(*v),
            Self::Add(l, r) => Ok(l.eval()? + r.eval()?),
            Self::Sub(l, r) => Ok(l.eval()? - r.eval()?),
            Self::Mul(l, r) => Ok(l.eval()? * r.eval()?),
            Self::Div(l, r) => {
                let rhs = r.eval()?;
                if rhs == 0.0 {
                    Err("除零错误".to_string())
                } else {
                    Ok(l.eval()? / rhs)
                }
            }
            Self::Neg(e) => Ok(-e.eval()?),
        }
    }

    /// 枚举 Visitor：打印表达式（中缀表示）
    /// enum Visitor：express （in represent ）
    pub fn to_infix(&self) -> String {
        match self {
            Self::Lit(v) => format!("{}", v),
            Self::Add(l, r) => format!("({} + {})", l.to_infix(), r.to_infix()),
            Self::Sub(l, r) => format!("({} - {})", l.to_infix(), r.to_infix()),
            Self::Mul(l, r) => format!("({} * {})", l.to_infix(), r.to_infix()),
            Self::Div(l, r) => format!("({} / {})", l.to_infix(), r.to_infix()),
            Self::Neg(e) => format!("(-{})", e.to_infix()),
        }
    }

    /// 枚举 Visitor：统计节点数量
    /// enum Visitornode count
    pub fn node_count(&self) -> usize {
        match self {
            Self::Lit(_) => 1,
            Self::Neg(e) => 1 + e.node_count(),
            Self::Add(l, r) | Self::Sub(l, r) | Self::Mul(l, r) | Self::Div(l, r) => {
                1 + l.node_count() + r.node_count()
            }
        }
    }
}

// -------------------- 示例 B：Trait 对象 Visitor --------------------

/// 可被访问的元素 trait
/// is element trait
pub trait AstNode {
    /// 接受访问者
    /// visitor
    fn accept(&self, visitor: &mut dyn AstVisitor);
}

/// 访问者 trait
/// visitor trait
pub trait AstVisitor {
    /// 访问字面量
    /// surface
    fn visit_lit(&mut self, value: f64);
    /// 访问二元操作
    fn visit_binary(&mut self, op: BinaryOp, lhs: &dyn AstNode, rhs: &dyn AstNode);
    /// 访问一元操作
    fn visit_unary(&mut self, op: UnaryOp, operand: &dyn AstNode);
}

/// 二元操作类型
/// operation type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// 一元操作类型
/// operation type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
}

/// 字面量节点
/// surface node
pub struct LitNode {
    value: f64,
}

impl LitNode {
    /// 创建字面量节点
    /// create node
    pub fn new(value: f64) -> Self {
        Self { value }
    }
}

impl AstNode for LitNode {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.visit_lit(self.value);
    }
}

/// 二元操作节点
/// operation node
pub struct BinaryNode {
    op: BinaryOp,
    lhs: Box<dyn AstNode>,
    rhs: Box<dyn AstNode>,
}

impl BinaryNode {
    /// 创建二元操作节点
    /// createoperation node
    pub fn new(op: BinaryOp, lhs: Box<dyn AstNode>, rhs: Box<dyn AstNode>) -> Self {
        Self { op, lhs, rhs }
    }
}

impl AstNode for BinaryNode {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.visit_binary(self.op, self.lhs.as_ref(), self.rhs.as_ref());
    }
}

/// 一元操作节点
/// operation node
pub struct UnaryNode {
    op: UnaryOp,
    operand: Box<dyn AstNode>,
}

impl UnaryNode {
    /// 创建一元操作节点
    /// createoperation node
    pub fn new(op: UnaryOp, operand: Box<dyn AstNode>) -> Self {
        Self { op, operand }
    }
}

impl AstNode for UnaryNode {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.visit_unary(self.op, self.operand.as_ref());
    }
}

/// 求值访问者
/// visitor
pub struct EvalVisitor {
    stack: Vec<f64>,
}

impl EvalVisitor {
    /// 创建新的求值访问者
    /// Create new value
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    /// 执行求值，返回结果
    /// executionvalue result
    pub fn eval(mut self, root: &dyn AstNode) -> Result<f64, String> {
        root.accept(&mut self);
        self.stack.pop().ok_or_else(|| "空表达式".to_string())
    }
}

impl AstVisitor for EvalVisitor {
    fn visit_lit(&mut self, value: f64) {
        self.stack.push(value);
    }

    fn visit_binary(&mut self, op: BinaryOp, lhs: &dyn AstNode, rhs: &dyn AstNode) {
        lhs.accept(self);
        rhs.accept(self);
        let r = self.stack.pop().expect("栈空");
        let l = self.stack.pop().expect("栈空");
        let result = match op {
            BinaryOp::Add => l + r,
            BinaryOp::Sub => l - r,
            BinaryOp::Mul => l * r,
            BinaryOp::Div => {
                if r == 0.0 {
                    f64::NAN
                } else {
                    l / r
                }
            }
        };
        self.stack.push(result);
    }

    fn visit_unary(&mut self, op: UnaryOp, operand: &dyn AstNode) {
        operand.accept(self);
        let v = self.stack.pop().expect("栈空");
        let result = match op {
            UnaryOp::Neg => -v,
        };
        self.stack.push(result);
    }
}

// ============================================================================
// 4. 其他 Rust 核心惯用法
// ============================================================================

/// # 其他 Rust 核心惯用法
/// # its Rust core
///
/// 本结构体汇集了 Rust 开发中最常用但不易归类的设计惯用法，
/// this struct Rust in but categorization design ，
/// 包括资源管理、API 设计、错误处理和内部可变性等关键主题。
/// 、API design 、error handling and inside etc. key 。
///
/// ## 涵盖内容
/// ## inside
/// - RAII 守卫模式（Scope Guard）
/// - `Into` 特质用于 ergonomic API 设计
/// - `Into` ergonomic API design
/// - 内部可变性决策树（Cell vs RefCell vs Atomic vs Mutex）
pub struct OtherRustIdioms;

impl OtherRustIdioms {
    /// 返回 RAII 守卫模式的说明
    /// RAII explain
    pub fn raii_guard_description() -> &'static str {
        "RAII 守卫模式利用 Drop trait 在变量离开作用域时自动执行清理逻辑，确保资源安全释放。"
    }

    /// 返回 Into 特质的说明
    /// Into trait explain
    pub fn into_trait_description() -> &'static str {
        "使用 Into<T> 作为函数参数类型，允许调用者传递任何可自动转换为目标类型的值，提升 API \
         易用性。"
    }

    /// 返回错误累积模式的说明
    /// explain
    pub fn error_accumulation_description() -> &'static str {
        "错误累积模式收集所有验证错误而非遇到第一个就返回，适用于配置解析和表单验证场景。"
    }

    /// 返回内部可变性决策树的说明
    /// inside tree explain
    pub fn interior_mutability_decision_tree() -> &'static str {
        "Cell<T>：单线程 + Copy 类型；RefCell<T>：单线程 + 运行时借用检查；Atomic<T>：多线程 + \
         简单数值；Mutex<T>/RwLock<T>：多线程 + 复杂类型。"
    }
}

// -------------------- RAII 守卫示例 --------------------

/// 作用域守卫：在离开作用域时执行回调
/// role domain ：in role domain
pub struct ScopeGuard<F: FnOnce()> {
    callback: Option<F>,
}

impl<F: FnOnce()> ScopeGuard<F> {
    /// 创建新的作用域守卫
    /// role domain
    pub fn new(callback: F) -> Self {
        Self {
            callback: Some(callback),
        }
    }

    /// 手动解除守卫（不再执行回调）
    /// （）
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

// -------------------- Into 特质 ergonomic API 示例 --------------------

/// 演示 `Into` 特质用于接受灵活参数类型
/// `Into` flexible type
pub struct PathOpener;

impl PathOpener {
    /// 接受任何可转换为 PathBuf 的类型
    /// conversion PathBuf type
    pub fn open<P: Into<PathBuf>>(path: P) -> PathBuf {
        let path = path.into();
        // 模拟打开操作
        path
    }

    /// 接受任何可转换为 String 的类型
    /// conversion String type
    pub fn greet<N: Into<String>>(name: N) -> String {
        format!("Hello, {}!", name.into())
    }
}

// -------------------- 错误累积模式示例 --------------------

/// 验证错误
/// Verify error
#[derive(Debug, Clone, PartialEq)]
pub struct ValidationError {
    pub field: String,
    pub message: String,
}

/// 错误累积验证器
#[derive(Debug, Default)]
pub struct ErrorAccumulator {
    errors: Vec<ValidationError>,
}

impl ErrorAccumulator {
    /// 创建新的错误累积器
    /// Create new error
    pub fn new() -> Self {
        Self::default()
    }

    /// 添加错误
    pub fn push(&mut self, field: impl Into<String>, message: impl Into<String>) {
        self.errors.push(ValidationError {
            field: field.into(),
            message: message.into(),
        });
    }

    /// 条件验证：如果失败则累积错误
    /// verify error
    pub fn validate(
        &mut self,
        field: impl Into<String>,
        condition: bool,
        message: impl Into<String>,
    ) {
        if !condition {
            self.push(field, message);
        }
    }

    /// 获取所有错误
    /// Get haserror
    pub fn errors(&self) -> &[ValidationError] {
        &self.errors
    }

    /// 检查是否有错误
    /// whetherhas error
    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }

    /// 消耗自身，返回结果
    /// ，result
    pub fn into_result(self) -> Result<(), Vec<ValidationError>> {
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors)
        }
    }
}

// -------------------- 内部可变性决策树示例 --------------------

/// 使用 `Cell<T>` 进行单线程内部可变性（T 必须实现 Copy）
/// `Cell<T>` thread inside （T must Copy）
pub struct CellCounter {
    value: Cell<u64>,
}

impl CellCounter {
    /// 创建新计数器
    pub fn new() -> Self {
        Self {
            value: Cell::new(0),
        }
    }

    /// 递增（无需 &mut self）
    /// （ &mut self）
    pub fn increment(&self) {
        self.value.set(self.value.get() + 1);
    }

    /// 获取当前值
    /// Get current value
    pub fn get(&self) -> u64 {
        self.value.get()
    }
}

impl Default for CellCounter {
    fn default() -> Self {
        Self::new()
    }
}

/// 使用 `RefCell<T>` 进行单线程内部可变性（运行时借用检查）
/// `RefCell<T>` thread inside （runtime borrowing ）
pub struct RefCellLog {
    entries: RefCell<Vec<String>>,
}

impl RefCellLog {
    /// 创建新日志
    /// Create new logging
    pub fn new() -> Self {
        Self {
            entries: RefCell::new(Vec::new()),
        }
    }

    /// 追加日志（无需 &mut self）
    /// （ &mut self）
    pub fn append(&self, msg: impl Into<String>) {
        self.entries.borrow_mut().push(msg.into());
    }

    /// 获取日志数量
    /// Get loggingcount
    pub fn len(&self) -> usize {
        self.entries.borrow().len()
    }

    /// 检查是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        self.entries.borrow().is_empty()
    }

    /// 获取所有日志的克隆
    /// Get haslogging
    pub fn get_all(&self) -> Vec<String> {
        self.entries.borrow().clone()
    }
}

impl Default for RefCellLog {
    fn default() -> Self {
        Self::new()
    }
}

/// 使用 `AtomicUsize` 进行多线程无锁计数
/// `AtomicUsize` thread lock-free
pub struct AtomicCounter {
    value: AtomicUsize,
}

impl AtomicCounter {
    /// 创建新原子计数器
    /// Create new atomic
    pub fn new() -> Self {
        Self {
            value: AtomicUsize::new(0),
        }
    }

    /// 原子递增
    pub fn increment(&self) -> usize {
        self.value.fetch_add(1, Ordering::Relaxed)
    }

    /// 获取当前值
    /// Get current value
    pub fn get(&self) -> usize {
        self.value.load(Ordering::Relaxed)
    }
}

impl Default for AtomicCounter {
    fn default() -> Self {
        Self::new()
    }
}

/// 使用 `Mutex<T>` 进行多线程内部可变性
/// `Mutex<T>` thread inside
pub struct MutexLog {
    entries: Mutex<Vec<String>>,
}

impl MutexLog {
    /// 创建新的线程安全日志
    /// Create new threadsafetylogging
    pub fn new() -> Self {
        Self {
            entries: Mutex::new(Vec::new()),
        }
    }

    /// 追加日志
    pub fn append(&self, msg: impl Into<String>) {
        self.entries
            .lock()
            .expect("mutex poisoned")
            .push(msg.into());
    }

    /// 获取日志数量
    /// Get loggingcount
    pub fn len(&self) -> usize {
        self.entries.lock().expect("mutex poisoned").len()
    }

    /// 检查是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        self.entries.lock().expect("mutex poisoned").is_empty()
    }

    /// 获取所有日志
    /// Get haslogging
    pub fn get_all(&self) -> Vec<String> {
        self.entries.lock().expect("mutex poisoned").clone()
    }
}

impl Default for MutexLog {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    // ==================== TypestatePattern 测试 ====================

    #[test]
    fn test_typestate_file_handle() {
        // 正确的状态转换链：Closed -> Open -> Reading -> Open -> Closed
        let file = FileClosed::new("/tmp/test.txt");
        assert_eq!(file.path().display().to_string(), "/tmp/test.txt");

        let open = file.open();
        let mut reading = open.read();
        let mut buf = [0u8; 10];
        let n = reading.read_bytes(&mut buf);
        assert_eq!(n, 10);
        assert_eq!(reading.position(), 10);

        let open = reading.finish();
        let mut writing = open.write();
        let data = b"hello";
        let n = writing.write_bytes(data);
        assert_eq!(n, 5);

        let open = writing.finish();
        let _closed = open.close();
    }

    #[test]
    fn test_typestate_http_builder() {
        let request = HttpRequestBuilderNoUrl::new()
            .url("https://api.example.com/users")
            .method("GET")
            .header("Accept", "application/json")
            .build()
            .finalize();

        assert_eq!(request.url, "https://api.example.com/users");
        assert_eq!(request.method, "GET");
        assert_eq!(
            request.headers,
            vec![("Accept".to_string(), "application/json".to_string())]
        );
        assert_eq!(request.body, None);
    }

    #[test]
    fn test_typestate_descriptions() {
        assert!(!TypestatePattern::description().is_empty());
        assert!(!TypestatePattern::benefits().is_empty());
        assert!(!TypestatePattern::trade_offs().is_empty());
        assert!(!TypestatePattern::real_world_usage().is_empty());
    }

    // ==================== NewtypePattern 测试 ====================

    #[test]
    fn test_newtype_user_id() {
        let uid = UserId(42);
        assert_eq!(uid.0, 42);
        assert_eq!(uid, UserId(42));
        assert_ne!(uid, UserId(43));
    }

    #[test]
    fn test_newtype_email() {
        let email = Email::new("user@example.com").unwrap();
        assert_eq!(email.as_str(), "user@example.com");
        assert_eq!(email.to_string(), "user@example.com");
        assert!(Email::new("invalid").is_err());
    }

    #[test]
    fn test_newtype_temperature() {
        let c = Celsius(100.0);
        let f = c.to_fahrenheit();
        assert!((f.0 - 212.0).abs() < 0.001);
        assert_eq!(f.to_celsius().0, 100.0);

        assert_eq!(c.to_string(), "100.0°C");
        assert_eq!(f.to_string(), "212.0°F");
    }

    #[test]
    fn test_newtype_prevents_mixing() {
        // 编译器会阻止以下操作（此处仅作逻辑说明）：
        // let user_id = UserId(1);
        // let order_id = OrderId(1);
        // user_id == order_id // 编译错误：类型不匹配
        assert!(NewtypePattern::description().contains("Newtype"));
        assert!(NewtypePattern::newtype_vs_type_alias().contains("Newtype"));
    }

    // ==================== VisitorPatternRust 测试 ====================

    #[test]
    fn test_enum_visitor_eval() {
        // (1 + 2) * 3 = 9
        let expr = Expr::mul(Expr::add(Expr::lit(1.0), Expr::lit(2.0)), Expr::lit(3.0));
        assert_eq!(expr.eval().unwrap(), 9.0);

        // 除零
        let bad = Expr::div(Expr::lit(1.0), Expr::lit(0.0));
        assert!(bad.eval().is_err());
    }

    #[test]
    fn test_enum_visitor_infix() {
        let expr = Expr::add(Expr::lit(1.0), Expr::mul(Expr::lit(2.0), Expr::lit(3.0)));
        assert_eq!(expr.to_infix(), "(1 + (2 * 3))");
    }

    #[test]
    fn test_enum_visitor_node_count() {
        let expr = Expr::add(Expr::lit(1.0), Expr::mul(Expr::lit(2.0), Expr::lit(3.0)));
        assert_eq!(expr.node_count(), 5);
    }

    #[test]
    fn test_trait_visitor_eval() {
        let expr = BinaryNode::new(
            BinaryOp::Mul,
            Box::new(BinaryNode::new(
                BinaryOp::Add,
                Box::new(LitNode::new(1.0)),
                Box::new(LitNode::new(2.0)),
            )),
            Box::new(LitNode::new(3.0)),
        );
        let visitor = EvalVisitor::new();
        let result = visitor.eval(&expr).unwrap();
        assert!((result - 9.0).abs() < 0.001);
    }

    #[test]
    fn test_visitor_descriptions() {
        assert!(!VisitorPatternRust::description().is_empty());
        assert!(!VisitorPatternRust::when_to_use().is_empty());
        assert!(!VisitorPatternRust::enum_vs_trait_visitor().is_empty());
    }

    // ==================== OtherRustIdioms 测试 ====================

    #[test]
    fn test_scope_guard() {
        let mut value = 0;
        {
            let _guard = ScopeGuard::new(|| value = 42);
        }
        assert_eq!(value, 42);
    }

    #[test]
    fn test_scope_guard_dismiss() {
        let mut value = 0;
        {
            let guard = ScopeGuard::new(|| value = 42);
            guard.dismiss();
        }
        assert_eq!(value, 0);
    }

    #[test]
    fn test_into_path_api() {
        let path = PathOpener::open("/tmp/test");
        assert_eq!(path, PathBuf::from("/tmp/test"));

        let path = PathOpener::open(PathBuf::from("/tmp/test2"));
        assert_eq!(path, PathBuf::from("/tmp/test2"));
    }

    #[test]
    fn test_into_greet_api() {
        assert_eq!(PathOpener::greet("World"), "Hello, World!");
        assert_eq!(PathOpener::greet(String::from("Rust")), "Hello, Rust!");
    }

    #[test]
    fn test_error_accumulator() {
        let mut acc = ErrorAccumulator::new();
        let empty = String::new();
        acc.validate("name", !empty.is_empty(), "名称不能为空");
        acc.validate("age", 20 >= 18, "年龄必须大于等于18");
        acc.validate("email", false, "邮箱格式错误");

        assert!(!acc.is_empty());
        assert_eq!(acc.errors().len(), 2); // name 和 email 失败
        assert_eq!(acc.errors()[0].field, "name");
        assert_eq!(acc.errors()[1].field, "email");

        let result = acc.into_result();
        assert!(result.is_err());
    }

    #[test]
    fn test_error_accumulator_success() {
        let mut acc = ErrorAccumulator::new();
        acc.validate("name", true, "名称不能为空");
        assert!(acc.is_empty());
        assert!(acc.into_result().is_ok());
    }

    #[test]
    fn test_cell_counter() {
        let counter = CellCounter::new();
        counter.increment();
        counter.increment();
        assert_eq!(counter.get(), 2);
    }

    #[test]
    fn test_refcell_log() {
        let log = RefCellLog::new();
        log.append("first");
        log.append("second");
        assert_eq!(log.len(), 2);
        assert_eq!(log.get_all(), vec!["first", "second"]);
    }

    #[test]
    fn test_atomic_counter() {
        let counter = AtomicCounter::new();
        let prev = counter.increment();
        assert_eq!(prev, 0);
        assert_eq!(counter.get(), 1);
    }

    #[test]
    fn test_mutex_log() {
        let log = MutexLog::new();
        log.append("first");
        log.append("second");
        assert_eq!(log.len(), 2);
        assert_eq!(log.get_all(), vec!["first", "second"]);
    }

    #[test]
    fn test_mutex_log_thread_safety() {
        let log = Arc::new(MutexLog::new());
        let mut handles = vec![];

        for i in 0..10 {
            let log = Arc::clone(&log);
            handles.push(std::thread::spawn(move || {
                log.append(format!("msg-{}", i));
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(log.len(), 10);
    }

    #[test]
    fn test_idiom_descriptions() {
        assert!(!OtherRustIdioms::raii_guard_description().is_empty());
        assert!(!OtherRustIdioms::into_trait_description().is_empty());
        assert!(!OtherRustIdioms::error_accumulation_description().is_empty());
        assert!(!OtherRustIdioms::interior_mutability_decision_tree().is_empty());
    }
}
