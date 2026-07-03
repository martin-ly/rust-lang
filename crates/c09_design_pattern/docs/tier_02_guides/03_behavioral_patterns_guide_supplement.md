# 3.2 行为型模式补充篇

> **文档类型**: Tier 2 - 实践指南（补充）
> **补充内容**: Chain of Responsibility / Template Method / Memento / Mediator / Interpreter
> **难度**: ⭐⭐⭐ 中级
> **最后更新**: 2026-02-28

---

## 📋 目录

- [3.2 行为型模式补充篇](#32-行为型模式补充篇)
  - [📋 目录](#-目录)
  - [1. 责任链模式 (Chain of Responsibility)](#1-责任链模式-chain-of-responsibility)
    - [1.1 模式定义](#11-模式定义)
    - [1.2 Rust 实现](#12-rust-实现)
    - [1.3 使用场景](#13-使用场景)
  - [2. 模板方法模式 (Template Method)](#2-模板方法模式-template-method)
    - [2.1 模式定义](#21-模式定义)
    - [2.2 Rust 实现](#22-rust-实现)
    - [2.3 模板方法与策略模式的区别](#23-模板方法与策略模式的区别)
  - [3. 备忘录模式 (Memento)](#3-备忘录模式-memento)
    - [3.1 模式定义](#31-模式定义)
    - [3.2 Rust 实现](#32-rust-实现)
    - [3.3 适用场景](#33-适用场景)
  - [4. 中介者模式 (Mediator)](#4-中介者模式-mediator)
    - [4.1 模式定义](#41-模式定义)
    - [4.2 Rust 实现](#42-rust-实现)
    - [4.3 适用场景](#43-适用场景)
  - [5. 解释器模式 (Interpreter)](#5-解释器模式-interpreter)
    - [5.1 模式定义](#51-模式定义)
    - [5.2 Rust 实现（简单表达式求值器）](#52-rust-实现简单表达式求值器)
    - [5.3 适用场景](#53-适用场景)
  - [6. 享元模式 (Flyweight)](#6-享元模式-flyweight)
    - [6.1 模式定义](#61-模式定义)
    - [6.2 Rust 实现](#62-rust-实现)
    - [6.3 内部状态 vs 外部状态](#63-内部状态-vs-外部状态)
  - [✅ 完成检查](#-完成检查)
  - [**版本**: v1.0 (补充完整)](#版本-v10-补充完整)

## 1. 责任链模式 (Chain of Responsibility)

### 1.1 模式定义

责任链模式允许你将请求沿着处理者链进行发送。
收到请求后，每个处理者均可对请求进行处理，或将其传递给链上的下个处理者。

### 1.2 Rust 实现

```rust
// 处理者 trait
trait Handler {
    fn set_next(&mut self, next: Box<dyn Handler>) -> &mut dyn Handler;
    fn handle(&self, request: &str) -> Option<String>;
}

// 基础处理者（提供默认实现）
struct BaseHandler {
    next: Option<Box<dyn Handler>>,
}

impl BaseHandler {
    fn new() -> Self {
        Self { next: None }
    }
}

impl Handler for BaseHandler {
    fn set_next(&mut self, next: Box<dyn Handler>) -> &mut dyn Handler {
        self.next = Some(next);
        self
    }

    fn handle(&self, request: &str) -> Option<String> {
        self.next.as_ref()?.handle(request)
    }
}

// 具体处理者：认证检查
struct AuthHandler {
    base: BaseHandler,
}

impl AuthHandler {
    fn new() -> Self {
        Self { base: BaseHandler::new() }
    }
}

impl Handler for AuthHandler {
    fn set_next(&mut self, next: Box<dyn Handler>) -> &mut dyn Handler {
        self.base.set_next(next);
        self
    }

    fn handle(&self, request: &str) -> Option<String> {
        if request.starts_with("AUTH:") {
            println!("AuthHandler: 验证通过");
            self.base.handle(request)
        } else {
            println!("AuthHandler: 无需认证，继续");
            self.base.handle(request)
        }
    }
}

// 具体处理者：日志记录
struct LoggingHandler {
    base: BaseHandler,
}

impl LoggingHandler {
    fn new() -> Self {
        Self { base: BaseHandler::new() }
    }
}

impl Handler for LoggingHandler {
    fn set_next(&mut self, next: Box<dyn Handler>) -> &mut dyn Handler {
        self.base.set_next(next);
        self
    }

    fn handle(&self, request: &str) -> Option<String> {
        println!("LoggingHandler: 记录请求 {}", request);
        self.base.handle(request)
    }
}

// 具体处理者：最终处理
struct FinalHandler;

impl Handler for FinalHandler {
    fn set_next(&mut self, _next: Box<dyn Handler>) -> &mut dyn Handler {
        self
    }

    fn handle(&self, request: &str) -> Option<String> {
        Some(format!("处理完成: {}", request))
    }
}

// 使用示例
fn main() {
    let mut auth = AuthHandler::new();
    let mut logging = LoggingHandler::new();
    let final_handler = FinalHandler;

    logging.set_next(Box::new(final_handler));
    auth.set_next(Box::new(logging));

    let result = auth.handle("AUTH:admin");
    println!("{:?}", result);
}
```
### 1.3 使用场景

- 当程序需要使用不同方式处理不同种类的请求时
- 当必须按照顺序执行多个处理者时
- 当处理者的集合和顺序需要动态改变时

---

## 2. 模板方法模式 (Template Method)

### 2.1 模式定义

模板方法模式在超类中定义一个算法的骨架，将某些步骤延迟到子类中实现。

### 2.2 Rust 实现

```rust
// 使用 trait 定义算法骨架
trait DataMiner {
    // 模板方法 - 定义算法骨架
    fn mine(&self, path: &str) -> String {
        let file = self.open_file(path);
        let raw_data = self.extract_data(&file);
        let data = self.parse_data(&raw_data);
        let analysis = self.analyze(&data);
        self.send_report(&analysis);
        self.close_file(&file);
        analysis
    }

    // 必须由实现者提供的步骤
    fn open_file(&self, path: &str) -> String;
    fn extract_data(&self, file: &str) -> String;
    fn parse_data(&self, raw: &str) -> Vec<String>;

    // 默认实现，可被子类覆盖
    fn analyze(&self, data: &[String]) -> String {
        format!("分析了 {} 条数据", data.len())
    }

    fn send_report(&self, analysis: &str) {
        println!("发送报告: {}", analysis);
    }

    fn close_file(&self, file: &str) {
        println!("关闭文件: {}", file);
    }
}

// 具体实现：PDF数据挖掘
struct PdfDataMiner;

impl DataMiner for PdfDataMiner {
    fn open_file(&self, path: &str) -> String {
        format!("PDF文件({})", path)
    }

    fn extract_data(&self, file: &str) -> String {
        println!("从 {} 提取PDF数据", file);
        "PDF原始数据".to_string()
    }

    fn parse_data(&self, raw: &str) -> Vec<String> {
        vec![raw.to_string(), "PDF解析结果".to_string()]
    }
}

// 具体实现：CSV数据挖掘
struct CsvDataMiner {
    delimiter: char,
}

impl CsvDataMiner {
    fn new(delimiter: char) -> Self {
        Self { delimiter }
    }
}

impl DataMiner for CsvDataMiner {
    fn open_file(&self, path: &str) -> String {
        format!("CSV文件({})", path)
    }

    fn extract_data(&self, file: &str) -> String {
        println!("从 {} 提取CSV数据", file);
        "CSV原始数据".to_string()
    }

    fn parse_data(&self, raw: &str) -> Vec<String> {
        raw.split(self.delimiter)
            .map(|s| s.to_string())
            .collect()
    }
}

// 使用示例
fn main() {
    let pdf_miner = PdfDataMiner;
    let csv_miner = CsvDataMiner::new(',');

    println!("=== PDF挖掘 ===");
    pdf_miner.mine("data.pdf");

    println!("\n=== CSV挖掘 ===");
    csv_miner.mine("data.csv");
}
```
### 2.3 模板方法与策略模式的区别

| 模板方法 | 策略模式 |
|---------|---------|
| 继承（代码复用） | 组合（委托） |
| 算法骨架固定 | 算法可完全替换 |
| 部分步骤可覆盖 | 整个算法可替换 |

---

## 3. 备忘录模式 (Memento)

### 3.1 模式定义

备忘录模式允许在不暴露对象实现细节的情况下捕获和恢复对象的内部状态。

### 3.2 Rust 实现

```rust
// 备忘录 - 保存编辑器状态
#[derive(Clone)]
struct EditorMemento {
    content: String,
    cursor_position: usize,
    timestamp: std::time::SystemTime,
}

impl EditorMemento {
    fn new(content: String, cursor_position: usize) -> Self {
        Self {
            content,
            cursor_position,
            timestamp: std::time::SystemTime::now(),
        }
    }

    fn get_content(&self) -> &str {
        &self.content
    }

    fn get_cursor_position(&self) -> usize {
        self.cursor_position
    }
}

// 原发器 - 编辑器
struct Editor {
    content: String,
    cursor_position: usize,
}

impl Editor {
    fn new() -> Self {
        Self {
            content: String::new(),
            cursor_position: 0,
        }
    }

    fn type_text(&mut self, text: &str) {
        self.content.insert_str(self.cursor_position, text);
        self.cursor_position += text.len();
    }

    fn delete(&mut self) {
        if self.cursor_position < self.content.len() {
            self.content.remove(self.cursor_position);
        }
    }

    // 创建备忘录
    fn save(&self) -> EditorMemento {
        EditorMemento::new(self.content.clone(), self.cursor_position)
    }

    // 从备忘录恢复
    fn restore(&mut self, memento: &EditorMemento) {
        self.content = memento.get_content().to_string();
        self.cursor_position = memento.get_cursor_position();
    }

    fn get_content(&self) -> &str {
        &self.content
    }
}

// 管理者 - 历史记录
struct History {
    mementos: Vec<EditorMemento>,
    current: usize,
}

impl History {
    fn new() -> Self {
        Self {
            mementos: Vec::new(),
            current: 0,
        }
    }

    fn backup(&mut self, memento: EditorMemento) {
        // 删除当前位置之后的所有历史
        self.mementos.truncate(self.current);
        self.mementos.push(memento);
        self.current += 1;
    }

    fn undo(&mut self) -> Option<&EditorMemento> {
        if self.current > 0 {
            self.current -= 1;
            self.mementos.get(self.current)
        } else {
            None
        }
    }

    fn redo(&mut self) -> Option<&EditorMemento> {
        if self.current < self.mementos.len() {
            self.current += 1;
            self.mementos.get(self.current - 1)
        } else {
            None
        }
    }
}

// 使用示例
fn main() {
    let mut editor = Editor::new();
    let mut history = History::new();

    // 编辑并保存
    editor.type_text("Hello ");
    history.backup(editor.save());

    editor.type_text("World!");
    history.backup(editor.save());

    editor.delete();
    println!("当前内容: {}", editor.get_content());

    // Undo
    if let Some(memento) = history.undo() {
        editor.restore(memento);
        println!("Undo后: {}", editor.get_content());
    }

    // Undo again
    if let Some(memento) = history.undo() {
        editor.restore(memento);
        println!("再次Undo后: {}", editor.get_content());
    }
}
```
### 3.3 适用场景

- 需要创建对象状态快照以便恢复
- 直接访问对象状态会破坏封装
- 需要实现撤销/重做功能

---

## 4. 中介者模式 (Mediator)

### 4.1 模式定义

中介者模式让你能减少对象之间混乱无序的依赖关系。
该模式限制对象之间的直接交互，迫使它们通过一个中介者对象进行合作。

### 4.2 Rust 实现

```rust
use std::collections::HashMap;

// 中介者 trait
trait ChatMediator {
    fn send_message(&self, message: &str, user_id: &str);
    fn add_user(&mut self, user: Box<dyn User>);
}

// 用户 trait
trait User {
    fn get_id(&self) -> &str;
    fn get_name(&self) -> &str;
    fn receive_message(&self, message: &str, from: &str);
    fn send_message(&self, mediator: &dyn ChatMediator, message: &str);
}

// 具体中介者
struct ChatRoom {
    users: HashMap<String, Box<dyn User>>,
}

impl ChatRoom {
    fn new() -> Self {
        Self {
            users: HashMap::new(),
        }
    }
}

impl ChatMediator for ChatRoom {
    fn send_message(&self, message: &str, user_id: &str) {
        if let Some(user) = self.users.get(user_id) {
            user.receive_message(message, "System");
        }
    }

    fn add_user(&mut self, user: Box<dyn User>) {
        let id = user.get_id().to_string();
        let name = user.get_name().to_string();
        self.users.insert(id.clone(), user);

        // 通知其他用户有新成员加入
        for (uid, u) in &self.users {
            if uid != &id {
                u.receive_message(&format!("{} 加入了聊天室", name), "System");
            }
        }
    }
}

// 具体用户
struct ChatUser {
    id: String,
    name: String,
}

impl ChatUser {
    fn new(id: &str, name: &str) -> Self {
        Self {
            id: id.to_string(),
            name: name.to_string(),
        }
    }
}

impl User for ChatUser {
    fn get_id(&self) -> &str {
        &self.id
    }

    fn get_name(&self) -> &str {
        &self.name
    }

    fn receive_message(&self, message: &str, from: &str) {
        println!("[{} -> {}]: {}", from, self.name, message);
    }

    fn send_message(&self, mediator: &dyn ChatMediator, message: &str) {
        println!("{} 发送消息: {}", self.name, message);
        // 通过中介者广播给所有用户
        for i in 0..3 {
            mediator.send_message(message, &format!("user{}", i));
        }
    }
}

// 使用示例
fn main() {
    let mut chat_room = ChatRoom::new();

    let user1 = Box::new(ChatUser::new("user0", "Alice"));
    let user2 = Box::new(ChatUser::new("user1", "Bob"));
    let user3 = Box::new(ChatUser::new("user2", "Charlie"));

    chat_room.add_user(user1);
    chat_room.add_user(user2);
    chat_room.add_user(user3);

    // 注意：实际使用需要保存用户引用来发送消息
    // 这里简化为通过中介者直接发送
}
```
### 4.3 适用场景

- 当多个对象以复杂方式交互，导致难以维护
- 当需要复用组件，但依赖难以复用时
- 当创建大量子类来定制行为变得困难时

---

## 5. 解释器模式 (Interpreter)

### 5.1 模式定义

解释器模式实现一个专用语言，为其语法创建解释器。

### 5.2 Rust 实现（简单表达式求值器）

```rust
// 表达式 trait
trait Expression {
    fn interpret(&self, context: &Context) -> i32;
    fn to_string(&self) -> String;
}

// 上下文
struct Context {
    variables: std::collections::HashMap<String, i32>,
}

impl Context {
    fn new() -> Self {
        Self {
            variables: std::collections::HashMap::new(),
        }
    }

    fn set_variable(&mut self, name: &str, value: i32) {
        self.variables.insert(name.to_string(), value);
    }

    fn get_variable(&self, name: &str) -> i32 {
        *self.variables.get(name).unwrap_or(&0)
    }
}

// 数字表达式
struct NumberExpression {
    value: i32,
}

impl NumberExpression {
    fn new(value: i32) -> Self {
        Self { value }
    }
}

impl Expression for NumberExpression {
    fn interpret(&self, _context: &Context) -> i32 {
        self.value
    }

    fn to_string(&self) -> String {
        self.value.to_string()
    }
}

// 变量表达式
struct VariableExpression {
    name: String,
}

impl VariableExpression {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

impl Expression for VariableExpression {
    fn interpret(&self, context: &Context) -> i32 {
        context.get_variable(&self.name)
    }

    fn to_string(&self) -> String {
        self.name.clone()
    }
}

// 加法表达式
struct AddExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl AddExpression {
    fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        Self { left, right }
    }
}

impl Expression for AddExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) + self.right.interpret(context)
    }

    fn to_string(&self) -> String {
        format!("({} + {})", self.left.to_string(), self.right.to_string())
    }
}

// 减法表达式
struct SubtractExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl SubtractExpression {
    fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        Self { left, right }
    }
}

impl Expression for SubtractExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) - self.right.interpret(context)
    }

    fn to_string(&self) -> String {
        format!("({} - {})", self.left.to_string(), self.right.to_string())
    }
}

// 解析器
struct Parser;

impl Parser {
    fn parse(expression: &str) -> Box<dyn Expression> {
        // 简化的解析器 - 实际应用需要完整的语法分析
        // 这里演示解析 "x + 5 - 3" 这样的简单表达式
        Box::new(NumberExpression::new(42))  // 简化实现
    }
}

// 使用示例
fn main() {
    let mut context = Context::new();
    context.set_variable("x", 10);
    context.set_variable("y", 5);

    // 构建表达式树: (x + y) - 3
    let expression = SubtractExpression::new(
        Box::new(AddExpression::new(
            Box::new(VariableExpression::new("x")),
            Box::new(VariableExpression::new("y")),
        )),
        Box::new(NumberExpression::new(3)),
    );

    println!("表达式: {}", expression.to_string());
    println!("结果: {}", expression.interpret(&context));
}
```
### 5.3 适用场景

- 当需要解释简单的语法规则
- 当效率不是关键考虑因素时
- 当语法规则频繁变化时

---

## 6. 享元模式 (Flyweight)

### 6.1 模式定义

享元模式通过共享多个对象之间通用的状态，让你能在有限的内存容量中载入更多对象。

### 6.2 Rust 实现

```rust
use std::collections::HashMap;
use std::rc::Rc;

// 享元 - 共享的状态
#[derive(Clone, Debug)]
struct TreeType {
    name: String,
    color: String,
    texture: String,
}

impl TreeType {
    fn new(name: &str, color: &str, texture: &str) -> Self {
        Self {
            name: name.to_string(),
            color: color.to_string(),
            texture: texture.to_string(),
        }
    }

    fn draw(&self, x: i32, y: i32) {
        println!(
            "在({}, {})绘制{}树 [颜色={}, 纹理={}]",
            x, y, self.name, self.color, self.texture
        );
    }
}

// 享元工厂
struct TreeFactory {
    tree_types: HashMap<String, Rc<TreeType>>,
}

impl TreeFactory {
    fn new() -> Self {
        Self {
            tree_types: HashMap::new(),
        }
    }

    fn get_tree_type(&mut self, name: &str, color: &str, texture: &str) -> Rc<TreeType> {
        let key = format!("{}_{}_{}", name, color, texture);

        self.tree_types
            .entry(key.clone())
            .or_insert_with(|| Rc::new(TreeType::new(name, color, texture)))
            .clone()
    }

    fn get_tree_type_count(&self) -> usize {
        self.tree_types.len()
    }
}

// 上下文 - 外部状态
struct Tree {
    x: i32,
    y: i32,
    tree_type: Rc<TreeType>,
}

impl Tree {
    fn new(x: i32, y: i32, tree_type: Rc<TreeType>) -> Self {
        Self { x, y, tree_type }
    }

    fn draw(&self) {
        self.tree_type.draw(self.x, self.y);
    }
}

// 森林
struct Forest {
    trees: Vec<Tree>,
    factory: TreeFactory,
}

impl Forest {
    fn new() -> Self {
        Self {
            trees: Vec::new(),
            factory: TreeFactory::new(),
        }
    }

    fn plant_tree(&mut self, x: i32, y: i32, name: &str, color: &str, texture: &str) {
        let tree_type = self.factory.get_tree_type(name, color, texture);
        let tree = Tree::new(x, y, tree_type);
        self.trees.push(tree);
    }

    fn draw(&self) {
        for tree in &self.trees {
            tree.draw();
        }
    }

    fn get_tree_type_count(&self) -> usize {
        self.factory.get_tree_type_count()
    }
}

// 使用示例
fn main() {
    let mut forest = Forest::new();

    // 种植1000棵树，但只有2种类型
    for i in 0..500 {
        forest.plant_tree(i % 100, i / 100, "松树", "深绿", "粗糙");
    }

    for i in 0..500 {
        forest.plant_tree((i % 100) + 200, i / 100, "桦树", "白色", "光滑");
    }

    println!("总树数量: {}", 1000);
    println!("实际树类型对象数量: {}", forest.get_tree_type_count());
    println!("内存节省: {}%", (1.0 - 2.0/1000.0) * 100.0);

    // forest.draw();  // 绘制所有树
}
```
### 6.3 内部状态 vs 外部状态

| 内部状态（共享） | 外部状态（每个对象独立） |
|----------------|------------------------|
| 树的类型、颜色、纹理 | 树的位置坐标 (x, y) |
| 字体名称、大小 | 字符位置、颜色 |

---

## ✅ 完成检查

现在 23 种 GoF 设计模式 + Rust 特有模式全部完整：

**创建型模式 (6)**:

- ✅ Singleton / Factory Method / Abstract Factory / Builder / Prototype / Object Pool

**结构型模式 (8)**:

- ✅ Adapter / Bridge / Composite / Decorator / Facade / Proxy / **Flyweight**

**行为型模式 (12)**:

- ✅ Strategy / Observer / Command / Iterator / State / Visitor
- ✅ **Chain of Responsibility** / **Template Method** / **Memento** / **Mediator** / **Interpreter**

**Rust 特有模式 (3)**:

- ✅ RAII / Newtype / Typestate

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-02-28
**版本**: v1.0 (补充完整)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
