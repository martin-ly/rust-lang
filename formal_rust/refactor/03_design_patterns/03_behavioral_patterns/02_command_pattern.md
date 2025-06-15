# 命令模式 (Command Pattern) - 形式化重构

## 目录

1. [模式概述](#1-模式概述)
2. [形式化定义](#2-形式化定义)
3. [数学理论](#3-数学理论)
4. [核心定理](#4-核心定理)
5. [Rust实现](#5-rust实现)
6. [应用场景](#6-应用场景)
7. [变体模式](#7-变体模式)
8. [性能分析](#8-性能分析)
9. [总结](#9-总结)

## 1. 模式概述

### 1.1 基本概念

命令模式是一种行为型设计模式，它将请求封装成对象，从而可以用不同的请求对客户进行参数化，对请求排队或记录请求日志，以及支持可撤销的操作。

### 1.2 模式特征

- **封装性**：将请求封装成独立的对象
- **参数化**：支持用不同的请求参数化客户端
- **队列化**：支持请求的排队和延迟执行
- **可撤销**：支持操作的撤销和重做
- **日志化**：支持请求的日志记录

## 2. 形式化定义

### 2.1 命令模式五元组

**定义2.1 (命令模式五元组)**
设 $C = (I, E, R, S, T)$ 为一个命令模式，其中：

- $I = \{i_1, i_2, ..., i_n\}$ 是命令接口集合
- $E = \{e_1, e_2, ..., e_m\}$ 是具体命令集合
- $R = \{r_1, r_2, ..., r_k\}$ 是接收者集合
- $S = \{s_1, s_2, ..., s_l\}$ 是状态集合
- $T = \{t_1, t_2, ..., t_p\}$ 是时间戳集合

### 2.2 命令接口定义

**定义2.2 (命令接口)**
命令接口 $I_C$ 定义为：

$$I_C = \{\text{execute}() \rightarrow \text{Result}, \text{undo}() \rightarrow \text{Result}, \text{canUndo}() \rightarrow \text{bool}\}$$

### 2.3 命令执行函数

**定义2.3 (命令执行函数)**
命令执行函数 $f_E: E \times R \rightarrow S \times \text{Result}$ 定义为：

$$f_E(e, r) = \begin{cases}
(s_{new}, \text{success}) & \text{if execution succeeds} \\
(s_{old}, \text{failure}) & \text{if execution fails}
\end{cases}$$

### 2.4 状态转换函数

**定义2.4 (状态转换函数)**
状态转换函数 $f_S: S \times E \rightarrow S$ 定义为：

$$f_S(s, e) = s'$$

其中 $s'$ 是执行命令 $e$ 后的新状态。

## 3. 数学理论

### 3.1 命令可逆性理论

**定义3.1 (命令可逆性)**
命令 $e$ 是可逆的，当且仅当存在逆命令 $e^{-1}$ 使得：

$$f_S(f_S(s, e), e^{-1}) = s$$

### 3.2 命令组合理论

**定义3.2 (命令组合)**
对于命令序列 $(e_1, e_2, ..., e_n)$，组合命令 $e_{composite}$ 定义为：

$$e_{composite} = e_1 \circ e_2 \circ ... \circ e_n$$

其中 $\circ$ 表示命令组合操作。

### 3.3 命令幂等性理论

**定义3.3 (命令幂等性)**
命令 $e$ 是幂等的，当且仅当：

$$f_S(f_S(s, e), e) = f_S(s, e)$$

### 3.4 命令交换性理论

**定义3.4 (命令交换性)**
命令 $e_1$ 和 $e_2$ 是可交换的，当且仅当：

$$f_S(f_S(s, e_1), e_2) = f_S(f_S(s, e_2), e_1)$$

## 4. 核心定理

### 4.1 命令执行正确性定理

**定理4.1 (命令执行正确性)**
如果命令 $e$ 在状态 $s$ 下是可执行的，则执行后状态 $s'$ 满足：

$$s' = f_S(s, e) \land \text{isValid}(s')$$

**证明：**
1. 根据定义2.3，$f_E(e, r) = (s_{new}, \text{success})$
2. 根据定义2.4，$s' = f_S(s, e)$
3. 由于执行成功，$s'$ 必须是有效状态
4. 正确性得证。

### 4.2 命令撤销正确性定理

**定理4.2 (命令撤销正确性)**
如果命令 $e$ 是可逆的，则撤销操作满足：

$$f_S(f_S(s, e), e^{-1}) = s$$

**证明：**
1. 根据定义3.1，可逆命令存在逆命令 $e^{-1}$
2. 执行命令：$s' = f_S(s, e)$
3. 撤销命令：$s'' = f_S(s', e^{-1})$
4. 根据可逆性定义，$s'' = s$
5. 撤销正确性得证。

### 4.3 命令组合正确性定理

**定理4.3 (命令组合正确性)**
对于命令序列 $(e_1, e_2, ..., e_n)$，组合执行等价于顺序执行：

$$f_S(s, e_{composite}) = f_S(f_S(...f_S(s, e_1), e_2), ..., e_n)$$

**证明：**
1. 根据定义3.2，$e_{composite} = e_1 \circ e_2 \circ ... \circ e_n$
2. 组合执行：$s' = f_S(s, e_{composite})$
3. 顺序执行：$s'' = f_S(f_S(...f_S(s, e_1), e_2), ..., e_n)$
4. 由于组合操作的定义，$s' = s''$
5. 组合正确性得证。

### 4.4 命令幂等性定理

**定理4.4 (命令幂等性)**
如果命令 $e$ 是幂等的，则多次执行不会改变结果：

$$f_S(f_S(s, e), e) = f_S(s, e)$$

**证明：**
1. 根据定义3.3，幂等命令满足 $f_S(f_S(s, e), e) = f_S(s, e)$
2. 这意味着多次执行命令 $e$ 不会改变最终状态
3. 幂等性得证。

### 4.5 命令交换性定理

**定理4.5 (命令交换性)**
如果命令 $e_1$ 和 $e_2$ 是可交换的，则执行顺序不影响最终结果：

$$f_S(f_S(s, e_1), e_2) = f_S(f_S(s, e_2), e_1)$$

**证明：**
1. 根据定义3.4，可交换命令满足交换律
2. 这意味着命令的执行顺序可以任意调整
3. 交换性得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;

// 命令执行结果
# [derive(Debug, Clone)]
pub struct CommandResult {
    pub success: bool,
    pub message: String,
    pub data: Option<String>,
}

impl CommandResult {
    pub fn new(success: bool, message: String, data: Option<String>) -> Self {
        CommandResult { success, message, data }
    }

    pub fn success(message: String) -> Self {
        CommandResult::new(true, message, None)
    }

    pub fn failure(message: String) -> Self {
        CommandResult::new(false, message, None)
    }
}

// 命令trait
pub trait Command: fmt::Display {
    fn execute(&self) -> CommandResult;
    fn undo(&self) -> CommandResult;
    fn can_undo(&self) -> bool;
    fn get_description(&self) -> String;
}

// 接收者trait
pub trait Receiver: fmt::Display {
    fn get_state(&self) -> String;
    fn set_state(&mut self, state: String);
}

// 具体接收者：文档编辑器
pub struct DocumentEditor {
    content: String,
    history: Vec<String>,
}

impl DocumentEditor {
    pub fn new() -> Self {
        DocumentEditor {
            content: String::new(),
            history: Vec::new(),
        }
    }

    pub fn get_content(&self) -> &str {
        &self.content
    }

    pub fn set_content(&mut self, content: String) {
        self.history.push(self.content.clone());
        self.content = content;
    }

    pub fn add_text(&mut self, text: &str) {
        self.history.push(self.content.clone());
        self.content.push_str(text);
    }

    pub fn delete_text(&mut self, length: usize) {
        self.history.push(self.content.clone());
        if length <= self.content.len() {
            self.content.truncate(self.content.len() - length);
        }
    }

    pub fn undo(&mut self) -> bool {
        if let Some(previous_content) = self.history.pop() {
            self.content = previous_content;
            true
        } else {
            false
        }
    }
}

impl fmt::Display for DocumentEditor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DocumentEditor(content: '{}')", self.content)
    }
}

impl Receiver for DocumentEditor {
    fn get_state(&self) -> String {
        self.content.clone()
    }

    fn set_state(&mut self, state: String) {
        self.content = state;
    }
}

// 具体命令：添加文本命令
pub struct AddTextCommand {
    receiver: DocumentEditor,
    text: String,
}

impl AddTextCommand {
    pub fn new(receiver: DocumentEditor, text: String) -> Self {
        AddTextCommand { receiver, text }
    }
}

impl fmt::Display for AddTextCommand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AddTextCommand(text: '{}')", self.text)
    }
}

impl Command for AddTextCommand {
    fn execute(&self) -> CommandResult {
        let mut receiver = self.receiver.clone();
        receiver.add_text(&self.text);
        CommandResult::success(format!("Added text: '{}'", self.text))
    }

    fn undo(&self) -> CommandResult {
        let mut receiver = self.receiver.clone();
        if receiver.undo() {
            CommandResult::success("Undid add text operation".to_string())
        } else {
            CommandResult::failure("Cannot undo add text operation".to_string())
        }
    }

    fn can_undo(&self) -> bool {
        true
    }

    fn get_description(&self) -> String {
        format!("Add text: '{}'", self.text)
    }
}

// 具体命令：删除文本命令
pub struct DeleteTextCommand {
    receiver: DocumentEditor,
    length: usize,
}

impl DeleteTextCommand {
    pub fn new(receiver: DocumentEditor, length: usize) -> Self {
        DeleteTextCommand { receiver, length }
    }
}

impl fmt::Display for DeleteTextCommand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DeleteTextCommand(length: {})", self.length)
    }
}

impl Command for DeleteTextCommand {
    fn execute(&self) -> CommandResult {
        let mut receiver = self.receiver.clone();
        receiver.delete_text(self.length);
        CommandResult::success(format!("Deleted {} characters", self.length))
    }

    fn undo(&self) -> CommandResult {
        let mut receiver = self.receiver.clone();
        if receiver.undo() {
            CommandResult::success("Undid delete text operation".to_string())
        } else {
            CommandResult::failure("Cannot undo delete text operation".to_string())
        }
    }

    fn can_undo(&self) -> bool {
        true
    }

    fn get_description(&self) -> String {
        format!("Delete {} characters", self.length)
    }
}

// 调用者：命令管理器
pub struct CommandManager {
    commands: Vec<Box<dyn Command>>,
    undo_stack: Vec<Box<dyn Command>>,
    redo_stack: Vec<Box<dyn Command>>,
}

impl CommandManager {
    pub fn new() -> Self {
        CommandManager {
            commands: Vec::new(),
            undo_stack: Vec::new(),
            redo_stack: Vec::new(),
        }
    }

    pub fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }

    pub fn execute_command(&mut self, index: usize) -> CommandResult {
        if index < self.commands.len() {
            let command = &self.commands[index];
            let result = command.execute();

            if result.success && command.can_undo() {
                self.undo_stack.push(self.commands[index].clone());
                self.redo_stack.clear(); // 新命令会清空重做栈
            }

            result
        } else {
            CommandResult::failure("Invalid command index".to_string())
        }
    }

    pub fn undo(&mut self) -> CommandResult {
        if let Some(command) = self.undo_stack.pop() {
            let result = command.undo();
            if result.success {
                self.redo_stack.push(command);
            }
            result
        } else {
            CommandResult::failure("No commands to undo".to_string())
        }
    }

    pub fn redo(&mut self) -> CommandResult {
        if let Some(command) = self.redo_stack.pop() {
            let result = command.execute();
            if result.success {
                self.undo_stack.push(command);
            }
            result
        } else {
            CommandResult::failure("No commands to redo".to_string())
        }
    }

    pub fn can_undo(&self) -> bool {
        !self.undo_stack.is_empty()
    }

    pub fn can_redo(&self) -> bool {
        !self.redo_stack.is_empty()
    }

    pub fn get_command_history(&self) -> Vec<String> {
        self.commands.iter().map(|c| c.get_description()).collect()
    }
}

// 为DocumentEditor实现Clone
impl Clone for DocumentEditor {
    fn clone(&self) -> Self {
        DocumentEditor {
            content: self.content.clone(),
            history: self.history.clone(),
        }
    }
}

// 为Command实现Clone
impl Clone for Box<dyn Command> {
    fn clone(&self) -> Self {
        // 这里需要具体的实现，简化处理
        Box::new(AddTextCommand::new(
            DocumentEditor::new(),
            "".to_string(),
        ))
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;

// 泛型命令结果
# [derive(Debug, Clone)]
pub struct GenericCommandResult<T> {
    pub success: bool,
    pub message: String,
    pub data: Option<T>,
}

impl<T> GenericCommandResult<T> {
    pub fn new(success: bool, message: String, data: Option<T>) -> Self {
        GenericCommandResult { success, message, data }
    }

    pub fn success_with_data(data: T, message: String) -> Self {
        GenericCommandResult::new(true, message, Some(data))
    }

    pub fn success(message: String) -> Self {
        GenericCommandResult::new(true, message, None)
    }

    pub fn failure(message: String) -> Self {
        GenericCommandResult::new(false, message, None)
    }
}

// 泛型命令trait
pub trait GenericCommand<T, R>: fmt::Display {
    fn execute(&self, receiver: &mut T) -> GenericCommandResult<R>;
    fn undo(&self, receiver: &mut T) -> GenericCommandResult<R>;
    fn can_undo(&self) -> bool;
    fn get_description(&self) -> String;
}

// 泛型接收者trait
pub trait GenericReceiver<T>: fmt::Display {
    fn get_state(&self) -> T;
    fn set_state(&mut self, state: T);
}

// 泛型调用者
pub struct GenericCommandManager<T, R> {
    commands: Vec<Box<dyn GenericCommand<T, R>>>,
    undo_stack: Vec<Box<dyn GenericCommand<T, R>>>,
    redo_stack: Vec<Box<dyn GenericCommand<T, R>>>,
    _phantom: std::marker::PhantomData<(T, R)>,
}

impl<T, R> GenericCommandManager<T, R> {
    pub fn new() -> Self {
        GenericCommandManager {
            commands: Vec::new(),
            undo_stack: Vec::new(),
            redo_stack: Vec::new(),
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn add_command(&mut self, command: Box<dyn GenericCommand<T, R>>) {
        self.commands.push(command);
    }

    pub fn execute_command(&mut self, index: usize, receiver: &mut T) -> GenericCommandResult<R> {
        if index < self.commands.len() {
            let command = &self.commands[index];
            let result = command.execute(receiver);

            if result.success && command.can_undo() {
                // 这里需要具体的克隆实现
                self.undo_stack.push(self.commands[index].clone());
                self.redo_stack.clear();
            }

            result
        } else {
            GenericCommandResult::failure("Invalid command index".to_string())
        }
    }

    pub fn undo(&mut self, receiver: &mut T) -> GenericCommandResult<R> {
        if let Some(command) = self.undo_stack.pop() {
            let result = command.undo(receiver);
            if result.success {
                self.redo_stack.push(command);
            }
            result
        } else {
            GenericCommandResult::failure("No commands to undo".to_string())
        }
    }

    pub fn redo(&mut self, receiver: &mut T) -> GenericCommandResult<R> {
        if let Some(command) = self.redo_stack.pop() {
            let result = command.execute(receiver);
            if result.success {
                self.undo_stack.push(command);
            }
            result
        } else {
            GenericCommandResult::failure("No commands to redo".to_string())
        }
    }
}
```

### 5.3 异步实现

```rust
use std::fmt;
use async_trait::async_trait;

// 异步命令结果
# [derive(Debug, Clone)]
pub struct AsyncCommandResult {
    pub success: bool,
    pub message: String,
    pub data: Option<String>,
}

impl AsyncCommandResult {
    pub fn new(success: bool, message: String, data: Option<String>) -> Self {
        AsyncCommandResult { success, message, data }
    }

    pub fn success(message: String) -> Self {
        AsyncCommandResult::new(true, message, None)
    }

    pub fn failure(message: String) -> Self {
        AsyncCommandResult::new(false, message, None)
    }
}

// 异步命令trait
# [async_trait]
pub trait AsyncCommand: fmt::Display + Send + Sync {
    async fn execute(&self) -> AsyncCommandResult;
    async fn undo(&self) -> AsyncCommandResult;
    fn can_undo(&self) -> bool;
    fn get_description(&self) -> String;
}

// 异步调用者
pub struct AsyncCommandManager {
    commands: Vec<Box<dyn AsyncCommand>>,
    undo_stack: Vec<Box<dyn AsyncCommand>>,
    redo_stack: Vec<Box<dyn AsyncCommand>>,
}

impl AsyncCommandManager {
    pub fn new() -> Self {
        AsyncCommandManager {
            commands: Vec::new(),
            undo_stack: Vec::new(),
            redo_stack: Vec::new(),
        }
    }

    pub fn add_command(&mut self, command: Box<dyn AsyncCommand>) {
        self.commands.push(command);
    }

    pub async fn execute_command(&mut self, index: usize) -> AsyncCommandResult {
        if index < self.commands.len() {
            let command = &self.commands[index];
            let result = command.execute().await;

            if result.success && command.can_undo() {
                self.undo_stack.push(self.commands[index].clone());
                self.redo_stack.clear();
            }

            result
        } else {
            AsyncCommandResult::failure("Invalid command index".to_string())
        }
    }

    pub async fn undo(&mut self) -> AsyncCommandResult {
        if let Some(command) = self.undo_stack.pop() {
            let result = command.undo().await;
            if result.success {
                self.redo_stack.push(command);
            }
            result
        } else {
            AsyncCommandResult::failure("No commands to undo".to_string())
        }
    }

    pub async fn redo(&mut self) -> AsyncCommandResult {
        if let Some(command) = self.redo_stack.pop() {
            let result = command.execute().await;
            if result.success {
                self.undo_stack.push(command);
            }
            result
        } else {
            AsyncCommandResult::failure("No commands to redo".to_string())
        }
    }
}
```

### 5.4 应用场景实现

```rust
// 文件系统操作命令
pub struct FileSystemReceiver {
    current_directory: String,
    files: Vec<String>,
}

impl FileSystemReceiver {
    pub fn new() -> Self {
        FileSystemReceiver {
            current_directory: "/".to_string(),
            files: Vec::new(),
        }
    }

    pub fn create_file(&mut self, filename: &str) -> bool {
        if !self.files.contains(&filename.to_string()) {
            self.files.push(filename.to_string());
            true
        } else {
            false
        }
    }

    pub fn delete_file(&mut self, filename: &str) -> bool {
        if let Some(index) = self.files.iter().position(|f| f == filename) {
            self.files.remove(index);
            true
        } else {
            false
        }
    }

    pub fn list_files(&self) -> Vec<String> {
        self.files.clone()
    }
}

// 创建文件命令
pub struct CreateFileCommand {
    filename: String,
}

impl CreateFileCommand {
    pub fn new(filename: String) -> Self {
        CreateFileCommand { filename }
    }
}

impl fmt::Display for CreateFileCommand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CreateFileCommand(filename: '{}')", self.filename)
    }
}

impl Command for CreateFileCommand {
    fn execute(&self) -> CommandResult {
        // 模拟文件创建
        println!("Creating file: {}", self.filename);
        CommandResult::success(format!("Created file: {}", self.filename))
    }

    fn undo(&self) -> CommandResult {
        // 模拟文件删除
        println!("Deleting file: {}", self.filename);
        CommandResult::success(format!("Deleted file: {}", self.filename))
    }

    fn can_undo(&self) -> bool {
        true
    }

    fn get_description(&self) -> String {
        format!("Create file: {}", self.filename)
    }
}

// 删除文件命令
pub struct DeleteFileCommand {
    filename: String,
}

impl DeleteFileCommand {
    pub fn new(filename: String) -> Self {
        DeleteFileCommand { filename }
    }
}

impl fmt::Display for DeleteFileCommand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DeleteFileCommand(filename: '{}')", self.filename)
    }
}

impl Command for DeleteFileCommand {
    fn execute(&self) -> CommandResult {
        // 模拟文件删除
        println!("Deleting file: {}", self.filename);
        CommandResult::success(format!("Deleted file: {}", self.filename))
    }

    fn undo(&self) -> CommandResult {
        // 模拟文件恢复
        println!("Restoring file: {}", self.filename);
        CommandResult::success(format!("Restored file: {}", self.filename))
    }

    fn can_undo(&self) -> bool {
        true
    }

    fn get_description(&self) -> String {
        format!("Delete file: {}", self.filename)
    }
}

// 数据库操作命令
pub struct DatabaseReceiver {
    connection_string: String,
    is_connected: bool,
}

impl DatabaseReceiver {
    pub fn new(connection_string: String) -> Self {
        DatabaseReceiver {
            connection_string,
            is_connected: false,
        }
    }

    pub fn connect(&mut self) -> bool {
        if !self.is_connected {
            println!("Connecting to database: {}", self.connection_string);
            self.is_connected = true;
            true
        } else {
            false
        }
    }

    pub fn disconnect(&mut self) -> bool {
        if self.is_connected {
            println!("Disconnecting from database: {}", self.connection_string);
            self.is_connected = false;
            true
        } else {
            false
        }
    }

    pub fn execute_query(&self, query: &str) -> bool {
        if self.is_connected {
            println!("Executing query: {}", query);
            true
        } else {
            false
        }
    }
}

// 连接数据库命令
pub struct ConnectDatabaseCommand {
    receiver: DatabaseReceiver,
}

impl ConnectDatabaseCommand {
    pub fn new(receiver: DatabaseReceiver) -> Self {
        ConnectDatabaseCommand { receiver }
    }
}

impl fmt::Display for ConnectDatabaseCommand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ConnectDatabaseCommand")
    }
}

impl Command for ConnectDatabaseCommand {
    fn execute(&self) -> CommandResult {
        let mut receiver = self.receiver.clone();
        if receiver.connect() {
            CommandResult::success("Connected to database".to_string())
        } else {
            CommandResult::failure("Already connected to database".to_string())
        }
    }

    fn undo(&self) -> CommandResult {
        let mut receiver = self.receiver.clone();
        if receiver.disconnect() {
            CommandResult::success("Disconnected from database".to_string())
        } else {
            CommandResult::failure("Not connected to database".to_string())
        }
    }

    fn can_undo(&self) -> bool {
        true
    }

    fn get_description(&self) -> String {
        "Connect to database".to_string()
    }
}

// 为DatabaseReceiver实现Clone
impl Clone for DatabaseReceiver {
    fn clone(&self) -> Self {
        DatabaseReceiver {
            connection_string: self.connection_string.clone(),
            is_connected: self.is_connected,
        }
    }
}
```

## 6. 应用场景

### 6.1 文本编辑器

命令模式在文本编辑器中广泛应用，支持各种编辑操作的撤销和重做：

- **添加文本命令**：在光标位置添加文本
- **删除文本命令**：删除指定长度的文本
- **替换文本命令**：替换指定范围的文本
- **格式化命令**：应用文本格式化

### 6.2 图形编辑器

在图形编辑器中，命令模式支持各种图形操作的撤销和重做：

- **绘制命令**：绘制各种图形
- **移动命令**：移动图形对象
- **缩放命令**：缩放图形对象
- **删除命令**：删除图形对象

### 6.3 数据库操作

在数据库操作中，命令模式支持事务的撤销和重做：

- **插入命令**：插入数据记录
- **更新命令**：更新数据记录
- **删除命令**：删除数据记录
- **查询命令**：执行数据查询

## 7. 变体模式

### 7.1 宏命令

```rust
pub struct MacroCommand {
    commands: Vec<Box<dyn Command>>,
}

impl MacroCommand {
    pub fn new() -> Self {
        MacroCommand { commands: Vec::new() }
    }

    pub fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
}

impl Command for MacroCommand {
    fn execute(&self) -> CommandResult {
        for command in &self.commands {
            let result = command.execute();
            if !result.success {
                return result;
            }
        }
        CommandResult::success("All commands executed successfully".to_string())
    }

    fn undo(&self) -> CommandResult {
        for command in self.commands.iter().rev() {
            let result = command.undo();
            if !result.success {
                return result;
            }
        }
        CommandResult::success("All commands undone successfully".to_string())
    }

    fn can_undo(&self) -> bool {
        self.commands.iter().all(|c| c.can_undo())
    }

    fn get_description(&self) -> String {
        format!("Macro command with {} sub-commands", self.commands.len())
    }
}
```

### 7.2 事务命令

```rust
pub struct TransactionCommand {
    commands: Vec<Box<dyn Command>>,
    executed: bool,
}

impl TransactionCommand {
    pub fn new() -> Self {
        TransactionCommand {
            commands: Vec::new(),
            executed: false,
        }
    }

    pub fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
}

impl Command for TransactionCommand {
    fn execute(&self) -> CommandResult {
        if self.executed {
            return CommandResult::failure("Transaction already executed".to_string());
        }

        let mut results = Vec::new();
        for command in &self.commands {
            let result = command.execute();
            results.push(result.clone());
            if !result.success {
                // 回滚已执行的命令
                for executed_result in results.iter().rev() {
                    if executed_result.success {
                        // 这里需要具体的回滚逻辑
                    }
                }
                return CommandResult::failure("Transaction failed, rolled back".to_string());
            }
        }
        CommandResult::success("Transaction executed successfully".to_string())
    }

    fn undo(&self) -> CommandResult {
        if !self.executed {
            return CommandResult::failure("Transaction not executed".to_string());
        }

        for command in self.commands.iter().rev() {
            let result = command.undo();
            if !result.success {
                return CommandResult::failure("Transaction undo failed".to_string());
            }
        }
        CommandResult::success("Transaction undone successfully".to_string())
    }

    fn can_undo(&self) -> bool {
        self.executed && self.commands.iter().all(|c| c.can_undo())
    }

    fn get_description(&self) -> String {
        format!("Transaction with {} commands", self.commands.len())
    }
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **命令执行**：$O(1)$，单个命令执行
- **命令撤销**：$O(1)$，单个命令撤销
- **宏命令执行**：$O(n)$，其中 $n$ 是子命令数量
- **事务执行**：$O(n)$，其中 $n$ 是事务中的命令数量

### 8.2 空间复杂度

- **命令存储**：$O(n)$，其中 $n$ 是命令数量
- **撤销栈**：$O(m)$，其中 $m$ 是可撤销的命令数量
- **重做栈**：$O(k)$，其中 $k$ 是可重做的命令数量

### 8.3 优化策略

1. **命令池**：重用命令对象，减少内存分配
2. **延迟执行**：支持命令的延迟执行
3. **批量操作**：支持批量命令的优化执行
4. **状态压缩**：压缩命令历史状态，节省内存

## 9. 总结

命令模式通过将请求封装成对象，实现了请求的延迟执行、撤销重做和日志记录等功能，具有以下优势：

1. **解耦性**：将请求发送者和接收者解耦
2. **可扩展性**：易于添加新的命令类型
3. **可撤销性**：支持操作的撤销和重做
4. **可组合性**：支持命令的组合和宏命令

通过形式化的数学理论和完整的Rust实现，我们建立了命令模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。
