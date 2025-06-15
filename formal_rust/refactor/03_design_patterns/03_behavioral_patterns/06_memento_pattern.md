# 备忘录模式 (Memento Pattern) - 形式化重构

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

备忘录模式是一种行为型设计模式，它允许在不破坏封装的前提下，捕获并外部化对象的内部状态，以便以后可以将对象恢复到这个状态。

### 1.2 模式特征

- **状态保存**：能够保存对象的内部状态
- **状态恢复**：能够将对象恢复到之前的状态
- **封装保护**：不破坏对象的封装性
- **历史管理**：支持多个历史状态的保存

## 2. 形式化定义

### 2.1 备忘录模式五元组

**定义2.1 (备忘录模式五元组)**
设 $M = (O, S, H, R, T)$ 为一个备忘录模式，其中：

- $O = \{o_1, o_2, ..., o_n\}$ 是原发器对象集合
- $S = \{s_1, s_2, ..., s_m\}$ 是状态集合
- $H = \{h_1, h_2, ..., h_k\}$ 是历史记录集合
- $R = \{r_1, r_2, ..., r_l\}$ 是恢复操作集合
- $T = \{t_1, t_2, ..., t_p\}$ 是时间戳集合

### 2.2 备忘录接口定义

**定义2.2 (备忘录接口)**
备忘录接口 $I_{mem}$ 定义为：

$$I_{mem} = \{\text{getState}() \rightarrow S, \text{setState}(s: S) \rightarrow \text{void}\}$$

### 2.3 原发器接口定义

**定义2.3 (原发器接口)**
原发器接口 $I_{ori}$ 定义为：

$$I_{ori} = \{\text{createMemento}() \rightarrow M, \text{restore}(m: M) \rightarrow \text{void}\}$$

### 2.4 状态转换函数

**定义2.4 (状态转换函数)**
状态转换函数 $f_S: O \times S \rightarrow O'$ 定义为：

$$f_S(o, s) = o' \text{ where } o' \text{ has state } s$$

## 3. 数学理论

### 3.1 状态一致性理论

**定义3.1 (状态一致性)**
备忘录 $M$ 与原发器 $O$ 的状态是一致的，当且仅当：

$$\text{getState}(M) = \text{getState}(O)$$

### 3.2 状态恢复理论

**定义3.2 (状态恢复)**
原发器 $O$ 从备忘录 $M$ 恢复状态，当且仅当：

$$\text{restore}(O, M) \Rightarrow \text{getState}(O) = \text{getState}(M)$$

### 3.3 历史完整性理论

**定义3.3 (历史完整性)**
历史记录 $H$ 是完整的，当且仅当：

$$\forall s \in S, \exists h \in H: \text{getState}(h) = s$$

### 3.4 状态转换理论

**定义3.4 (状态转换)**
状态转换序列 $T_S = (s_1, s_2, ..., s_n)$ 是有效的，当且仅当：

$$\forall i \in [1, n-1]: \text{isValidTransition}(s_i, s_{i+1})$$

## 4. 核心定理

### 4.1 状态保存定理

**定理4.1 (状态保存)**
如果备忘录 $M$ 是从原发器 $O$ 创建的，则状态一致性成立：

$$\text{createMemento}(O) = M \Rightarrow \text{getState}(M) = \text{getState}(O)$$

**证明：**

1. 根据定义2.3，`createMemento()` 方法保存当前状态
2. 根据定义3.1，备忘录状态与原发器状态一致
3. 状态保存定理得证。

### 4.2 状态恢复定理

**定理4.2 (状态恢复)**
如果原发器 $O$ 从备忘录 $M$ 恢复状态，则状态一致性成立：

$$\text{restore}(O, M) \Rightarrow \text{getState}(O) = \text{getState}(M)$$

**证明：**

1. 根据定义2.3，`restore()` 方法恢复备忘录状态
2. 根据定义3.2，恢复后状态一致
3. 状态恢复定理得证。

### 4.3 历史完整性定理

**定理4.3 (历史完整性)**
如果历史记录 $H$ 包含所有保存的状态，则历史完整性成立：

$$\forall s \in S: \text{saved}(s) \Rightarrow \exists h \in H: \text{getState}(h) = s$$

**证明：**

1. 根据定义3.3，历史记录包含所有保存的状态
2. 每次保存操作都会添加到历史记录
3. 历史完整性定理得证。

### 4.4 状态转换安全性定理

**定理4.4 (状态转换安全性)**
如果状态转换序列 $T_S$ 是有效的，则转换过程是安全的：

$$\text{isValidSequence}(T_S) \Rightarrow \forall i: \text{isValidState}(s_i)$$

**证明：**

1. 根据定义3.4，有效转换序列满足转换约束
2. 每个状态转换都是有效的
3. 状态转换安全性定理得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;
use std::collections::HashMap;

// 备忘录trait
pub trait Memento: fmt::Display {
    fn get_state(&self) -> String;
    fn set_state(&mut self, state: String);
}

// 原发器trait
pub trait Originator: fmt::Display {
    fn create_memento(&self) -> Box<dyn Memento>;
    fn restore(&mut self, memento: &dyn Memento);
    fn get_state(&self) -> String;
    fn set_state(&mut self, state: String);
}

// 具体备忘录：文本编辑器备忘录
pub struct TextEditorMemento {
    content: String,
    cursor_position: usize,
    selection_start: Option<usize>,
    selection_end: Option<usize>,
}

impl TextEditorMemento {
    pub fn new(content: String, cursor_position: usize, 
               selection_start: Option<usize>, selection_end: Option<usize>) -> Self {
        TextEditorMemento {
            content,
            cursor_position,
            selection_start,
            selection_end,
        }
    }
}

impl fmt::Display for TextEditorMemento {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TextEditorMemento(content: '{}', cursor: {})", 
               self.content, self.cursor_position)
    }
}

impl Memento for TextEditorMemento {
    fn get_state(&self) -> String {
        format!("{}|{}|{}|{}", 
                self.content,
                self.cursor_position,
                self.selection_start.unwrap_or(0),
                self.selection_end.unwrap_or(0))
    }

    fn set_state(&mut self, state: String) {
        let parts: Vec<&str> = state.split('|').collect();
        if parts.len() >= 4 {
            self.content = parts[0].to_string();
            self.cursor_position = parts[1].parse().unwrap_or(0);
            self.selection_start = parts[2].parse().ok();
            self.selection_end = parts[3].parse().ok();
        }
    }
}

// 具体原发器：文本编辑器
pub struct TextEditor {
    content: String,
    cursor_position: usize,
    selection_start: Option<usize>,
    selection_end: Option<usize>,
    history: Vec<Box<dyn Memento>>,
    current_index: isize,
}

impl TextEditor {
    pub fn new() -> Self {
        TextEditor {
            content: String::new(),
            cursor_position: 0,
            selection_start: None,
            selection_end: None,
            history: Vec::new(),
            current_index: -1,
        }
    }

    pub fn insert_text(&mut self, text: &str) {
        self.save_state();
        self.content.insert_str(self.cursor_position, text);
        self.cursor_position += text.len();
    }

    pub fn delete_text(&mut self, length: usize) {
        self.save_state();
        if self.cursor_position >= length {
            self.content.drain((self.cursor_position - length)..self.cursor_position);
            self.cursor_position -= length;
        }
    }

    pub fn move_cursor(&mut self, position: usize) {
        if position <= self.content.len() {
            self.cursor_position = position;
        }
    }

    pub fn select_text(&mut self, start: usize, end: usize) {
        if start <= end && end <= self.content.len() {
            self.selection_start = Some(start);
            self.selection_end = Some(end);
        }
    }

    pub fn get_content(&self) -> &str {
        &self.content
    }

    pub fn get_cursor_position(&self) -> usize {
        self.cursor_position
    }

    pub fn can_undo(&self) -> bool {
        self.current_index >= 0
    }

    pub fn can_redo(&self) -> bool {
        self.current_index < (self.history.len() as isize) - 1
    }

    fn save_state(&mut self) {
        // 移除当前索引之后的历史记录
        if self.current_index >= 0 {
            self.history.truncate((self.current_index + 1) as usize);
        }
        
        let memento = self.create_memento();
        self.history.push(memento);
        self.current_index = self.history.len() as isize - 1;
    }
}

impl fmt::Display for TextEditor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TextEditor(content: '{}', cursor: {})", 
               self.content, self.cursor_position)
    }
}

impl Originator for TextEditor {
    fn create_memento(&self) -> Box<dyn Memento> {
        Box::new(TextEditorMemento::new(
            self.content.clone(),
            self.cursor_position,
            self.selection_start,
            self.selection_end,
        ))
    }

    fn restore(&mut self, memento: &dyn Memento) {
        let state = memento.get_state();
        let parts: Vec<&str> = state.split('|').collect();
        if parts.len() >= 4 {
            self.content = parts[0].to_string();
            self.cursor_position = parts[1].parse().unwrap_or(0);
            self.selection_start = parts[2].parse().ok();
            self.selection_end = parts[3].parse().ok();
        }
    }

    fn get_state(&self) -> String {
        format!("{}|{}|{}|{}", 
                self.content,
                self.cursor_position,
                self.selection_start.unwrap_or(0),
                self.selection_end.unwrap_or(0))
    }

    fn set_state(&mut self, state: String) {
        let parts: Vec<&str> = state.split('|').collect();
        if parts.len() >= 4 {
            self.content = parts[0].to_string();
            self.cursor_position = parts[1].parse().unwrap_or(0);
            self.selection_start = parts[2].parse().ok();
            self.selection_end = parts[3].parse().ok();
        }
    }
}

// 管理者：历史管理器
pub struct HistoryManager {
    originator: TextEditor,
    max_history_size: usize,
}

impl HistoryManager {
    pub fn new(originator: TextEditor, max_history_size: usize) -> Self {
        HistoryManager {
            originator,
            max_history_size,
        }
    }

    pub fn save_state(&mut self) {
        let memento = self.originator.create_memento();
        
        // 限制历史记录大小
        if self.originator.history.len() >= self.max_history_size {
            self.originator.history.remove(0);
            self.originator.current_index -= 1;
        }
        
        self.originator.history.push(memento);
        self.originator.current_index = self.originator.history.len() as isize - 1;
    }

    pub fn undo(&mut self) -> bool {
        if self.originator.can_undo() {
            self.originator.current_index -= 1;
            if let Some(memento) = self.originator.history.get(self.originator.current_index as usize) {
                self.originator.restore(memento.as_ref());
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn redo(&mut self) -> bool {
        if self.originator.can_redo() {
            self.originator.current_index += 1;
            if let Some(memento) = self.originator.history.get(self.originator.current_index as usize) {
                self.originator.restore(memento.as_ref());
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn get_originator(&self) -> &TextEditor {
        &self.originator
    }

    pub fn get_originator_mut(&mut self) -> &mut TextEditor {
        &mut self.originator
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;
use serde::{Serialize, Deserialize};

// 泛型备忘录trait
pub trait GenericMemento<T>: fmt::Display {
    fn get_state(&self) -> T;
    fn set_state(&mut self, state: T);
}

// 泛型原发器trait
pub trait GenericOriginator<T>: fmt::Display {
    fn create_memento(&self) -> Box<dyn GenericMemento<T>>;
    fn restore(&mut self, memento: &dyn GenericMemento<T>);
    fn get_state(&self) -> T;
    fn set_state(&mut self, state: T);
}

// 可序列化备忘录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializableMemento<T> {
    state: T,
    timestamp: u64,
}

impl<T> SerializableMemento<T> {
    pub fn new(state: T, timestamp: u64) -> Self {
        SerializableMemento { state, timestamp }
    }

    pub fn get_timestamp(&self) -> u64 {
        self.timestamp
    }
}

impl<T: fmt::Display> fmt::Display for SerializableMemento<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SerializableMemento(state: {}, timestamp: {})", 
               self.state, self.timestamp)
    }
}

impl<T: Clone> GenericMemento<T> for SerializableMemento<T> {
    fn get_state(&self) -> T {
        self.state.clone()
    }

    fn set_state(&mut self, state: T) {
        self.state = state;
    }
}

// 游戏状态备忘录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameState {
    player_position: (f32, f32),
    player_health: i32,
    score: u32,
    level: u32,
    inventory: Vec<String>,
}

impl GameState {
    pub fn new() -> Self {
        GameState {
            player_position: (0.0, 0.0),
            player_health: 100,
            score: 0,
            level: 1,
            inventory: Vec::new(),
        }
    }

    pub fn move_player(&mut self, dx: f32, dy: f32) {
        self.player_position.0 += dx;
        self.player_position.1 += dy;
    }

    pub fn take_damage(&mut self, damage: i32) {
        self.player_health -= damage;
        if self.player_health < 0 {
            self.player_health = 0;
        }
    }

    pub fn heal(&mut self, amount: i32) {
        self.player_health += amount;
        if self.player_health > 100 {
            self.player_health = 100;
        }
    }

    pub fn add_score(&mut self, points: u32) {
        self.score += points;
    }

    pub fn level_up(&mut self) {
        self.level += 1;
    }

    pub fn add_item(&mut self, item: String) {
        self.inventory.push(item);
    }

    pub fn remove_item(&mut self, item: &str) -> bool {
        if let Some(index) = self.inventory.iter().position(|i| i == item) {
            self.inventory.remove(index);
            true
        } else {
            false
        }
    }
}

impl fmt::Display for GameState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GameState(pos: ({:.1}, {:.1}), health: {}, score: {}, level: {})", 
               self.player_position.0, self.player_position.1,
               self.player_health, self.score, self.level)
    }
}

// 游戏原发器
pub struct Game {
    state: GameState,
    history: Vec<Box<dyn GenericMemento<GameState>>>,
    current_index: isize,
}

impl Game {
    pub fn new() -> Self {
        Game {
            state: GameState::new(),
            history: Vec::new(),
            current_index: -1,
        }
    }

    pub fn save_checkpoint(&mut self) {
        let memento = self.create_memento();
        self.history.push(memento);
        self.current_index = self.history.len() as isize - 1;
    }

    pub fn load_checkpoint(&mut self, index: usize) -> bool {
        if index < self.history.len() {
            self.current_index = index as isize;
            if let Some(memento) = self.history.get(index) {
                self.restore(memento.as_ref());
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn get_state(&self) -> &GameState {
        &self.state
    }

    pub fn get_state_mut(&mut self) -> &mut GameState {
        &mut self.state
    }

    pub fn can_undo(&self) -> bool {
        self.current_index >= 0
    }

    pub fn can_redo(&self) -> bool {
        self.current_index < (self.history.len() as isize) - 1
    }
}

impl fmt::Display for Game {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Game({})", self.state)
    }
}

impl GenericOriginator<GameState> for Game {
    fn create_memento(&self) -> Box<dyn GenericMemento<GameState>> {
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        Box::new(SerializableMemento::new(self.state.clone(), timestamp))
    }

    fn restore(&mut self, memento: &dyn GenericMemento<GameState>) {
        self.state = memento.get_state();
    }

    fn get_state(&self) -> GameState {
        self.state.clone()
    }

    fn set_state(&mut self, state: GameState) {
        self.state = state;
    }
}
```

### 5.3 应用场景实现

```rust
// 数据库事务备忘录
pub struct DatabaseTransaction {
    connection_string: String,
    queries: Vec<String>,
    results: Vec<String>,
    is_committed: bool,
}

impl DatabaseTransaction {
    pub fn new(connection_string: String) -> Self {
        DatabaseTransaction {
            connection_string,
            queries: Vec::new(),
            results: Vec::new(),
            is_committed: false,
        }
    }

    pub fn add_query(&mut self, query: String) {
        self.queries.push(query);
    }

    pub fn execute_query(&mut self, query: &str) -> String {
        // 模拟查询执行
        let result = format!("Result for: {}", query);
        self.results.push(result.clone());
        result
    }

    pub fn commit(&mut self) -> bool {
        if !self.is_committed {
            println!("Committing transaction with {} queries", self.queries.len());
            self.is_committed = true;
            true
        } else {
            false
        }
    }

    pub fn rollback(&mut self) -> bool {
        if self.is_committed {
            println!("Rolling back transaction");
            self.is_committed = false;
            self.results.clear();
            true
        } else {
            false
        }
    }
}

// 数据库事务备忘录
pub struct TransactionMemento {
    queries: Vec<String>,
    results: Vec<String>,
    is_committed: bool,
}

impl TransactionMemento {
    pub fn new(queries: Vec<String>, results: Vec<String>, is_committed: bool) -> Self {
        TransactionMemento {
            queries,
            results,
            is_committed,
        }
    }
}

impl fmt::Display for TransactionMemento {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TransactionMemento(queries: {}, committed: {})", 
               self.queries.len(), self.is_committed)
    }
}

impl Memento for TransactionMemento {
    fn get_state(&self) -> String {
        format!("{}|{}|{}", 
                self.queries.join(","),
                self.results.join(","),
                self.is_committed)
    }

    fn set_state(&mut self, state: String) {
        let parts: Vec<&str> = state.split('|').collect();
        if parts.len() >= 3 {
            self.queries = parts[0].split(',').map(|s| s.to_string()).collect();
            self.results = parts[1].split(',').map(|s| s.to_string()).collect();
            self.is_committed = parts[2].parse().unwrap_or(false);
        }
    }
}

impl Originator for DatabaseTransaction {
    fn create_memento(&self) -> Box<dyn Memento> {
        Box::new(TransactionMemento::new(
            self.queries.clone(),
            self.results.clone(),
            self.is_committed,
        ))
    }

    fn restore(&mut self, memento: &dyn Memento) {
        let state = memento.get_state();
        let parts: Vec<&str> = state.split('|').collect();
        if parts.len() >= 3 {
            self.queries = parts[0].split(',').map(|s| s.to_string()).collect();
            self.results = parts[1].split(',').map(|s| s.to_string()).collect();
            self.is_committed = parts[2].parse().unwrap_or(false);
        }
    }

    fn get_state(&self) -> String {
        format!("{}|{}|{}", 
                self.queries.join(","),
                self.results.join(","),
                self.is_committed)
    }

    fn set_state(&mut self, state: String) {
        let parts: Vec<&str> = state.split('|').collect();
        if parts.len() >= 3 {
            self.queries = parts[0].split(',').map(|s| s.to_string()).collect();
            self.results = parts[1].split(',').map(|s| s.to_string()).collect();
            self.is_committed = parts[2].parse().unwrap_or(false);
        }
    }
}

impl fmt::Display for DatabaseTransaction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DatabaseTransaction(queries: {}, committed: {})", 
               self.queries.len(), self.is_committed)
    }
}
```

## 6. 应用场景

### 6.1 文本编辑器

备忘录模式在文本编辑器中广泛应用，支持撤销和重做功能：

- **文本编辑**：保存编辑历史，支持撤销重做
- **光标位置**：保存光标位置和选择状态
- **格式化操作**：保存格式化历史
- **查找替换**：保存查找替换历史

### 6.2 游戏开发

在游戏开发中，备忘录模式用于保存游戏状态：

- **检查点系统**：保存游戏进度
- **回放系统**：记录游戏操作历史
- **状态回滚**：支持状态回滚到之前的时间点
- **多人游戏**：同步游戏状态

### 6.3 数据库事务

在数据库事务中，备忘录模式用于事务管理：

- **事务保存点**：创建事务保存点
- **事务回滚**：回滚到保存点
- **事务恢复**：从保存点恢复
- **事务历史**：记录事务历史

## 7. 变体模式

### 7.1 增量备忘录

```rust
pub struct IncrementalMemento {
    base_state: String,
    changes: Vec<Change>,
}

#[derive(Debug, Clone)]
pub struct Change {
    operation: String,
    position: usize,
    old_value: String,
    new_value: String,
}

impl IncrementalMemento {
    pub fn new(base_state: String) -> Self {
        IncrementalMemento {
            base_state,
            changes: Vec::new(),
        }
    }

    pub fn add_change(&mut self, change: Change) {
        self.changes.push(change);
    }

    pub fn apply_changes(&self) -> String {
        let mut state = self.base_state.clone();
        for change in &self.changes {
            match change.operation.as_str() {
                "insert" => {
                    if change.position <= state.len() {
                        state.insert_str(change.position, &change.new_value);
                    }
                }
                "delete" => {
                    if change.position + change.old_value.len() <= state.len() {
                        state.drain(change.position..(change.position + change.old_value.len()));
                    }
                }
                "replace" => {
                    if change.position + change.old_value.len() <= state.len() {
                        state.drain(change.position..(change.position + change.old_value.len()));
                        state.insert_str(change.position, &change.new_value);
                    }
                }
                _ => {}
            }
        }
        state
    }
}
```

### 7.2 压缩备忘录

```rust
use std::collections::HashMap;

pub struct CompressedMemento {
    state_map: HashMap<String, String>,
    compression_ratio: f32,
}

impl CompressedMemento {
    pub fn new() -> Self {
        CompressedMemento {
            state_map: HashMap::new(),
            compression_ratio: 0.0,
        }
    }

    pub fn compress_state(&mut self, state: String) -> String {
        // 简单的压缩算法：重复字符串替换
        let mut compressed = state.clone();
        let mut replacements = HashMap::new();
        let mut counter = 0;

        // 查找重复的子字符串
        for len in (3..=10).rev() {
            for i in 0..=state.len() - len {
                let substring = &state[i..i + len];
                if state.matches(substring).count() > 1 {
                    let key = format!("@{}", counter);
                    compressed = compressed.replace(substring, &key);
                    replacements.insert(key, substring.to_string());
                    counter += 1;
                }
            }
        }

        // 存储替换映射
        for (key, value) in replacements {
            self.state_map.insert(key, value);
        }

        self.compression_ratio = compressed.len() as f32 / state.len() as f32;
        compressed
    }

    pub fn decompress_state(&self, compressed: String) -> String {
        let mut decompressed = compressed;
        for (key, value) in &self.state_map {
            decompressed = decompressed.replace(key, value);
        }
        decompressed
    }

    pub fn get_compression_ratio(&self) -> f32 {
        self.compression_ratio
    }
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **状态保存**：$O(1)$，创建备忘录对象
- **状态恢复**：$O(1)$，从备忘录恢复状态
- **历史管理**：$O(n)$，其中 $n$ 是历史记录数量
- **状态压缩**：$O(m^2)$，其中 $m$ 是状态大小

### 8.2 空间复杂度

- **备忘录存储**：$O(s)$，其中 $s$ 是状态大小
- **历史记录**：$O(n \cdot s)$，其中 $n$ 是历史记录数量
- **增量存储**：$O(c)$，其中 $c$ 是变更数量
- **压缩存储**：$O(s \cdot r)$，其中 $r$ 是压缩比

### 8.3 优化策略

1. **增量保存**：只保存状态变更
2. **压缩存储**：压缩备忘录数据
3. **历史限制**：限制历史记录数量
4. **延迟保存**：延迟保存不重要的状态

## 9. 总结

备忘录模式通过保存和恢复对象状态，实现了撤销重做和历史管理功能，具有以下优势：

1. **状态保护**：不破坏对象的封装性
2. **历史管理**：支持多个历史状态
3. **撤销重做**：支持操作的撤销和重做
4. **状态恢复**：支持任意时间点的状态恢复

通过形式化的数学理论和完整的Rust实现，我们建立了备忘录模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。
