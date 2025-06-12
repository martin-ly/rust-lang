# 组合模式 (Composite Pattern) - 形式化重构

## 1. 形式化定义 (Formal Definition)

### 1.1 组合模式五元组

设组合模式 $C = (N, I, S, R, C)$，其中：

- $N = \{\text{Composite Pattern}\}$ - 模式名称
- $I = \{\text{将对象组合成树形结构以表示"部分-整体"的层次结构}\}$ - 意图
- $S = \{\text{Component}, \text{Leaf}, \text{Composite}\}$ - 结构组件
- $R = \{\text{继承关系}, \text{组合关系}, \text{聚合关系}\}$ - 关系映射
- $C = \{\text{类型安全}, \text{递归结构}, \text{统一接口}\}$ - 约束条件

### 1.2 数学理论 (Mathematical Theory)

#### 1.2.1 树形结构理论 (Tree Structure Theory)

**定义1.1 (树形结构)**
设 $T = (V, E)$ 为一个有向树，其中：
- $V$ 是节点集合，$V = \{\text{Component}, \text{Leaf}, \text{Composite}\}$
- $E$ 是边集合，表示继承和组合关系

**定义1.2 (递归结构)**
对于任意节点 $v \in V$，其子树 $T_v$ 定义为：
$$T_v = \{v\} \cup \bigcup_{u \in \text{children}(v)} T_u$$

#### 1.2.2 统一接口理论 (Unified Interface Theory)

**定义1.3 (统一接口)**
设 $I$ 为接口集合，对于任意组件 $c \in \text{Component}$：
$$\forall i \in I, c \text{ implements } i$$

#### 1.2.3 递归操作理论 (Recursive Operation Theory)

**定义1.4 (递归操作)**
对于任意操作 $op$ 和组件 $c$：
$$op(c) = \begin{cases}
\text{leaf\_operation}(c) & \text{if } c \text{ is Leaf} \\
\text{composite\_operation}(c) \circ \bigcirc_{child \in \text{children}(c)} op(child) & \text{if } c \text{ is Composite}
\end{cases}$$

## 2. 核心定理 (Core Theorems)

### 2.1 结构完整性定理

**定理2.1.1 (结构完整性)**
组合模式保证树形结构的完整性：
$$\forall c \in \text{Composite}, \text{children}(c) \subseteq \text{Component}$$

**证明：**
1. 根据定义，Composite 继承自 Component
2. 根据组合关系，children 必须是 Component 类型
3. 因此 $\text{children}(c) \subseteq \text{Component}$ 成立

### 2.2 递归操作正确性定理

**定理2.2.1 (递归操作正确性)**
对于任意递归操作 $op$，如果满足：
1. 基础情况：对于 Leaf 节点，$op$ 正确执行
2. 递归情况：对于 Composite 节点，$op$ 正确组合子操作

则 $op$ 在整个树形结构上正确执行。

**证明：**
使用数学归纳法：
- **基础情况**：对于叶子节点，操作直接执行
- **归纳假设**：假设对于深度为 $k$ 的子树，操作正确执行
- **归纳步骤**：对于深度为 $k+1$ 的节点，操作正确组合子操作

### 2.3 类型安全定理

**定理2.3.1 (类型安全)**
组合模式保证类型安全：
$$\forall c_1, c_2 \in \text{Component}, \text{type}(c_1) = \text{type}(c_2) \Rightarrow \text{compatible}(c_1, c_2)$$

### 2.4 性能复杂度定理

**定理2.4.1 (遍历复杂度)**
对于包含 $n$ 个节点的树形结构，遍历操作的复杂度为：
$$\text{Complexity}(op) = O(n)$$

**定理2.4.2 (内存复杂度)**
组合模式的内存复杂度为：
$$\text{Memory}(C) = O(n)$$

## 3. Rust 实现 (Rust Implementation)

### 3.1 基础实现

```rust
use std::collections::HashMap;

// 组件接口
trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>);
    fn remove(&mut self, component: &str);
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>>;
    fn get_children(&self) -> Vec<&Box<dyn Component>>;
}

// 叶子节点
struct Leaf {
    name: String,
    value: String,
}

impl Leaf {
    fn new(name: String, value: String) -> Self {
        Leaf { name, value }
    }
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf[{}]: {}", self.name, self.value)
    }

    fn add(&mut self, _component: Box<dyn Component>) {
        // 叶子节点不支持添加子组件
    }

    fn remove(&mut self, _name: &str) {
        // 叶子节点不支持删除子组件
    }

    fn get_child(&self, _name: &str) -> Option<&Box<dyn Component>> {
        None
    }

    fn get_children(&self) -> Vec<&Box<dyn Component>> {
        Vec::new()
    }
}

// 复合节点
struct Composite {
    name: String,
    children: HashMap<String, Box<dyn Component>>,
}

impl Composite {
    fn new(name: String) -> Self {
        Composite {
            name,
            children: HashMap::new(),
        }
    }
}

impl Component for Composite {
    fn operation(&self) -> String {
        let mut result = format!("Composite[{}]: ", self.name);
        for child in self.children.values() {
            result.push_str(&format!("({})", child.operation()));
        }
        result
    }

    fn add(&mut self, component: Box<dyn Component>) {
        // 这里需要获取组件名称，简化实现
        let name = format!("child_{}", self.children.len());
        self.children.insert(name, component);
    }

    fn remove(&mut self, name: &str) {
        self.children.remove(name);
    }

    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>> {
        self.children.get(name)
    }

    fn get_children(&self) -> Vec<&Box<dyn Component>> {
        self.children.values().collect()
    }
}
```

### 3.2 泛型实现

```rust
use std::collections::HashMap;

// 泛型组件接口
trait GenericComponent<T> {
    fn operation(&self) -> T;
    fn add(&mut self, component: Box<dyn GenericComponent<T>>);
    fn remove(&mut self, name: &str);
    fn get_child(&self, name: &str) -> Option<&Box<dyn GenericComponent<T>>>;
    fn get_children(&self) -> Vec<&Box<dyn GenericComponent<T>>>;
}

// 泛型叶子节点
struct GenericLeaf<T> {
    name: String,
    value: T,
}

impl<T> GenericLeaf<T> {
    fn new(name: String, value: T) -> Self {
        GenericLeaf { name, value }
    }
}

impl<T: Clone + std::fmt::Display> GenericComponent<T> for GenericLeaf<T> {
    fn operation(&self) -> T {
        self.value.clone()
    }

    fn add(&mut self, _component: Box<dyn GenericComponent<T>>) {
        // 叶子节点不支持添加子组件
    }

    fn remove(&mut self, _name: &str) {
        // 叶子节点不支持删除子组件
    }

    fn get_child(&self, _name: &str) -> Option<&Box<dyn GenericComponent<T>>> {
        None
    }

    fn get_children(&self) -> Vec<&Box<dyn GenericComponent<T>>> {
        Vec::new()
    }
}

// 泛型复合节点
struct GenericComposite<T> {
    name: String,
    children: HashMap<String, Box<dyn GenericComponent<T>>>,
    combine_fn: fn(Vec<T>) -> T,
}

impl<T> GenericComposite<T> {
    fn new(name: String, combine_fn: fn(Vec<T>) -> T) -> Self {
        GenericComposite {
            name,
            children: HashMap::new(),
            combine_fn,
        }
    }
}

impl<T: Clone> GenericComponent<T> for GenericComposite<T> {
    fn operation(&self) -> T {
        let values: Vec<T> = self.children.values()
            .map(|child| child.operation())
            .collect();
        (self.combine_fn)(values)
    }

    fn add(&mut self, component: Box<dyn GenericComponent<T>>) {
        let name = format!("child_{}", self.children.len());
        self.children.insert(name, component);
    }

    fn remove(&mut self, name: &str) {
        self.children.remove(name);
    }

    fn get_child(&self, name: &str) -> Option<&Box<dyn GenericComponent<T>>> {
        self.children.get(name)
    }

    fn get_children(&self) -> Vec<&Box<dyn GenericComponent<T>>> {
        self.children.values().collect()
    }
}
```

### 3.3 异步实现

```rust
use std::collections::HashMap;
use async_trait::async_trait;

#[async_trait]
trait AsyncComponent {
    async fn operation(&self) -> String;
    async fn add(&mut self, component: Box<dyn AsyncComponent + Send>);
    async fn remove(&mut self, name: &str);
    async fn get_child(&self, name: &str) -> Option<&Box<dyn AsyncComponent + Send>>;
    async fn get_children(&self) -> Vec<&Box<dyn AsyncComponent + Send>>;
}

struct AsyncLeaf {
    name: String,
    value: String,
}

#[async_trait]
impl AsyncComponent for AsyncLeaf {
    async fn operation(&self) -> String {
        format!("AsyncLeaf[{}]: {}", self.name, self.value)
    }

    async fn add(&mut self, _component: Box<dyn AsyncComponent + Send>) {
        // 叶子节点不支持添加子组件
    }

    async fn remove(&mut self, _name: &str) {
        // 叶子节点不支持删除子组件
    }

    async fn get_child(&self, _name: &str) -> Option<&Box<dyn AsyncComponent + Send>> {
        None
    }

    async fn get_children(&self) -> Vec<&Box<dyn AsyncComponent + Send>> {
        Vec::new()
    }
}

struct AsyncComposite {
    name: String,
    children: HashMap<String, Box<dyn AsyncComponent + Send>>,
}

#[async_trait]
impl AsyncComponent for AsyncComposite {
    async fn operation(&self) -> String {
        let mut result = format!("AsyncComposite[{}]: ", self.name);
        for child in self.children.values() {
            result.push_str(&format!("({})", child.operation().await));
        }
        result
    }

    async fn add(&mut self, component: Box<dyn AsyncComponent + Send>) {
        let name = format!("child_{}", self.children.len());
        self.children.insert(name, component);
    }

    async fn remove(&mut self, name: &str) {
        self.children.remove(name);
    }

    async fn get_child(&self, name: &str) -> Option<&Box<dyn AsyncComponent + Send>> {
        self.children.get(name)
    }

    async fn get_children(&self) -> Vec<&Box<dyn AsyncComponent + Send>> {
        self.children.values().collect()
    }
}
```

### 3.4 应用场景实现

```rust
// 文件系统示例
struct FileSystemComponent {
    name: String,
    size: u64,
    children: HashMap<String, Box<dyn FileSystemComponent>>,
    is_file: bool,
}

impl FileSystemComponent {
    fn new_file(name: String, size: u64) -> Self {
        FileSystemComponent {
            name,
            size,
            children: HashMap::new(),
            is_file: true,
        }
    }

    fn new_directory(name: String) -> Self {
        FileSystemComponent {
            name,
            size: 0,
            children: HashMap::new(),
            is_file: false,
        }
    }

    fn add_child(&mut self, child: Box<dyn FileSystemComponent>) {
        if !self.is_file {
            self.children.insert(child.get_name().clone(), child);
        }
    }

    fn get_name(&self) -> &String {
        &self.name
    }

    fn get_size(&self) -> u64 {
        if self.is_file {
            self.size
        } else {
            self.children.values().map(|child| child.get_size()).sum()
        }
    }

    fn list_contents(&self) -> Vec<String> {
        if self.is_file {
            vec![format!("{} ({})", self.name, self.size)]
        } else {
            let mut contents = vec![format!("{} (dir)", self.name)];
            for child in self.children.values() {
                contents.extend(child.list_contents().iter().map(|s| format!("  {}", s)));
            }
            contents
        }
    }
}

// 图形界面示例
trait UIComponent {
    fn render(&self) -> String;
    fn add_child(&mut self, child: Box<dyn UIComponent>);
    fn remove_child(&mut self, name: &str);
    fn get_name(&self) -> &String;
}

struct UIWindow {
    name: String,
    title: String,
    children: HashMap<String, Box<dyn UIComponent>>,
}

impl UIWindow {
    fn new(name: String, title: String) -> Self {
        UIWindow {
            name,
            title,
            children: HashMap::new(),
        }
    }
}

impl UIComponent for UIWindow {
    fn render(&self) -> String {
        let mut result = format!("Window: {}\n", self.title);
        for child in self.children.values() {
            result.push_str(&format!("  {}\n", child.render()));
        }
        result
    }

    fn add_child(&mut self, child: Box<dyn UIComponent>) {
        self.children.insert(child.get_name().clone(), child);
    }

    fn remove_child(&mut self, name: &str) {
        self.children.remove(name);
    }

    fn get_name(&self) -> &String {
        &self.name
    }
}

struct UIButton {
    name: String,
    text: String,
}

impl UIButton {
    fn new(name: String, text: String) -> Self {
        UIButton { name, text }
    }
}

impl UIComponent for UIButton {
    fn render(&self) -> String {
        format!("Button: {}", self.text)
    }

    fn add_child(&mut self, _child: Box<dyn UIComponent>) {
        // 按钮不支持子组件
    }

    fn remove_child(&mut self, _name: &str) {
        // 按钮不支持子组件
    }

    fn get_name(&self) -> &String {
        &self.name
    }
}
```

## 4. 应用场景 (Application Scenarios)

### 4.1 文件系统 (File System)

**场景描述：**
文件系统是组合模式的经典应用，目录可以包含文件和子目录，形成树形结构。

**优势：**
- 统一处理文件和目录
- 递归遍历文件系统
- 计算目录大小等操作

### 4.2 图形用户界面 (GUI)

**场景描述：**
GUI框架中，窗口可以包含按钮、面板等组件，面板又可以包含其他组件。

**优势：**
- 统一渲染接口
- 递归布局计算
- 事件传播机制

### 4.3 组织架构 (Organization Structure)

**场景描述：**
公司组织架构中，部门可以包含员工和子部门。

**优势：**
- 统一管理接口
- 递归统计功能
- 权限控制机制

### 4.4 数学表达式 (Mathematical Expressions)

**场景描述：**
数学表达式可以表示为树形结构，操作符是复合节点，数字是叶子节点。

**优势：**
- 统一计算接口
- 递归求值
- 表达式优化

## 5. 变体模式 (Variant Patterns)

### 5.1 安全组合模式 (Safe Composite Pattern)

**特点：**
- 在 Component 接口中不定义 add/remove 方法
- 只在 Composite 类中定义这些方法
- 提供类型安全保证

### 5.2 透明组合模式 (Transparent Composite Pattern)

**特点：**
- 在 Component 接口中定义 add/remove 方法
- Leaf 类提供空实现
- 提供统一接口

### 5.3 父引用组合模式 (Parent Reference Composite Pattern)

**特点：**
- 每个组件维护对父组件的引用
- 支持向上遍历
- 简化删除操作

### 5.4 缓存组合模式 (Cached Composite Pattern)

**特点：**
- 缓存计算结果
- 避免重复计算
- 提高性能

## 6. 质量属性分析 (Quality Attributes Analysis)

### 6.1 可维护性 (Maintainability)

**评分：** ⭐⭐⭐⭐⭐

**分析：**
- 统一接口简化维护
- 递归结构清晰
- 易于扩展新组件类型

### 6.2 可扩展性 (Extensibility)

**评分：** ⭐⭐⭐⭐⭐

**分析：**
- 支持动态添加组件
- 支持新组件类型
- 支持新操作类型

### 6.3 可重用性 (Reusability)

**评分：** ⭐⭐⭐⭐⭐

**分析：**
- 组件高度可重用
- 操作可应用于不同结构
- 接口标准化

### 6.4 性能 (Performance)

**评分：** ⭐⭐⭐⭐

**分析：**
- 遍历复杂度 $O(n)$
- 内存使用合理
- 支持缓存优化

## 7. 总结 (Summary)

组合模式通过树形结构实现了"部分-整体"的层次结构，提供了统一的操作接口。其数学理论基础扎实，Rust实现灵活多样，应用场景广泛。该模式在文件系统、GUI框架、组织架构等领域都有重要应用，是面向对象设计中的核心模式之一。

---

**文档版本**: 1.0  
**最后更新**: 2024-12-19  
**作者**: AI Assistant  
**状态**: 已完成
