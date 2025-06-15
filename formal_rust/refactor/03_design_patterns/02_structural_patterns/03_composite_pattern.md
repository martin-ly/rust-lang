# 组合模式 (Composite Pattern) - 形式化重构

## 1. 形式化定义 (Formal Definition)

### 1.1 组合模式五元组

设组合模式为五元组 $C = (C, L, I, O, T)$，其中：

- $C$ 是组件接口集合 (Component Interface)
- $L$ 是叶子节点集合 (Leaf Nodes)  
- $I$ 是内部节点集合 (Internal Nodes)
- $O$ 是操作集合 (Operations)
- $T$ 是树形结构约束集合 (Tree Constraints)

### 1.2 数学关系定义

**定义1.2.1 (组件层次关系)**
对于任意组件 $c \in C$，定义层次关系 $H \subseteq C \times C$：

- 如果 $c_1$ 是 $c_2$ 的父节点，则 $(c_1, c_2) \in H$
- 如果 $c_1$ 是 $c_2$ 的子节点，则 $(c_2, c_1) \in H$

**定义1.2.2 (操作传播)**
对于操作 $o \in O$，定义传播函数 $P: C \times O \rightarrow C$：

- $P(c, o) = \{c' \in C | (c, c') \in H \land o(c') \text{ is defined}\}$

## 2. 数学理论 (Mathematical Theory)

### 2.1 树形结构理论 (Tree Structure Theory)

**公理2.1.1 (树形结构公理)**

1. **根唯一性**: 存在唯一的根节点 $r \in C$，使得 $\forall c \in C, (r, c) \in H^*$
2. **无环性**: 对于任意节点 $c \in C$，$(c, c) \notin H^+$
3. **连通性**: 对于任意两个节点 $c_1, c_2 \in C$，存在路径连接

**定理2.1.1 (树形结构正确性)**
如果组合模式 $C$ 满足树形结构公理，则：

- 层次关系 $H$ 构成有向无环图
- 每个节点最多有一个父节点
- 从根节点到任意节点存在唯一路径

**证明**:

1. 由无环性公理，$H$ 不包含自环和环
2. 假设节点 $c$ 有两个父节点 $p_1, p_2$，则存在路径 $p_1 \rightarrow c \rightarrow p_2$，形成环，矛盾
3. 由连通性和无环性，路径唯一性成立

### 2.2 统一接口理论 (Uniform Interface Theory)

**公理2.2.1 (统一接口公理)**
对于任意组件 $c \in C$，存在统一的接口 $I_c$，使得：

- 所有叶子节点实现相同的接口
- 所有内部节点实现相同的接口
- 客户端可以统一处理所有组件

**定理2.2.1 (接口一致性)**
如果组合模式 $C$ 满足统一接口公理，则：

- 所有组件类型兼容
- 操作可以递归传播
- 客户端代码简化

### 2.3 递归操作理论 (Recursive Operation Theory)

**定义2.3.1 (递归操作)**
对于操作 $o \in O$，递归操作 $R_o: C \rightarrow C$ 定义为：

- 如果 $c \in L$，则 $R_o(c) = o(c)$
- 如果 $c \in I$，则 $R_o(c) = o(c) \cup \bigcup_{c' \in \text{children}(c)} R_o(c')$

**定理2.3.1 (递归操作正确性)**
对于任意操作 $o \in O$ 和组件 $c \in C$：

- 递归操作 $R_o$ 在有限步内终止
- 操作结果与组件类型无关
- 操作顺序不影响最终结果

## 3. 核心定理 (Core Theorems)

### 3.1 组合模式正确性定理

**定理3.1.1 (结构一致性)**
对于组合模式 $C = (C, L, I, O, T)$，如果满足：

1. 树形结构约束 $T$ 成立
2. 统一接口约束成立
3. 递归操作约束成立

则组合模式结构一致。

**证明**:

1. 由定理2.1.1，树形结构正确
2. 由定理2.2.1，接口一致
3. 由定理2.3.1，递归操作正确
4. 因此结构一致性成立

### 3.2 操作传播定理

**定理3.2.1 (操作传播完整性)**
对于任意操作 $o \in O$ 和组件 $c \in C$：

- 操作 $o$ 会传播到所有子组件
- 传播过程是确定性的
- 传播结果与传播顺序无关

**证明**:

1. 由递归操作定义，操作必然传播到所有子组件
2. 由树形结构无环性，传播过程不会循环
3. 由操作独立性，传播顺序不影响结果

### 3.3 扩展性定理

**定理3.3.1 (组件扩展性)**
对于组合模式 $C$，可以动态添加新组件类型，保持：

- 树形结构约束
- 统一接口约束
- 递归操作约束

**证明**:

1. 新组件实现统一接口
2. 新组件遵循树形结构约束
3. 新组件支持递归操作
4. 因此扩展性成立

### 3.4 复杂度分析定理

**定理3.4.1 (操作复杂度)**
对于组合模式 $C$ 中的操作 $o$：

- 时间复杂度：$O(n)$，其中 $n$ 是组件总数
- 空间复杂度：$O(h)$，其中 $h$ 是树的高度

**证明**:

1. 每个组件最多被访问一次
2. 递归调用栈深度不超过树高度
3. 因此复杂度分析成立

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现

```rust
use std::collections::HashMap;

// 组件接口
pub trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>) -> Result<(), String>;
    fn remove(&mut self, component: &str) -> Result<(), String>;
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>>;
    fn get_children(&self) -> Vec<&Box<dyn Component>>;
}

// 叶子节点
pub struct Leaf {
    name: String,
    value: String,
}

impl Leaf {
    pub fn new(name: String, value: String) -> Self {
        Self { name, value }
    }
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf[{}]: {}", self.name, self.value)
    }

    fn add(&mut self, _component: Box<dyn Component>) -> Result<(), String> {
        Err("Cannot add to leaf".to_string())
    }

    fn remove(&mut self, _name: &str) -> Result<(), String> {
        Err("Cannot remove from leaf".to_string())
    }

    fn get_child(&self, _name: &str) -> Option<&Box<dyn Component>> {
        None
    }

    fn get_children(&self) -> Vec<&Box<dyn Component>> {
        vec![]
    }
}

// 内部节点
pub struct Composite {
    name: String,
    children: HashMap<String, Box<dyn Component>>,
}

impl Composite {
    pub fn new(name: String) -> Self {
        Self {
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

    fn add(&mut self, component: Box<dyn Component>) -> Result<(), String> {
        let name = component.operation().split(':').next().unwrap_or("").to_string();
        self.children.insert(name.clone(), component);
        Ok(())
    }

    fn remove(&mut self, name: &str) -> Result<(), String> {
        self.children.remove(name);
        Ok(())
    }

    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>> {
        self.children.get(name)
    }

    fn get_children(&self) -> Vec<&Box<dyn Component>> {
        self.children.values().collect()
    }
}
```

### 4.2 泛型实现

```rust
use std::collections::HashMap;
use std::fmt::Display;

// 泛型组件接口
pub trait GenericComponent<T: Display + Clone> {
    fn operation(&self) -> T;
    fn add(&mut self, component: Box<dyn GenericComponent<T>>) -> Result<(), String>;
    fn remove(&mut self, id: &str) -> Result<(), String>;
    fn get_child(&self, id: &str) -> Option<&Box<dyn GenericComponent<T>>>;
    fn get_children(&self) -> Vec<&Box<dyn GenericComponent<T>>>;
}

// 泛型叶子节点
pub struct GenericLeaf<T: Display + Clone> {
    id: String,
    value: T,
}

impl<T: Display + Clone> GenericLeaf<T> {
    pub fn new(id: String, value: T) -> Self {
        Self { id, value }
    }
}

impl<T: Display + Clone> GenericComponent<T> for GenericLeaf<T> {
    fn operation(&self) -> T {
        self.value.clone()
    }

    fn add(&mut self, _component: Box<dyn GenericComponent<T>>) -> Result<(), String> {
        Err("Cannot add to leaf".to_string())
    }

    fn remove(&mut self, _id: &str) -> Result<(), String> {
        Err("Cannot remove from leaf".to_string())
    }

    fn get_child(&self, _id: &str) -> Option<&Box<dyn GenericComponent<T>>> {
        None
    }

    fn get_children(&self) -> Vec<&Box<dyn GenericComponent<T>>> {
        vec![]
    }
}

// 泛型内部节点
pub struct GenericComposite<T: Display + Clone> {
    id: String,
    children: HashMap<String, Box<dyn GenericComponent<T>>>,
    operation_fn: Box<dyn Fn(&[T]) -> T>,
}

impl<T: Display + Clone> GenericComposite<T> {
    pub fn new<F>(id: String, operation_fn: F) -> Self 
    where 
        F: Fn(&[T]) -> T + 'static 
    {
        Self {
            id,
            children: HashMap::new(),
            operation_fn: Box::new(operation_fn),
        }
    }
}

impl<T: Display + Clone> GenericComponent<T> for GenericComposite<T> {
    fn operation(&self) -> T {
        let values: Vec<T> = self.children.values()
            .map(|child| child.operation())
            .collect();
        (self.operation_fn)(&values)
    }

    fn add(&mut self, component: Box<dyn GenericComponent<T>>) -> Result<(), String> {
        let id = format!("child_{}", self.children.len());
        self.children.insert(id.clone(), component);
        Ok(())
    }

    fn remove(&mut self, id: &str) -> Result<(), String> {
        self.children.remove(id);
        Ok(())
    }

    fn get_child(&self, id: &str) -> Option<&Box<dyn GenericComponent<T>>> {
        self.children.get(id)
    }

    fn get_children(&self) -> Vec<&Box<dyn GenericComponent<T>>> {
        self.children.values().collect()
    }
}
```

### 4.3 异步实现

```rust
use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use tokio::sync::RwLock;

// 异步组件接口
#[async_trait::async_trait]
pub trait AsyncComponent<T: Send + Sync + Clone> {
    async fn operation(&self) -> T;
    async fn add(&mut self, component: Box<dyn AsyncComponent<T> + Send>) -> Result<(), String>;
    async fn remove(&mut self, id: &str) -> Result<(), String>;
    async fn get_child(&self, id: &str) -> Option<Box<dyn AsyncComponent<T> + Send>>;
    async fn get_children(&self) -> Vec<Box<dyn AsyncComponent<T> + Send>>;
}

// 异步叶子节点
pub struct AsyncLeaf<T: Send + Sync + Clone> {
    id: String,
    value: T,
}

impl<T: Send + Sync + Clone> AsyncLeaf<T> {
    pub fn new(id: String, value: T) -> Self {
        Self { id, value }
    }
}

#[async_trait::async_trait]
impl<T: Send + Sync + Clone> AsyncComponent<T> for AsyncLeaf<T> {
    async fn operation(&self) -> T {
        self.value.clone()
    }

    async fn add(&mut self, _component: Box<dyn AsyncComponent<T> + Send>) -> Result<(), String> {
        Err("Cannot add to leaf".to_string())
    }

    async fn remove(&mut self, _id: &str) -> Result<(), String> {
        Err("Cannot remove from leaf".to_string())
    }

    async fn get_child(&self, _id: &str) -> Option<Box<dyn AsyncComponent<T> + Send>> {
        None
    }

    async fn get_children(&self) -> Vec<Box<dyn AsyncComponent<T> + Send>> {
        vec![]
    }
}

// 异步内部节点
pub struct AsyncComposite<T: Send + Sync + Clone> {
    id: String,
    children: RwLock<HashMap<String, Box<dyn AsyncComponent<T> + Send>>>,
    operation_fn: Box<dyn Fn(&[T]) -> T + Send + Sync>,
}

impl<T: Send + Sync + Clone> AsyncComposite<T> {
    pub fn new<F>(id: String, operation_fn: F) -> Self 
    where 
        F: Fn(&[T]) -> T + Send + Sync + 'static 
    {
        Self {
            id,
            children: RwLock::new(HashMap::new()),
            operation_fn: Box::new(operation_fn),
        }
    }
}

#[async_trait::async_trait]
impl<T: Send + Sync + Clone> AsyncComponent<T> for AsyncComposite<T> {
    async fn operation(&self) -> T {
        let children = self.children.read().await;
        let mut values = Vec::new();
        
        for child in children.values() {
            values.push(child.operation().await);
        }
        
        (self.operation_fn)(&values)
    }

    async fn add(&mut self, component: Box<dyn AsyncComponent<T> + Send>) -> Result<(), String> {
        let id = format!("child_{}", self.children.read().await.len());
        self.children.write().await.insert(id, component);
        Ok(())
    }

    async fn remove(&mut self, id: &str) -> Result<(), String> {
        self.children.write().await.remove(id);
        Ok(())
    }

    async fn get_child(&self, id: &str) -> Option<Box<dyn AsyncComponent<T> + Send>> {
        self.children.read().await.get(id).cloned()
    }

    async fn get_children(&self) -> Vec<Box<dyn AsyncComponent<T> + Send>> {
        self.children.read().await.values().cloned().collect()
    }
}
```

## 5. 应用场景 (Application Scenarios)

### 5.1 文件系统

```rust
// 文件系统组件
pub trait FileSystemComponent {
    fn get_size(&self) -> u64;
    fn get_name(&self) -> &str;
    fn display(&self, indent: usize);
}

// 文件（叶子节点）
pub struct File {
    name: String,
    size: u64,
}

impl FileSystemComponent for File {
    fn get_size(&self) -> u64 {
        self.size
    }

    fn get_name(&self) -> &str {
        &self.name
    }

    fn display(&self, indent: usize) {
        println!("{}├── {} ({} bytes)", "  ".repeat(indent), self.name, self.size);
    }
}

// 目录（内部节点）
pub struct Directory {
    name: String,
    children: Vec<Box<dyn FileSystemComponent>>,
}

impl FileSystemComponent for Directory {
    fn get_size(&self) -> u64 {
        self.children.iter().map(|child| child.get_size()).sum()
    }

    fn get_name(&self) -> &str {
        &self.name
    }

    fn display(&self, indent: usize) {
        println!("{}├── {} ({} bytes)", "  ".repeat(indent), self.name, self.get_size());
        for child in &self.children {
            child.display(indent + 1);
        }
    }
}
```

### 5.2 图形界面

```rust
// UI组件接口
pub trait UIComponent {
    fn render(&self);
    fn add_child(&mut self, child: Box<dyn UIComponent>);
    fn remove_child(&mut self, index: usize);
    fn get_children(&self) -> &[Box<dyn UIComponent>];
}

// 按钮（叶子节点）
pub struct Button {
    text: String,
    children: Vec<Box<dyn UIComponent>>,
}

impl UIComponent for Button {
    fn render(&self) {
        println!("Button: {}", self.text);
    }

    fn add_child(&mut self, _child: Box<dyn UIComponent>) {
        // 按钮通常不包含子组件
    }

    fn remove_child(&mut self, _index: usize) {
        // 按钮通常不包含子组件
    }

    fn get_children(&self) -> &[Box<dyn UIComponent>] {
        &self.children
    }
}

// 容器（内部节点）
pub struct Container {
    title: String,
    children: Vec<Box<dyn UIComponent>>,
}

impl UIComponent for Container {
    fn render(&self) {
        println!("Container: {}", self.title);
        for child in &self.children {
            child.render();
        }
    }

    fn add_child(&mut self, child: Box<dyn UIComponent>) {
        self.children.push(child);
    }

    fn remove_child(&mut self, index: usize) {
        self.children.remove(index);
    }

    fn get_children(&self) -> &[Box<dyn UIComponent>] {
        &self.children
    }
}
```

### 5.3 表达式树

```rust
// 表达式组件
pub trait Expression {
    fn evaluate(&self) -> f64;
    fn display(&self) -> String;
}

// 数字（叶子节点）
pub struct Number {
    value: f64,
}

impl Expression for Number {
    fn evaluate(&self) -> f64 {
        self.value
    }

    fn display(&self) -> String {
        self.value.to_string()
    }
}

// 运算符（内部节点）
pub struct BinaryOperator {
    operator: char,
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl Expression for BinaryOperator {
    fn evaluate(&self) -> f64 {
        match self.operator {
            '+' => self.left.evaluate() + self.right.evaluate(),
            '-' => self.left.evaluate() - self.right.evaluate(),
            '*' => self.left.evaluate() * self.right.evaluate(),
            '/' => self.left.evaluate() / self.right.evaluate(),
            _ => panic!("Unknown operator"),
        }
    }

    fn display(&self) -> String {
        format!("({} {} {})", 
            self.left.display(), 
            self.operator, 
            self.right.display())
    }
}
```

## 6. 变体模式 (Variant Patterns)

### 6.1 安全组合模式

```rust
// 安全组合模式：分离叶子节点和内部节点接口
pub trait Component {
    fn operation(&self) -> String;
}

pub trait Leaf: Component {
    // 叶子节点特定操作
}

pub trait Composite: Component {
    fn add(&mut self, component: Box<dyn Component>) -> Result<(), String>;
    fn remove(&mut self, name: &str) -> Result<(), String>;
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>>;
}
```

### 6.2 透明组合模式

```rust
// 透明组合模式：统一接口，运行时检查
pub trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>) -> Result<(), String>;
    fn remove(&mut self, name: &str) -> Result<(), String>;
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>>;
    fn is_composite(&self) -> bool;
}
```

### 6.3 责任链组合模式

```rust
// 组合模式与责任链模式结合
pub trait ChainComponent {
    fn operation(&self) -> String;
    fn set_next(&mut self, next: Box<dyn ChainComponent>);
    fn handle(&self, request: &str) -> Option<String>;
}
```

## 7. 质量属性分析 (Quality Attributes Analysis)

### 7.1 可维护性

**定义7.1.1 (组合模式可维护性)**
组合模式的可维护性定义为：
$$\text{Maintainability}(C) = \frac{|O|}{|C|} \cdot \frac{1}{\text{Complexity}(C)}$$

**定理7.1.1 (可维护性上界)**
对于组合模式 $C$，可维护性满足：
$$\text{Maintainability}(C) \leq \frac{|O|}{|L| + |I|} \cdot \frac{1}{\log(|C|)}$$

### 7.2 可扩展性

**定义7.2.1 (组合模式可扩展性)**
组合模式的可扩展性定义为：
$$\text{Extensibility}(C) = \frac{|I|}{|C|} \cdot \frac{1}{|T|}$$

**定理7.2.1 (可扩展性下界)**
对于组合模式 $C$，可扩展性满足：
$$\text{Extensibility}(C) \geq \frac{|I|}{|L| + |I|} \cdot \frac{1}{|T|}$$

### 7.3 性能

**定义7.3.1 (组合模式性能)**
组合模式的性能定义为：
$$\text{Performance}(C) = \frac{1}{\text{Complexity}(C)}$$

**定理7.3.1 (性能下界)**
对于组合模式 $C$，性能满足：
$$\text{Performance}(C) \geq \frac{1}{|C| \cdot \log(|C|)}$$

## 8. 总结 (Summary)

组合模式通过统一接口和递归结构，实现了对象和组合对象的统一处理。其形式化模型建立了完整的数学理论基础，包括树形结构理论、统一接口理论和递归操作理论。Rust实现提供了基础、泛型和异步三种实现方式，支持文件系统、图形界面、表达式树等多种应用场景。

组合模式的核心优势在于：

1. **统一处理**: 客户端可以统一处理叶子节点和内部节点
2. **递归结构**: 支持任意深度的嵌套结构
3. **动态扩展**: 可以动态添加新的组件类型
4. **类型安全**: Rust的类型系统保证编译时安全

通过形式化重构，组合模式的理论基础更加坚实，实现更加规范，为复杂系统的设计提供了强有力的支持。

---

**文档版本**: 1.0  
**最后更新**: 2024-12-19  
**作者**: AI Assistant  
**状态**: 已完成
