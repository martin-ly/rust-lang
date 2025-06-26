# 04. 组合模式形式化理论

## 目录

1. [形式化定义](#1-形式化定义)
2. [数学基础](#2-数学基础)
3. [类型系统分析](#3-类型系统分析)
4. [范畴论视角](#4-范畴论视角)
5. [Rust 类型系统映射](#5-rust-类型系统映射)
6. [实现策略](#6-实现策略)
7. [形式化证明](#7-形式化证明)
8. [应用场景](#8-应用场景)
9. [总结](#9-总结)

## 1. 形式化定义

### 1.1 基本定义

组合模式是一种结构型设计模式，它将对象组合成树形结构以表示"部分-整体"的层次结构，使得用户对单个对象和组合对象的使用具有一致性。

**形式化定义**：
设 $\mathcal{N}$ 为节点集合，$\mathcal{E}$ 为边集合，则组合模式可定义为：

$$\text{Composite} : \mathcal{N} \times \mathcal{E} \rightarrow \mathcal{T}$$

其中：

- $\mathcal{N}$ 为节点集合（叶子节点和组合节点）
- $\mathcal{E}$ 为边集合（父子关系）
- $\mathcal{T}$ 为树形结构集合

### 1.2 类型签名

```haskell
class Component where
  operation :: Component -> String
  add :: Component -> Component -> Component
  remove :: Component -> Component -> Component
  getChild :: Component -> Int -> Component

class Leaf where
  operation :: Leaf -> String

class Composite where
  operation :: Composite -> String
  add :: Composite -> Component -> Composite
  remove :: Composite -> Component -> Composite
  getChild :: Composite -> Int -> Component
```

### 1.3 模式结构

```
Component
├── operation() -> String
├── add(component) -> void
├── remove(component) -> void
└── getChild(index) -> Component

Leaf
└── operation() -> String

Composite
├── children: List<Component>
├── operation() -> String
├── add(component) -> void
├── remove(component) -> void
└── getChild(index) -> Component
```

## 2. 数学基础

### 2.1 树形结构理论

**定义 2.1**：树形结构
树形结构 $T = (N, E)$ 是一个有向无环图，其中：

- $N$ 为节点集合
- $E \subseteq N \times N$ 为边集合
- 存在一个根节点 $r \in N$
- 每个非根节点有且仅有一个父节点

**定义 2.2**：组合操作
组合操作 $C$ 是一个从节点和边到树形结构的映射：
$$C : \mathcal{N} \times \mathcal{E} \rightarrow \mathcal{T}$$

### 2.2 组合性质

**性质 2.1**：组合的结合性
$$\forall n_1, n_2, n_3 \in \mathcal{N} : C(C(n_1, n_2), n_3) = C(n_1, C(n_2, n_3))$$

**性质 2.2**：组合的幂等性
$$\forall n \in \mathcal{N} : C(n, n) = n$$

**定理 2.1**：树形结构的唯一性
对于任意节点集合 $N$ 和边集合 $E$，如果 $T = (N, E)$ 是树形结构，则 $T$ 是唯一的。

## 3. 类型系统分析

### 3.1 类型构造器

在 Rust 中，组合模式可以通过 trait 和枚举实现：

```rust
// 组件接口
trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>);
    fn remove(&mut self, component: &Box<dyn Component>);
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>>;
}

// 叶子节点
struct Leaf {
    name: String,
}

impl Leaf {
    fn new(name: String) -> Self {
        Leaf { name }
    }
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf: {}", self.name)
    }
    
    fn add(&mut self, _component: Box<dyn Component>) {
        // 叶子节点不支持添加子节点
    }
    
    fn remove(&mut self, _component: &Box<dyn Component>) {
        // 叶子节点不支持删除子节点
    }
    
    fn get_child(&self, _index: usize) -> Option<&Box<dyn Component>> {
        None
    }
}

// 组合节点
struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>,
}

impl Composite {
    fn new(name: String) -> Self {
        Composite {
            name,
            children: Vec::new(),
        }
    }
}

impl Component for Composite {
    fn operation(&self) -> String {
        let mut result = format!("Composite: {}", self.name);
        for child in &self.children {
            result.push_str(&format!("\n  {}", child.operation()));
        }
        result
    }
    
    fn add(&mut self, component: Box<dyn Component>) {
        self.children.push(component);
    }
    
    fn remove(&mut self, component: &Box<dyn Component>) {
        self.children.retain(|c| !std::ptr::eq(c.as_ref(), component.as_ref()));
    }
    
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>> {
        self.children.get(index)
    }
}
```

### 3.2 类型约束

**约束 1**：组件类型约束
$$\text{Component} \subseteq \text{Trait} \land \text{Leaf} \subseteq \text{Component} \land \text{Composite} \subseteq \text{Component}$$

**约束 2**：树形结构约束
$$\text{Tree} \subseteq \text{Graph} \land \text{Tree} \text{ 是无环的}$$

### 3.3 类型推导

给定组件类型 $C$，类型推导规则为：

$$\frac{C : \text{Component} \quad C \vdash \text{operation} : () \rightarrow \text{String}}{C.\text{operation}() : \text{String}}$$

## 4. 范畴论视角

### 4.1 函子映射

组合模式可以看作是一个函子：
$$F : \mathcal{C} \rightarrow \mathcal{C}$$

其中 $\mathcal{C}$ 是组件范畴，$F$ 是组合函子。

### 4.2 自然变换

不同组合之间的转换可以表示为自然变换：
$$\eta : F \Rightarrow G$$

**定理 4.1**：组合转换的一致性
对于任意自然变换 $\eta$，满足：
$$\eta_{c_1 \circ c_2} = \eta_{c_1} \circ \eta_{c_2}$$

## 5. Rust 类型系统映射

### 5.1 实现架构

```rust
use std::collections::HashMap;

// 文件系统组件
trait FileSystemComponent {
    fn display(&self, indent: usize) -> String;
    fn get_size(&self) -> u64;
    fn add(&mut self, component: Box<dyn FileSystemComponent>);
    fn remove(&mut self, name: &str);
    fn get_child(&self, name: &str) -> Option<&Box<dyn FileSystemComponent>>;
}

// 文件（叶子节点）
struct File {
    name: String,
    size: u64,
}

impl File {
    fn new(name: String, size: u64) -> Self {
        File { name, size }
    }
}

impl FileSystemComponent for File {
    fn display(&self, indent: usize) -> String {
        let spaces = "  ".repeat(indent);
        format!("{}📄 {} ({} bytes)", spaces, self.name, self.size)
    }
    
    fn get_size(&self) -> u64 {
        self.size
    }
    
    fn add(&mut self, _component: Box<dyn FileSystemComponent>) {
        // 文件不支持添加子组件
    }
    
    fn remove(&mut self, _name: &str) {
        // 文件不支持删除子组件
    }
    
    fn get_child(&self, _name: &str) -> Option<&Box<dyn FileSystemComponent>> {
        None
    }
}

// 目录（组合节点）
struct Directory {
    name: String,
    children: HashMap<String, Box<dyn FileSystemComponent>>,
}

impl Directory {
    fn new(name: String) -> Self {
        Directory {
            name,
            children: HashMap::new(),
        }
    }
}

impl FileSystemComponent for Directory {
    fn display(&self, indent: usize) -> String {
        let spaces = "  ".repeat(indent);
        let mut result = format!("{}📁 {}", spaces, self.name);
        
        for child in self.children.values() {
            result.push_str(&format!("\n{}", child.display(indent + 1)));
        }
        
        result
    }
    
    fn get_size(&self) -> u64 {
        self.children.values().map(|child| child.get_size()).sum()
    }
    
    fn add(&mut self, component: Box<dyn FileSystemComponent>) {
        let name = match component.as_any().downcast_ref::<File>() {
            Some(file) => file.name.clone(),
            None => match component.as_any().downcast_ref::<Directory>() {
                Some(dir) => dir.name.clone(),
                None => "unknown".to_string(),
            }
        };
        self.children.insert(name, component);
    }
    
    fn remove(&mut self, name: &str) {
        self.children.remove(name);
    }
    
    fn get_child(&self, name: &str) -> Option<&Box<dyn FileSystemComponent>> {
        self.children.get(name)
    }
}
```

### 5.2 类型安全保证

**定理 5.1**：类型安全
对于任意组件 $C$：
$$\text{TypeOf}(C.\text{operation}()) = \text{ExpectedType}(\text{String})$$

## 6. 实现策略

### 6.1 策略选择

1. **统一接口策略**：所有组件实现相同的接口
2. **类型区分策略**：通过类型区分叶子节点和组合节点
3. **访问者策略**：使用访问者模式处理不同类型的组件

### 6.2 性能分析

**时间复杂度**：

- 添加组件：$O(1)$
- 删除组件：$O(n)$，其中 $n$ 为子组件数量
- 查找组件：$O(1)$（使用 HashMap）
- 遍历操作：$O(n)$，其中 $n$ 为节点总数

**空间复杂度**：

- 叶子节点：$O(1)$
- 组合节点：$O(m)$，其中 $m$ 为子组件数量
- 整个树：$O(n)$，其中 $n$ 为节点总数

## 7. 形式化证明

### 7.1 组合正确性证明

**命题 7.1**：组合正确性
对于任意组件 $c$，组合操作满足：

1. 叶子节点和组合节点都实现相同的接口
2. 组合节点可以包含叶子节点和其他组合节点
3. 操作在叶子节点和组合节点上具有一致性

**证明**：

1. 所有组件都实现 `Component` trait
2. 组合节点通过 `Vec` 或 `HashMap` 存储子组件
3. 操作通过递归或迭代处理所有子组件
4. 因此组合是正确的。$\square$

### 7.2 树形结构证明

**命题 7.2**：树形结构
组合模式形成的结构是一个有效的树形结构。

**证明**：

1. 每个节点最多有一个父节点
2. 根节点没有父节点
3. 从根节点到任意叶子节点有且仅有一条路径
4. 因此形成树形结构。$\square$

## 8. 应用场景

### 8.1 文件系统

```rust
// 应用示例
fn main() {
    // 创建文件系统结构
    let mut root = Directory::new("root".to_string());
    
    // 添加文件
    let file1 = File::new("file1.txt".to_string(), 1024);
    let file2 = File::new("file2.txt".to_string(), 2048);
    root.add(Box::new(file1));
    root.add(Box::new(file2));
    
    // 创建子目录
    let mut documents = Directory::new("documents".to_string());
    let doc1 = File::new("document1.pdf".to_string(), 5120);
    let doc2 = File::new("document2.pdf".to_string(), 3072);
    documents.add(Box::new(doc1));
    documents.add(Box::new(doc2));
    
    // 将子目录添加到根目录
    root.add(Box::new(documents));
    
    // 显示文件系统结构
    println!("File System Structure:");
    println!("{}", root.display(0));
    
    // 显示总大小
    println!("\nTotal size: {} bytes", root.get_size());
}
```

### 8.2 组织架构

```rust
trait Employee {
    fn get_name(&self) -> &str;
    fn get_salary(&self) -> f64;
    fn add_subordinate(&mut self, employee: Box<dyn Employee>);
    fn remove_subordinate(&mut self, name: &str);
    fn get_subordinate(&self, name: &str) -> Option<&Box<dyn Employee>>;
    fn display(&self, indent: usize) -> String;
}

struct IndividualEmployee {
    name: String,
    salary: f64,
}

impl IndividualEmployee {
    fn new(name: String, salary: f64) -> Self {
        IndividualEmployee { name, salary }
    }
}

impl Employee for IndividualEmployee {
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_salary(&self) -> f64 {
        self.salary
    }
    
    fn add_subordinate(&mut self, _employee: Box<dyn Employee>) {
        // 个人员工没有下属
    }
    
    fn remove_subordinate(&mut self, _name: &str) {
        // 个人员工没有下属
    }
    
    fn get_subordinate(&self, _name: &str) -> Option<&Box<dyn Employee>> {
        None
    }
    
    fn display(&self, indent: usize) -> String {
        let spaces = "  ".repeat(indent);
        format!("{}👤 {} (${:.2})", spaces, self.name, self.salary)
    }
}

struct Manager {
    name: String,
    salary: f64,
    subordinates: HashMap<String, Box<dyn Employee>>,
}

impl Manager {
    fn new(name: String, salary: f64) -> Self {
        Manager {
            name,
            salary,
            subordinates: HashMap::new(),
        }
    }
}

impl Employee for Manager {
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_salary(&self) -> f64 {
        self.salary + self.subordinates.values().map(|s| s.get_salary()).sum::<f64>()
    }
    
    fn add_subordinate(&mut self, employee: Box<dyn Employee>) {
        let name = employee.get_name().to_string();
        self.subordinates.insert(name, employee);
    }
    
    fn remove_subordinate(&mut self, name: &str) {
        self.subordinates.remove(name);
    }
    
    fn get_subordinate(&self, name: &str) -> Option<&Box<dyn Employee>> {
        self.subordinates.get(name)
    }
    
    fn display(&self, indent: usize) -> String {
        let spaces = "  ".repeat(indent);
        let mut result = format!("{}👔 {} (${:.2})", spaces, self.name, self.salary);
        
        for subordinate in self.subordinates.values() {
            result.push_str(&format!("\n{}", subordinate.display(indent + 1)));
        }
        
        result
    }
}
```

## 9. 总结

组合模式通过以下方式提供形式化保证：

1. **统一接口**：叶子节点和组合节点实现相同的接口
2. **递归结构**：支持任意深度的嵌套结构
3. **类型安全**：通过 Rust 的类型系统确保操作的正确性
4. **扩展性**：支持动态添加和删除组件

该模式在 Rust 中的实现充分利用了 trait 系统和所有权系统的优势，提供了灵活且可扩展的树形结构管理。

---

**参考文献**：

1. Gamma, E., et al. "Design Patterns: Elements of Reusable Object-Oriented Software"
2. Pierce, B. C. "Types and Programming Languages"
3. Mac Lane, S. "Categories for the Working Mathematician"
