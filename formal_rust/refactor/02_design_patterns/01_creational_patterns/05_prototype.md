# 原型模式 (Prototype Pattern) - 形式化重构

## 目录 (Table of Contents)

1. [形式化定义 (Formal Definition)](#1-形式化定义-formal-definition)
2. [数学理论基础 (Mathematical Foundation)](#2-数学理论基础-mathematical-foundation)
3. [定理与证明 (Theorems and Proofs)](#3-定理与证明-theorems-and-proofs)
4. [Rust实现 (Rust Implementation)](#4-rust实现-rust-implementation)
5. [应用场景 (Application Scenarios)](#5-应用场景-application-scenarios)
6. [性能分析 (Performance Analysis)](#6-性能分析-performance-analysis)

---

## 1. 形式化定义 (Formal Definition)

### 1.1 原型模式四元组 (Prototype Pattern Quadruple)

**定义 1.1.1 (原型模式)**

设 $P = (N, I, S, R, C)$ 为原型模式，其中：

- $N = \{\text{"Prototype"}\}$ (模式名称)
- $I = \{\text{"通过克隆创建对象"}, \text{"避免重复初始化"}\}$ (意图描述)
- $S = \{\text{Prototype}, \text{ConcretePrototype}, \text{Clone}, \text{Client}\}$ (结构定义)
- $R = \{(\text{Prototype}, \text{clone}), (\text{ConcretePrototype}, \text{Prototype}), (\text{Client}, \text{Prototype})\}$ (关系映射)
- $C = \{\text{克隆一致性约束}, \text{深度复制约束}, \text{性能约束}\}$ (约束条件)

### 1.2 克隆操作定义 (Clone Operation Definition)

**定义 1.2.1 (浅克隆)**

设 $p$ 为原型对象，浅克隆操作 $\text{shallow\_clone}$ 定义为：

$$\text{shallow\_clone}(p) = p' \text{ where } \text{TypeOf}(p) = \text{TypeOf}(p')$$

**定义 1.2.2 (深克隆)**

设 $p$ 为原型对象，深克隆操作 $\text{deep\_clone}$ 定义为：

$$\text{deep\_clone}(p) = p' \text{ where } \forall x \in p, \text{Clone}(x) \in p'$$

---

## 2. 数学理论基础 (Mathematical Foundation)

### 2.1 克隆一致性理论 (Clone Consistency Theory)

**定义 2.1.1 (克隆等价性)**

两个对象 $p_1, p_2$ 是克隆等价的，记作 $p_1 \equiv p_2$，当且仅当：

$$\text{TypeOf}(p_1) = \text{TypeOf}(p_2) \land \text{State}(p_1) = \text{State}(p_2)$$

**定义 2.1.2 (克隆幂等性)**

克隆操作是幂等的，当且仅当：

$$\text{clone}(\text{clone}(p)) \equiv \text{clone}(p)$$

### 2.2 原型管理理论 (Prototype Management Theory)

**定义 2.2.1 (原型注册表)**

原型注册表 $\mathcal{R}$ 是一个映射：

$$\mathcal{R}: \text{String} \rightarrow \text{Prototype}$$

**定义 2.2.2 (原型查找)**

原型查找操作定义为：

$$\text{find\_prototype}(\mathcal{R}, name) = \mathcal{R}(name)$$

---

## 3. 定理与证明 (Theorems and Proofs)

### 3.1 克隆正确性定理 (Clone Correctness Theorem)

**定理 3.1.1 (克隆类型保持)**

对于任意原型对象 $p$，克隆操作保持类型不变：

$$\text{TypeOf}(\text{clone}(p)) = \text{TypeOf}(p)$$

**证明**:
根据定义 1.2.1，浅克隆操作保持类型不变。

根据定义 1.2.2，深克隆操作也保持类型不变。

因此，克隆操作保持类型不变。

**定理 3.1.2 (克隆状态一致性)**

对于任意原型对象 $p$，克隆对象的状态与原对象一致：

$$\text{State}(\text{clone}(p)) = \text{State}(p)$$

**证明**:
根据定义 2.1.1，克隆等价性要求状态一致。

克隆操作的目标是创建状态相同的对象。

因此，克隆状态与原对象一致。

**定理 3.1.3 (克隆幂等性)**

克隆操作满足幂等性：

$$\text{clone}(\text{clone}(p)) \equiv \text{clone}(p)$$

**证明**:
根据定义 2.1.2，克隆操作是幂等的。

多次克隆同一对象产生等价的结果。

因此，克隆操作满足幂等性。

### 3.2 性能分析定理 (Performance Analysis Theorem)

**定理 3.2.1 (克隆时间复杂度)**

浅克隆的时间复杂度为 $O(1)$，深克隆的时间复杂度为 $O(n)$，其中 $n$ 是对象的复杂度。

**证明**:
浅克隆只需要复制引用，时间为常数。

深克隆需要遍历对象的所有成员，时间为线性。

因此，时间复杂度分别为 $O(1)$ 和 $O(n)$。

**定理 3.2.2 (克隆空间复杂度)**

浅克隆的空间复杂度为 $O(1)$，深克隆的空间复杂度为 $O(n)$。

**证明**:
浅克隆只分配引用空间，空间为常数。

深克隆需要为所有成员分配空间，空间为线性。

因此，空间复杂度分别为 $O(1)$ 和 $O(n)$。

---

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现 (Basic Implementation)

```rust
use std::collections::HashMap;

/// 抽象原型
pub trait Prototype: Clone {
    fn clone_prototype(&self) -> Self;
    fn get_name(&self) -> &str;
}

/// 具体原型
#[derive(Debug, Clone)]
pub struct ConcretePrototype {
    name: String,
    data: Vec<String>,
    metadata: HashMap<String, String>,
}

impl ConcretePrototype {
    pub fn new(name: String) -> Self {
        ConcretePrototype {
            name,
            data: Vec::new(),
            metadata: HashMap::new(),
        }
    }

    pub fn add_data(&mut self, item: String) {
        self.data.push(item);
    }

    pub fn set_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    pub fn get_data(&self) -> &Vec<String> {
        &self.data
    }

    pub fn get_metadata(&self) -> &HashMap<String, String> {
        &self.metadata
    }
}

impl Prototype for ConcretePrototype {
    fn clone_prototype(&self) -> Self {
        self.clone()
    }

    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 原型管理器
pub struct PrototypeManager {
    prototypes: HashMap<String, Box<dyn Prototype>>,
}

impl PrototypeManager {
    pub fn new() -> Self {
        PrototypeManager {
            prototypes: HashMap::new(),
        }
    }

    pub fn add_prototype(&mut self, name: String, prototype: Box<dyn Prototype>) {
        self.prototypes.insert(name, prototype);
    }

    pub fn get_prototype(&self, name: &str) -> Option<Box<dyn Prototype>> {
        self.prototypes.get(name).map(|p| p.clone_prototype())
    }

    pub fn remove_prototype(&mut self, name: &str) -> Option<Box<dyn Prototype>> {
        self.prototypes.remove(name)
    }

    pub fn list_prototypes(&self) -> Vec<String> {
        self.prototypes.keys().cloned().collect()
    }
}
```

### 4.2 泛型原型实现 (Generic Prototype Implementation)

```rust
use std::collections::HashMap;

/// 泛型原型
pub trait GenericPrototype<T: Clone> {
    fn clone_prototype(&self) -> Self;
    fn get_data(&self) -> &T;
    fn set_data(&mut self, data: T);
}

/// 泛型具体原型
#[derive(Debug, Clone)]
pub struct GenericConcretePrototype<T: Clone> {
    name: String,
    data: T,
    version: u32,
}

impl<T: Clone> GenericConcretePrototype<T> {
    pub fn new(name: String, data: T) -> Self {
        GenericConcretePrototype {
            name,
            data,
            version: 1,
        }
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_version(&self) -> u32 {
        self.version
    }

    pub fn increment_version(&mut self) {
        self.version += 1;
    }
}

impl<T: Clone> GenericPrototype<T> for GenericConcretePrototype<T> {
    fn clone_prototype(&self) -> Self {
        GenericConcretePrototype {
            name: self.name.clone(),
            data: self.data.clone(),
            version: self.version + 1,
        }
    }

    fn get_data(&self) -> &T {
        &self.data
    }

    fn set_data(&mut self, data: T) {
        self.data = data;
        self.increment_version();
    }
}

/// 泛型原型管理器
pub struct GenericPrototypeManager<T: Clone> {
    prototypes: HashMap<String, Box<dyn GenericPrototype<T>>>,
}

impl<T: Clone> GenericPrototypeManager<T> {
    pub fn new() -> Self {
        GenericPrototypeManager {
            prototypes: HashMap::new(),
        }
    }

    pub fn add_prototype(&mut self, name: String, prototype: Box<dyn GenericPrototype<T>>) {
        self.prototypes.insert(name, prototype);
    }

    pub fn get_prototype(&self, name: &str) -> Option<Box<dyn GenericPrototype<T>>> {
        self.prototypes.get(name).map(|p| p.clone_prototype())
    }
}
```

### 4.3 深度克隆实现 (Deep Clone Implementation)

```rust
use std::collections::HashMap;

/// 支持深度克隆的原型
pub trait DeepClone {
    fn deep_clone(&self) -> Self;
}

/// 复杂原型对象
#[derive(Debug)]
pub struct ComplexPrototype {
    name: String,
    data: Vec<String>,
    nested: HashMap<String, Box<dyn DeepClone>>,
    metadata: HashMap<String, String>,
}

impl ComplexPrototype {
    pub fn new(name: String) -> Self {
        ComplexPrototype {
            name,
            data: Vec::new(),
            nested: HashMap::new(),
            metadata: HashMap::new(),
        }
    }

    pub fn add_data(&mut self, item: String) {
        self.data.push(item);
    }

    pub fn add_nested(&mut self, key: String, value: Box<dyn DeepClone>) {
        self.nested.insert(key, value);
    }

    pub fn set_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }
}

impl DeepClone for ComplexPrototype {
    fn deep_clone(&self) -> Self {
        let mut cloned = ComplexPrototype::new(self.name.clone());
        
        // 深度克隆数据
        cloned.data = self.data.clone();
        
        // 深度克隆嵌套对象
        for (key, value) in &self.nested {
            cloned.nested.insert(key.clone(), Box::new(value.deep_clone()));
        }
        
        // 深度克隆元数据
        cloned.metadata = self.metadata.clone();
        
        cloned
    }
}

/// 嵌套原型对象
#[derive(Debug)]
pub struct NestedPrototype {
    id: u32,
    content: String,
    children: Vec<Box<dyn DeepClone>>,
}

impl NestedPrototype {
    pub fn new(id: u32, content: String) -> Self {
        NestedPrototype {
            id,
            content,
            children: Vec::new(),
        }
    }

    pub fn add_child(&mut self, child: Box<dyn DeepClone>) {
        self.children.push(child);
    }
}

impl DeepClone for NestedPrototype {
    fn deep_clone(&self) -> Self {
        let mut cloned = NestedPrototype::new(self.id, self.content.clone());
        
        // 深度克隆子对象
        for child in &self.children {
            cloned.children.push(Box::new(child.deep_clone()));
        }
        
        cloned
    }
}
```

### 4.4 原型缓存实现 (Prototype Cache Implementation)

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

/// 原型缓存
pub struct PrototypeCache {
    cache: Arc<RwLock<HashMap<String, Arc<dyn Prototype>>>>,
    max_size: usize,
}

impl PrototypeCache {
    pub fn new(max_size: usize) -> Self {
        PrototypeCache {
            cache: Arc::new(RwLock::new(HashMap::new())),
            max_size,
        }
    }

    pub fn get_prototype(&self, name: &str) -> Option<Arc<dyn Prototype>> {
        let cache = self.cache.read().unwrap();
        cache.get(name).cloned()
    }

    pub fn store_prototype(&self, name: String, prototype: Arc<dyn Prototype>) -> bool {
        let mut cache = self.cache.write().unwrap();
        
        if cache.len() >= self.max_size && !cache.contains_key(&name) {
            return false; // 缓存已满
        }
        
        cache.insert(name, prototype);
        true
    }

    pub fn remove_prototype(&self, name: &str) -> Option<Arc<dyn Prototype>> {
        let mut cache = self.cache.write().unwrap();
        cache.remove(name)
    }

    pub fn clear(&self) {
        let mut cache = self.cache.write().unwrap();
        cache.clear();
    }

    pub fn size(&self) -> usize {
        let cache = self.cache.read().unwrap();
        cache.len()
    }
}

/// 原型工厂
pub struct PrototypeFactory {
    cache: PrototypeCache,
}

impl PrototypeFactory {
    pub fn new() -> Self {
        PrototypeFactory {
            cache: PrototypeCache::new(100),
        }
    }

    pub fn create_prototype(&self, name: &str) -> Option<Arc<dyn Prototype>> {
        // 首先尝试从缓存获取
        if let Some(cached) = self.cache.get_prototype(name) {
            return Some(cached);
        }

        // 如果缓存中没有，创建新的原型
        let prototype = self.create_new_prototype(name)?;
        
        // 存储到缓存
        let arc_prototype = Arc::new(prototype);
        self.cache.store_prototype(name.to_string(), arc_prototype.clone());
        
        Some(arc_prototype)
    }

    fn create_new_prototype(&self, name: &str) -> Option<ConcretePrototype> {
        match name {
            "default" => Some(ConcretePrototype::new("Default".to_string())),
            "template" => {
                let mut prototype = ConcretePrototype::new("Template".to_string());
                prototype.add_data("template_data".to_string());
                Some(prototype)
            }
            _ => None,
        }
    }
}
```

---

## 5. 应用场景 (Application Scenarios)

### 5.1 文档模板系统 (Document Template System)

```rust
use std::collections::HashMap;

/// 文档模板
#[derive(Debug, Clone)]
pub struct DocumentTemplate {
    title: String,
    content: String,
    styles: HashMap<String, String>,
    metadata: HashMap<String, String>,
}

impl DocumentTemplate {
    pub fn new(title: String, content: String) -> Self {
        DocumentTemplate {
            title,
            content,
            styles: HashMap::new(),
            metadata: HashMap::new(),
        }
    }

    pub fn add_style(&mut self, property: String, value: String) {
        self.styles.insert(property, value);
    }

    pub fn set_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    pub fn generate_document(&self, data: HashMap<String, String>) -> Document {
        let mut content = self.content.clone();
        
        // 替换模板变量
        for (key, value) in data {
            content = content.replace(&format!("{{{{{}}}}}", key), &value);
        }

        Document {
            title: self.title.clone(),
            content,
            styles: self.styles.clone(),
            metadata: self.metadata.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Document {
    pub title: String,
    pub content: String,
    pub styles: HashMap<String, String>,
    pub metadata: HashMap<String, String>,
}

/// 模板管理器
pub struct TemplateManager {
    templates: HashMap<String, DocumentTemplate>,
}

impl TemplateManager {
    pub fn new() -> Self {
        TemplateManager {
            templates: HashMap::new(),
        }
    }

    pub fn register_template(&mut self, name: String, template: DocumentTemplate) {
        self.templates.insert(name, template);
    }

    pub fn get_template(&self, name: &str) -> Option<DocumentTemplate> {
        self.templates.get(name).cloned()
    }

    pub fn create_document(&self, template_name: &str, data: HashMap<String, String>) -> Option<Document> {
        let template = self.get_template(template_name)?;
        Some(template.generate_document(data))
    }
}
```

### 5.2 游戏对象克隆系统 (Game Object Clone System)

```rust
use std::collections::HashMap;

/// 游戏对象原型
#[derive(Debug, Clone)]
pub struct GameObject {
    id: String,
    name: String,
    position: (f32, f32),
    properties: HashMap<String, String>,
    components: Vec<String>,
}

impl GameObject {
    pub fn new(id: String, name: String) -> Self {
        GameObject {
            id,
            name,
            position: (0.0, 0.0),
            properties: HashMap::new(),
            components: Vec::new(),
        }
    }

    pub fn set_position(&mut self, x: f32, y: f32) {
        self.position = (x, y);
    }

    pub fn add_property(&mut self, key: String, value: String) {
        self.properties.insert(key, value);
    }

    pub fn add_component(&mut self, component: String) {
        self.components.push(component);
    }

    pub fn clone_with_id(&self, new_id: String) -> Self {
        let mut cloned = self.clone();
        cloned.id = new_id;
        cloned
    }
}

/// 游戏对象工厂
pub struct GameObjectFactory {
    prototypes: HashMap<String, GameObject>,
}

impl GameObjectFactory {
    pub fn new() -> Self {
        GameObjectFactory {
            prototypes: HashMap::new(),
        }
    }

    pub fn register_prototype(&mut self, name: String, prototype: GameObject) {
        self.prototypes.insert(name, prototype);
    }

    pub fn create_object(&self, prototype_name: &str, id: String) -> Option<GameObject> {
        let prototype = self.prototypes.get(prototype_name)?;
        Some(prototype.clone_with_id(id))
    }

    pub fn create_objects(&self, prototype_name: &str, count: usize) -> Vec<GameObject> {
        let mut objects = Vec::new();
        
        for i in 0..count {
            if let Some(prototype) = self.prototypes.get(prototype_name) {
                let id = format!("{}_{}", prototype_name, i);
                objects.push(prototype.clone_with_id(id));
            }
        }
        
        objects
    }
}
```

### 5.3 配置对象克隆系统 (Configuration Object Clone System)

```rust
use std::collections::HashMap;

/// 配置原型
#[derive(Debug, Clone)]
pub struct ConfigPrototype {
    name: String,
    settings: HashMap<String, String>,
    nested_configs: HashMap<String, Box<ConfigPrototype>>,
    metadata: HashMap<String, String>,
}

impl ConfigPrototype {
    pub fn new(name: String) -> Self {
        ConfigPrototype {
            name,
            settings: HashMap::new(),
            nested_configs: HashMap::new(),
            metadata: HashMap::new(),
        }
    }

    pub fn set_setting(&mut self, key: String, value: String) {
        self.settings.insert(key, value);
    }

    pub fn add_nested_config(&mut self, name: String, config: ConfigPrototype) {
        self.nested_configs.insert(name, Box::new(config));
    }

    pub fn set_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    pub fn clone_with_modifications(&self, modifications: HashMap<String, String>) -> Self {
        let mut cloned = self.clone();
        
        for (key, value) in modifications {
            cloned.settings.insert(key, value);
        }
        
        cloned
    }
}

/// 配置管理器
pub struct ConfigManager {
    prototypes: HashMap<String, ConfigPrototype>,
}

impl ConfigManager {
    pub fn new() -> Self {
        ConfigManager {
            prototypes: HashMap::new(),
        }
    }

    pub fn register_prototype(&mut self, name: String, prototype: ConfigPrototype) {
        self.prototypes.insert(name, prototype);
    }

    pub fn create_config(&self, prototype_name: &str, modifications: HashMap<String, String>) -> Option<ConfigPrototype> {
        let prototype = self.prototypes.get(prototype_name)?;
        Some(prototype.clone_with_modifications(modifications))
    }
}
```

---

## 6. 性能分析 (Performance Analysis)

### 6.1 时间复杂度分析

**浅克隆**: $O(1)$

- 只复制引用，时间为常数

**深克隆**: $O(n)$

- 需要遍历所有成员，时间为线性

**原型查找**: $O(1)$

- 使用哈希表，平均时间为常数

### 6.2 空间复杂度分析

**浅克隆**: $O(1)$

- 只分配引用空间

**深克隆**: $O(n)$

- 需要为所有成员分配空间

**原型缓存**: $O(k)$

- k为缓存的原型数量

### 6.3 性能优化策略

**1. 对象池模式**

```rust
pub struct PrototypePool {
    prototypes: Vec<ConcretePrototype>,
}

impl PrototypePool {
    pub fn new(capacity: usize) -> Self {
        let mut prototypes = Vec::with_capacity(capacity);
        for i in 0..capacity {
            prototypes.push(ConcretePrototype::new(format!("prototype_{}", i)));
        }
        PrototypePool { prototypes }
    }

    pub fn acquire(&mut self) -> Option<ConcretePrototype> {
        self.prototypes.pop()
    }

    pub fn release(&mut self, prototype: ConcretePrototype) {
        if self.prototypes.len() < self.prototypes.capacity() {
            self.prototypes.push(prototype);
        }
    }
}
```

**2. 延迟克隆**

```rust
pub struct LazyPrototype {
    prototype: Option<ConcretePrototype>,
    factory: Box<dyn Fn() -> ConcretePrototype>,
}

impl LazyPrototype {
    pub fn new<F>(factory: F) -> Self 
    where 
        F: Fn() -> ConcretePrototype + 'static,
    {
        LazyPrototype {
            prototype: None,
            factory: Box::new(factory),
        }
    }

    pub fn get_prototype(&mut self) -> &ConcretePrototype {
        if self.prototype.is_none() {
            self.prototype = Some((self.factory)());
        }
        self.prototype.as_ref().unwrap()
    }

    pub fn clone_prototype(&mut self) -> ConcretePrototype {
        self.get_prototype().clone()
    }
}
```

---

## 总结

原型模式通过克隆现有对象来创建新对象，避免了重复的初始化过程。其形式化模型确保了克隆操作的正确性、一致性和性能，而Rust实现展示了模式在实际应用中的灵活性和效率。

该模式特别适用于：

- 需要频繁创建相似对象的场景
- 对象创建成本较高的应用
- 需要保持对象状态一致性的系统
- 支持对象模板和配置的场景

通过形式化分析和Rust实现，原型模式展现了其在软件架构中的重要价值，特别是在性能敏感的应用中。
