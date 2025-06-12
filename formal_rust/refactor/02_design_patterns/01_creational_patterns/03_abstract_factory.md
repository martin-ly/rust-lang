# 抽象工厂模式 (Abstract Factory Pattern) - 形式化重构

## 目录 (Table of Contents)

1. [形式化定义 (Formal Definition)](#1-形式化定义-formal-definition)
2. [数学理论基础 (Mathematical Foundation)](#2-数学理论基础-mathematical-foundation)
3. [定理与证明 (Theorems and Proofs)](#3-定理与证明-theorems-and-proofs)
4. [Rust实现 (Rust Implementation)](#4-rust实现-rust-implementation)
5. [应用场景 (Application Scenarios)](#5-应用场景-application-scenarios)

---

## 1. 形式化定义 (Formal Definition)

### 1.1 抽象工厂模式五元组 (Abstract Factory Pattern Quintuple)

-**定义 1.1.1 (抽象工厂模式)**

设 $AF = (N, I, S, R, C)$ 为抽象工厂模式，其中：

- $N = \{\text{"Abstract Factory"}\}$ (模式名称)
- $I = \{\text{"创建一系列相关对象"}, \text{"确保对象兼容性"}\}$ (意图描述)
- $S = \{\text{AbstractFactory}, \text{ConcreteFactory}, \text{AbstractProduct}, \text{ConcreteProduct}, \text{create\_product}\}$ (结构定义)
- $R = \{(\text{AbstractFactory}, \text{create\_product}), (\text{ConcreteFactory}, \text{AbstractProduct}), (\text{AbstractProduct}, \text{ConcreteProduct})\}$ (关系映射)
- $C = \{\text{产品族约束}, \text{兼容性约束}, \text{扩展性约束}\}$ (约束条件)

### 1.2 产品族定义 (Product Family Definition)

-**定义 1.2.1 (产品族)**

设 $\mathcal{F}$ 为产品族，满足：

$$\mathcal{F} = \{\text{Product}_1, \text{Product}_2, \ldots, \text{Product}_n\}$$

其中每个产品都是相关的。

-**定义 1.2.2 (产品族兼容性)**

产品族 $\mathcal{F}$ 是兼容的，当且仅当：

$$\forall \text{Product}_i, \text{Product}_j \in \mathcal{F}, \text{Compatible}(\text{Product}_i, \text{Product}_j)$$

---

## 2. 数学理论基础 (Mathematical Foundation)

### 2.1 产品族理论 (Product Family Theory)

-**定义 2.1.1 (产品族一致性)**

抽象工厂模式满足产品族一致性，当且仅当：

$$\forall f \in \text{ConcreteFactory}, \forall p_1, p_2 \in \text{create\_products}(f), \text{Compatible}(p_1, p_2)$$

-**定义 2.1.2 (工厂抽象性)**

抽象工厂模式满足工厂抽象性，当且仅当：

$$\text{AbstractFactory} \not\hookrightarrow \text{ConcreteProduct}$$

### 2.2 兼容性理论 (Compatibility Theory)

-**定义 2.2.1 (产品兼容性)**

两个产品 $p_1, p_2$ 是兼容的，当且仅当：

$$\text{Interface}(p_1) \cap \text{Interface}(p_2) \neq \emptyset$$

---

## 3. 定理与证明 (Theorems and Proofs)

### 3.1 产品族一致性定理 (Product Family Consistency Theorem)

**定理 3.1.1 (产品族一致性)**

对于任意抽象工厂模式 $AF$，同一工厂创建的产品是兼容的。

**证明**:
设 $f \in \text{ConcreteFactory}$ 是具体工厂。

根据定义 1.2.2，产品族 $\mathcal{F}$ 是兼容的。

因此，$f$ 创建的所有产品都满足兼容性约束。

**定理 3.1.2 (工厂抽象性)**

抽象工厂模式满足依赖倒置原则。

**证明**:
在抽象工厂模式中：

- 客户端依赖于 `AbstractFactory` 抽象
- 具体工厂实现 `AbstractFactory` 接口
- 两者都依赖于抽象，而不是具体实现

因此，满足依赖倒置原则。

---

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现 (Basic Implementation)

```rust
/// 抽象产品 A
pub trait AbstractProductA {
    fn operation_a(&self) -> String;
}

/// 抽象产品 B
pub trait AbstractProductB {
    fn operation_b(&self) -> String;
}

/// 具体产品 A1
pub struct ConcreteProductA1;

impl AbstractProductA for ConcreteProductA1 {
    fn operation_a(&self) -> String {
        "ConcreteProductA1: operation A".to_string()
    }
}

/// 具体产品 A2
pub struct ConcreteProductA2;

impl AbstractProductA for ConcreteProductA2 {
    fn operation_a(&self) -> String {
        "ConcreteProductA2: operation A".to_string()
    }
}

/// 具体产品 B1
pub struct ConcreteProductB1;

impl AbstractProductB for ConcreteProductB1 {
    fn operation_b(&self) -> String {
        "ConcreteProductB1: operation B".to_string()
    }
}

/// 具体产品 B2
pub struct ConcreteProductB2;

impl AbstractProductB for ConcreteProductB2 {
    fn operation_b(&self) -> String {
        "ConcreteProductB2: operation B".to_string()
    }
}

/// 抽象工厂
pub trait AbstractFactory {
    fn create_product_a(&self) -> Box<dyn AbstractProductA>;
    fn create_product_b(&self) -> Box<dyn AbstractProductB>;
}

/// 具体工厂 1
pub struct ConcreteFactory1;

impl AbstractFactory for ConcreteFactory1 {
    fn create_product_a(&self) -> Box<dyn AbstractProductA> {
        Box::new(ConcreteProductA1)
    }

    fn create_product_b(&self) -> Box<dyn AbstractProductB> {
        Box::new(ConcreteProductB1)
    }
}

/// 具体工厂 2
pub struct ConcreteFactory2;

impl AbstractFactory for ConcreteFactory2 {
    fn create_product_a(&self) -> Box<dyn AbstractProductA> {
        Box::new(ConcreteProductA2)
    }

    fn create_product_b(&self) -> Box<dyn AbstractProductB> {
        Box::new(ConcreteProductB2)
    }
}
```

### 4.2 泛型抽象工厂实现 (Generic Abstract Factory Implementation)

```rust
use std::collections::HashMap;

/// 泛型抽象产品
pub trait GenericProduct {
    fn get_id(&self) -> String;
    fn get_config(&self) -> HashMap<String, String>;
    fn execute(&self) -> Result<String, String>;
}

/// 泛型抽象工厂
pub trait GenericAbstractFactory<P: GenericProduct> {
    fn create_product(&self, product_type: &str) -> Option<Box<P>>;
    fn get_supported_types(&self) -> Vec<String>;
}

/// 具体泛型产品
pub struct GenericConcreteProduct {
    id: String,
    product_type: String,
    config: HashMap<String, String>,
}

impl GenericConcreteProduct {
    pub fn new(id: String, product_type: String, config: HashMap<String, String>) -> Self {
        GenericConcreteProduct {
            id,
            product_type,
            config,
        }
    }
}

impl GenericProduct for GenericConcreteProduct {
    fn get_id(&self) -> String {
        self.id.clone()
    }

    fn get_config(&self) -> HashMap<String, String> {
        self.config.clone()
    }

    fn execute(&self) -> Result<String, String> {
        Ok(format!("Executing {} with id: {}", self.product_type, self.id))
    }
}

/// 具体泛型工厂
pub struct GenericConcreteFactory {
    factory_id: String,
    supported_types: Vec<String>,
}

impl GenericConcreteFactory {
    pub fn new(factory_id: String, supported_types: Vec<String>) -> Self {
        GenericConcreteFactory {
            factory_id,
            supported_types,
        }
    }
}

impl GenericAbstractFactory<GenericConcreteProduct> for GenericConcreteFactory {
    fn create_product(&self, product_type: &str) -> Option<Box<GenericConcreteProduct>> {
        if self.supported_types.contains(&product_type.to_string()) {
            let mut config = HashMap::new();
            config.insert("factory_id".to_string(), self.factory_id.clone());
            config.insert("product_type".to_string(), product_type.to_string());
            
            Some(Box::new(GenericConcreteProduct::new(
                format!("{}_{}", self.factory_id, product_type),
                product_type.to_string(),
                config,
            )))
        } else {
            None
        }
    }

    fn get_supported_types(&self) -> Vec<String> {
        self.supported_types.clone()
    }
}
```

### 4.3 应用场景实现 (Application Scenarios Implementation)

```rust
/// GUI 组件抽象
pub trait Button {
    fn render(&self) -> String;
    fn click(&self) -> String;
}

pub trait Checkbox {
    fn render(&self) -> String;
    fn check(&self) -> String;
}

/// Windows GUI 组件
pub struct WindowsButton;

impl Button for WindowsButton {
    fn render(&self) -> String {
        "Windows Button rendered".to_string()
    }

    fn click(&self) -> String {
        "Windows Button clicked".to_string()
    }
}

pub struct WindowsCheckbox;

impl Checkbox for WindowsCheckbox {
    fn render(&self) -> String {
        "Windows Checkbox rendered".to_string()
    }

    fn check(&self) -> String {
        "Windows Checkbox checked".to_string()
    }
}

/// macOS GUI 组件
pub struct MacOSButton;

impl Button for MacOSButton {
    fn render(&self) -> String {
        "macOS Button rendered".to_string()
    }

    fn click(&self) -> String {
        "macOS Button clicked".to_string()
    }
}

pub struct MacOSCheckbox;

impl Checkbox for MacOSCheckbox {
    fn render(&self) -> String {
        "macOS Checkbox rendered".to_string()
    }

    fn check(&self) -> String {
        "macOS Checkbox checked".to_string()
    }
}

/// GUI 工厂抽象
pub trait GUIFactory {
    fn create_button(&self) -> Box<dyn Button>;
    fn create_checkbox(&self) -> Box<dyn Checkbox>;
}

/// Windows GUI 工厂
pub struct WindowsGUIFactory;

impl GUIFactory for WindowsGUIFactory {
    fn create_button(&self) -> Box<dyn Button> {
        Box::new(WindowsButton)
    }

    fn create_checkbox(&self) -> Box<dyn Checkbox> {
        Box::new(WindowsCheckbox)
    }
}

/// macOS GUI 工厂
pub struct MacOSGUIFactory;

impl GUIFactory for MacOSGUIFactory {
    fn create_button(&self) -> Box<dyn Button> {
        Box::new(MacOSButton)
    }

    fn create_checkbox(&self) -> Box<dyn Checkbox> {
        Box::new(MacOSCheckbox)
    }
}

/// 应用程序
pub struct Application {
    factory: Box<dyn GUIFactory>,
}

impl Application {
    pub fn new(factory: Box<dyn GUIFactory>) -> Self {
        Application { factory }
    }

    pub fn create_ui(&self) -> String {
        let button = self.factory.create_button();
        let checkbox = self.factory.create_checkbox();
        
        format!("{} -> {}", button.render(), checkbox.render())
    }
}
```

### 4.4 测试实现 (Test Implementation)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abstract_factory() {
        let factory1 = ConcreteFactory1;
        let factory2 = ConcreteFactory2;

        let product_a1 = factory1.create_product_a();
        let product_b1 = factory1.create_product_b();
        let product_a2 = factory2.create_product_a();
        let product_b2 = factory2.create_product_b();

        assert!(product_a1.operation_a().contains("A1"));
        assert!(product_b1.operation_b().contains("B1"));
        assert!(product_a2.operation_a().contains("A2"));
        assert!(product_b2.operation_b().contains("B2"));
    }

    #[test]
    fn test_generic_abstract_factory() {
        let factory = GenericConcreteFactory::new(
            "TestFactory".to_string(),
            vec!["Type1".to_string(), "Type2".to_string()],
        );

        let product1 = factory.create_product("Type1").unwrap();
        let product2 = factory.create_product("Type2").unwrap();
        let product3 = factory.create_product("Type3");

        assert!(product1.get_id().contains("TestFactory"));
        assert!(product2.get_id().contains("TestFactory"));
        assert!(product3.is_none());

        let supported_types = factory.get_supported_types();
        assert_eq!(supported_types.len(), 2);
        assert!(supported_types.contains(&"Type1".to_string()));
        assert!(supported_types.contains(&"Type2".to_string()));
    }

    #[test]
    fn test_gui_factory() {
        let windows_factory = WindowsGUIFactory;
        let macos_factory = MacOSGUIFactory;

        let windows_button = windows_factory.create_button();
        let windows_checkbox = windows_factory.create_checkbox();
        let macos_button = macos_factory.create_button();
        let macos_checkbox = macos_factory.create_checkbox();

        assert!(windows_button.render().contains("Windows"));
        assert!(windows_checkbox.render().contains("Windows"));
        assert!(macos_button.render().contains("macOS"));
        assert!(macos_checkbox.render().contains("macOS"));
    }

    #[test]
    fn test_application() {
        let windows_app = Application::new(Box::new(WindowsGUIFactory));
        let macos_app = Application::new(Box::new(MacOSGUIFactory));

        let windows_ui = windows_app.create_ui();
        let macos_ui = macos_app.create_ui();

        assert!(windows_ui.contains("Windows"));
        assert!(macos_ui.contains("macOS"));
    }
}
```

---

## 5. 应用场景 (Application Scenarios)

### 5.1 GUI 框架 (GUI Framework)

抽象工厂模式在GUI框架中的应用：

- 不同操作系统的GUI组件
- 确保组件风格一致性
- 支持主题切换

### 5.2 数据库访问 (Database Access)

```rust
/// 数据库连接抽象
pub trait DatabaseConnection {
    fn connect(&self) -> Result<String, String>;
    fn execute_query(&self, query: &str) -> Result<String, String>;
}

/// 数据库查询抽象
pub trait DatabaseQuery {
    fn build_query(&self) -> String;
    fn execute(&self) -> Result<String, String>;
}

/// MySQL 工厂
pub struct MySQLFactory;

impl MySQLFactory {
    pub fn create_connection(&self) -> Box<dyn DatabaseConnection> {
        Box::new(MySQLConnection)
    }

    pub fn create_query(&self) -> Box<dyn DatabaseQuery> {
        Box::new(MySQLQuery)
    }
}

/// PostgreSQL 工厂
pub struct PostgreSQLFactory;

impl PostgreSQLFactory {
    pub fn create_connection(&self) -> Box<dyn DatabaseConnection> {
        Box::new(PostgreSQLConnection)
    }

    pub fn create_query(&self) -> Box<dyn DatabaseQuery> {
        Box::new(PostgreSQLQuery)
    }
}
```

### 5.3 游戏引擎 (Game Engine)

```rust
/// 游戏对象抽象
pub trait GameObject {
    fn update(&self) -> String;
    fn render(&self) -> String;
}

/// 游戏世界抽象
pub trait GameWorld {
    fn add_object(&mut self, object: Box<dyn GameObject>);
    fn update_world(&self) -> String;
}

/// 2D 游戏工厂
pub struct Game2DFactory;

impl Game2DFactory {
    pub fn create_game_object(&self) -> Box<dyn GameObject> {
        Box::new(GameObject2D)
    }

    pub fn create_game_world(&self) -> Box<dyn GameWorld> {
        Box::new(GameWorld2D)
    }
}

/// 3D 游戏工厂
pub struct Game3DFactory;

impl Game3DFactory {
    pub fn create_game_object(&self) -> Box<dyn GameObject> {
        Box::new(GameObject3D)
    }

    pub fn create_game_world(&self) -> Box<dyn GameWorld> {
        Box::new(GameWorld3D)
    }
}
```

---

## 6. 总结 (Summary)

### 6.1 设计模式特性 (Pattern Characteristics)

1. **产品族一致性**: 确保相关产品的兼容性
2. **工厂抽象性**: 客户端不依赖具体产品
3. **扩展性**: 易于添加新的产品族
4. **封装性**: 封装产品创建逻辑

### 6.2 实现要点 (Implementation Points)

1. **抽象产品**: 定义产品接口
2. **具体产品**: 实现具体产品类
3. **抽象工厂**: 定义工厂接口
4. **具体工厂**: 实现具体工厂类

### 6.3 使用建议 (Usage Recommendations)

1. **适用场景**: 需要创建相关对象族、确保对象兼容性
2. **注意事项**: 避免过度设计简单对象创建
3. **性能考虑**: 创建开销小，但增加了抽象层
4. **测试策略**: 易于进行单元测试和模拟

---

**文档版本**: 1.0
**最后更新**: 2024-12-19
**状态**: 完成
