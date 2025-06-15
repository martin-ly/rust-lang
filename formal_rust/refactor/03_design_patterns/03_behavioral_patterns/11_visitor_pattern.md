# 访问者模式 (Visitor Pattern) - 形式化重构

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

访问者模式是一种行为型设计模式，它允许在不改变类的前提下定义新的操作。访问者模式将算法与对象结构分离，使得算法可以独立于对象结构而变化。

### 1.2 模式特征

- **操作分离**：将操作从对象结构中分离出来
- **双重分发**：支持基于对象类型和访问者类型的双重分发
- **开闭原则**：对扩展开放，对修改封闭
- **类型安全**：编译时类型检查

## 2. 形式化定义

### 2.1 访问者模式五元组

**定义2.1 (访问者模式五元组)**
设 $V = (E, V, A, D, R)$ 为一个访问者模式，其中：

- $E = \{e_1, e_2, ..., e_n\}$ 是元素集合
- $V = \{v_1, v_2, ..., v_m\}$ 是访问者集合
- $A = \{a_1, a_2, ..., a_k\}$ 是操作集合
- $D = \{d_1, d_2, ..., d_l\}$ 是数据集合
- $R = \{r_1, r_2, ..., r_p\}$ 是结果集合

### 2.2 访问者接口定义

**定义2.2 (访问者接口)**
访问者接口 $I_{vis}$ 定义为：

$$I_{vis} = \{\text{visit}(e: E) \rightarrow R, \text{visitAll}(E: [E]) \rightarrow [R]\}$$

### 2.3 元素接口定义

**定义2.3 (元素接口)**
元素接口 $I_{elem}$ 定义为：

$$I_{elem} = \{\text{accept}(v: V) \rightarrow R, \text{getType}() \rightarrow \text{Type}\}$$

### 2.4 双重分发函数

**定义2.4 (双重分发函数)**
双重分发函数 $f_D: E \times V \rightarrow R$ 定义为：

$$f_D(e, v) = e.\text{accept}(v) = v.\text{visit}(e)$$

## 3. 数学理论

### 3.1 双重分发理论

**定义3.1 (双重分发)**
双重分发机制定义为：

$$\text{dispatch}(e, v) = \text{dispatch}_1(e) \circ \text{dispatch}_2(v)$$

其中 $\circ$ 表示函数组合。

### 3.2 访问者完整性理论

**定义3.2 (访问者完整性)**
访问者 $v$ 对于元素集合 $E$ 是完整的，当且仅当：

$$\forall e \in E: \exists \text{visit}_e \in v$$

### 3.3 操作分离理论

**定义3.3 (操作分离)**
操作 $A$ 与元素 $E$ 分离，当且仅当：

$$A \cap E = \emptyset \land \text{independent}(A, E)$$

### 3.4 类型安全理论

**定义3.4 (类型安全)**
访问者模式是类型安全的，当且仅当：

$$\forall e \in E, v \in V: \text{type}(e) \subseteq \text{domain}(v)$$

## 4. 核心定理

### 4.1 双重分发正确性定理

**定理4.1 (双重分发正确性)**
如果双重分发机制正确实现，则访问操作是确定的：

$$\text{correctDispatch}(e, v) \Rightarrow f_D(e, v) \text{ is deterministic}$$

**证明：**

1. 根据定义2.4，双重分发函数是确定的
2. 元素类型和访问者类型都是确定的
3. 双重分发正确性定理得证。

### 4.2 访问者完整性定理

**定理4.2 (访问者完整性)**
如果访问者实现了所有元素的访问方法，则访问是完整的：

$$\forall e \in E: \text{hasVisitMethod}(v, e) \Rightarrow \text{complete}(v, E)$$

**证明：**

1. 根据定义3.2，访问者完整性要求所有元素都有对应的访问方法
2. 如果所有元素都有访问方法，则访问是完整的
3. 访问者完整性定理得证。

### 4.3 操作分离定理

**定理4.3 (操作分离)**
如果操作与元素分离，则新操作可以独立添加：

$$\text{separated}(A, E) \Rightarrow \text{extensible}(A)$$

**证明：**

1. 根据定义3.3，操作与元素分离
2. 新操作不依赖于元素结构
3. 操作分离定理得证。

### 4.4 类型安全定理

**定理4.4 (类型安全)**
如果访问者模式是类型安全的，则运行时类型错误不会发生：

$$\text{typeSafe}(V) \Rightarrow \neg \text{runtimeTypeError}()$$

**证明：**

1. 根据定义3.4，类型安全保证类型匹配
2. 编译时类型检查防止运行时错误
3. 类型安全定理得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;

// 访问者trait
pub trait Visitor: fmt::Display {
    fn visit_number(&self, number: &NumberExpression) -> String;
    fn visit_variable(&self, variable: &VariableExpression) -> String;
    fn visit_add(&self, add: &AddExpression) -> String;
    fn visit_subtract(&self, subtract: &SubtractExpression) -> String;
    fn visit_multiply(&self, multiply: &MultiplyExpression) -> String;
    fn visit_divide(&self, divide: &DivideExpression) -> String;
}

// 表达式trait
pub trait Expression: fmt::Display {
    fn accept(&self, visitor: &dyn Visitor) -> String;
}

// 具体表达式：数字
pub struct NumberExpression {
    value: i32,
}

impl NumberExpression {
    pub fn new(value: i32) -> Self {
        NumberExpression { value }
    }
    
    pub fn get_value(&self) -> i32 {
        self.value
    }
}

impl fmt::Display for NumberExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Number({})", self.value)
    }
}

impl Expression for NumberExpression {
    fn accept(&self, visitor: &dyn Visitor) -> String {
        visitor.visit_number(self)
    }
}

// 具体表达式：变量
pub struct VariableExpression {
    name: String,
}

impl VariableExpression {
    pub fn new(name: String) -> Self {
        VariableExpression { name }
    }
    
    pub fn get_name(&self) -> &str {
        &self.name
    }
}

impl fmt::Display for VariableExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Variable({})", self.name)
    }
}

impl Expression for VariableExpression {
    fn accept(&self, visitor: &dyn Visitor) -> String {
        visitor.visit_variable(self)
    }
}

// 具体表达式：加法
pub struct AddExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl AddExpression {
    pub fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        AddExpression { left, right }
    }
    
    pub fn get_left(&self) -> &Box<dyn Expression> {
        &self.left
    }
    
    pub fn get_right(&self) -> &Box<dyn Expression> {
        &self.right
    }
}

impl fmt::Display for AddExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Add({} + {})", self.left, self.right)
    }
}

impl Expression for AddExpression {
    fn accept(&self, visitor: &dyn Visitor) -> String {
        visitor.visit_add(self)
    }
}

// 具体表达式：减法
pub struct SubtractExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl SubtractExpression {
    pub fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        SubtractExpression { left, right }
    }
    
    pub fn get_left(&self) -> &Box<dyn Expression> {
        &self.left
    }
    
    pub fn get_right(&self) -> &Box<dyn Expression> {
        &self.right
    }
}

impl fmt::Display for SubtractExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Subtract({} - {})", self.left, self.right)
    }
}

impl Expression for SubtractExpression {
    fn accept(&self, visitor: &dyn Visitor) -> String {
        visitor.visit_subtract(self)
    }
}

// 具体表达式：乘法
pub struct MultiplyExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl MultiplyExpression {
    pub fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        MultiplyExpression { left, right }
    }
    
    pub fn get_left(&self) -> &Box<dyn Expression> {
        &self.left
    }
    
    pub fn get_right(&self) -> &Box<dyn Expression> {
        &self.right
    }
}

impl fmt::Display for MultiplyExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Multiply({} * {})", self.left, self.right)
    }
}

impl Expression for MultiplyExpression {
    fn accept(&self, visitor: &dyn Visitor) -> String {
        visitor.visit_multiply(self)
    }
}

// 具体表达式：除法
pub struct DivideExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl DivideExpression {
    pub fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        DivideExpression { left, right }
    }
    
    pub fn get_left(&self) -> &Box<dyn Expression> {
        &self.left
    }
    
    pub fn get_right(&self) -> &Box<dyn Expression> {
        &self.right
    }
}

impl fmt::Display for DivideExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Divide({} / {})", self.left, self.right)
    }
}

impl Expression for DivideExpression {
    fn accept(&self, visitor: &dyn Visitor) -> String {
        visitor.visit_divide(self)
    }
}

// 具体访问者：求值访问者
pub struct EvaluateVisitor {
    variables: std::collections::HashMap<String, i32>,
}

impl EvaluateVisitor {
    pub fn new() -> Self {
        EvaluateVisitor {
            variables: std::collections::HashMap::new(),
        }
    }
    
    pub fn set_variable(&mut self, name: String, value: i32) {
        self.variables.insert(name, value);
    }
    
    pub fn get_variables(&self) -> &std::collections::HashMap<String, i32> {
        &self.variables
    }
}

impl fmt::Display for EvaluateVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EvaluateVisitor(variables: {:?})", self.variables)
    }
}

impl Visitor for EvaluateVisitor {
    fn visit_number(&self, number: &NumberExpression) -> String {
        number.get_value().to_string()
    }
    
    fn visit_variable(&self, variable: &VariableExpression) -> String {
        match self.variables.get(variable.get_name()) {
            Some(value) => value.to_string(),
            None => format!("Undefined variable: {}", variable.get_name()),
        }
    }
    
    fn visit_add(&self, add: &AddExpression) -> String {
        let left_result = add.get_left().accept(self);
        let right_result = add.get_right().accept(self);
        
        if let (Ok(left), Ok(right)) = (left_result.parse::<i32>(), right_result.parse::<i32>()) {
            (left + right).to_string()
        } else {
            format!("Error: Cannot evaluate {} + {}", left_result, right_result)
        }
    }
    
    fn visit_subtract(&self, subtract: &SubtractExpression) -> String {
        let left_result = subtract.get_left().accept(self);
        let right_result = subtract.get_right().accept(self);
        
        if let (Ok(left), Ok(right)) = (left_result.parse::<i32>(), right_result.parse::<i32>()) {
            (left - right).to_string()
        } else {
            format!("Error: Cannot evaluate {} - {}", left_result, right_result)
        }
    }
    
    fn visit_multiply(&self, multiply: &MultiplyExpression) -> String {
        let left_result = multiply.get_left().accept(self);
        let right_result = multiply.get_right().accept(self);
        
        if let (Ok(left), Ok(right)) = (left_result.parse::<i32>(), right_result.parse::<i32>()) {
            (left * right).to_string()
        } else {
            format!("Error: Cannot evaluate {} * {}", left_result, right_result)
        }
    }
    
    fn visit_divide(&self, divide: &DivideExpression) -> String {
        let left_result = divide.get_left().accept(self);
        let right_result = divide.get_right().accept(self);
        
        if let (Ok(left), Ok(right)) = (left_result.parse::<i32>(), right_result.parse::<i32>()) {
            if right != 0 {
                (left / right).to_string()
            } else {
                "Error: Division by zero".to_string()
            }
        } else {
            format!("Error: Cannot evaluate {} / {}", left_result, right_result)
        }
    }
}

// 具体访问者：打印访问者
pub struct PrintVisitor;

impl PrintVisitor {
    pub fn new() -> Self {
        PrintVisitor
    }
}

impl fmt::Display for PrintVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PrintVisitor")
    }
}

impl Visitor for PrintVisitor {
    fn visit_number(&self, number: &NumberExpression) -> String {
        number.get_value().to_string()
    }
    
    fn visit_variable(&self, variable: &VariableExpression) -> String {
        variable.get_name().to_string()
    }
    
    fn visit_add(&self, add: &AddExpression) -> String {
        let left = add.get_left().accept(self);
        let right = add.get_right().accept(self);
        format!("({} + {})", left, right)
    }
    
    fn visit_subtract(&self, subtract: &SubtractExpression) -> String {
        let left = subtract.get_left().accept(self);
        let right = subtract.get_right().accept(self);
        format!("({} - {})", left, right)
    }
    
    fn visit_multiply(&self, multiply: &MultiplyExpression) -> String {
        let left = multiply.get_left().accept(self);
        let right = multiply.get_right().accept(self);
        format!("({} * {})", left, right)
    }
    
    fn visit_divide(&self, divide: &DivideExpression) -> String {
        let left = divide.get_left().accept(self);
        let right = divide.get_right().accept(self);
        format!("({} / {})", left, right)
    }
}

// 具体访问者：类型检查访问者
pub struct TypeCheckVisitor {
    variables: std::collections::HashMap<String, String>,
}

impl TypeCheckVisitor {
    pub fn new() -> Self {
        TypeCheckVisitor {
            variables: std::collections::HashMap::new(),
        }
    }
    
    pub fn declare_variable(&mut self, name: String, var_type: String) {
        self.variables.insert(name, var_type);
    }
    
    pub fn get_variables(&self) -> &std::collections::HashMap<String, String> {
        &self.variables
    }
}

impl fmt::Display for TypeCheckVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeCheckVisitor(variables: {:?})", self.variables)
    }
}

impl Visitor for TypeCheckVisitor {
    fn visit_number(&self, _number: &NumberExpression) -> String {
        "int".to_string()
    }
    
    fn visit_variable(&self, variable: &VariableExpression) -> String {
        match self.variables.get(variable.get_name()) {
            Some(var_type) => var_type.clone(),
            None => format!("Undefined variable: {}", variable.get_name()),
        }
    }
    
    fn visit_add(&self, add: &AddExpression) -> String {
        let left_type = add.get_left().accept(self);
        let right_type = add.get_right().accept(self);
        
        if left_type == "int" && right_type == "int" {
            "int".to_string()
        } else {
            format!("Type error: Cannot add {} and {}", left_type, right_type)
        }
    }
    
    fn visit_subtract(&self, subtract: &SubtractExpression) -> String {
        let left_type = subtract.get_left().accept(self);
        let right_type = subtract.get_right().accept(self);
        
        if left_type == "int" && right_type == "int" {
            "int".to_string()
        } else {
            format!("Type error: Cannot subtract {} and {}", left_type, right_type)
        }
    }
    
    fn visit_multiply(&self, multiply: &MultiplyExpression) -> String {
        let left_type = multiply.get_left().accept(self);
        let right_type = multiply.get_right().accept(self);
        
        if left_type == "int" && right_type == "int" {
            "int".to_string()
        } else {
            format!("Type error: Cannot multiply {} and {}", left_type, right_type)
        }
    }
    
    fn visit_divide(&self, divide: &DivideExpression) -> String {
        let left_type = divide.get_left().accept(self);
        let right_type = divide.get_right().accept(self);
        
        if left_type == "int" && right_type == "int" {
            "int".to_string()
        } else {
            format!("Type error: Cannot divide {} and {}", left_type, right_type)
        }
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;

// 泛型访问者trait
pub trait GenericVisitor<T, R>: fmt::Display {
    fn visit_element(&self, element: &T) -> R;
    fn visit_all(&self, elements: &[T]) -> Vec<R> {
        elements.iter().map(|e| self.visit_element(e)).collect()
    }
}

// 泛型元素trait
pub trait GenericElement<T, R>: fmt::Display {
    fn accept(&self, visitor: &dyn GenericVisitor<T, R>) -> R;
}

// 文档元素
#[derive(Debug, Clone)]
pub struct DocumentElement {
    element_type: String,
    content: String,
    attributes: std::collections::HashMap<String, String>,
}

impl DocumentElement {
    pub fn new(element_type: String, content: String) -> Self {
        DocumentElement {
            element_type,
            content,
            attributes: std::collections::HashMap::new(),
        }
    }
    
    pub fn add_attribute(&mut self, key: String, value: String) {
        self.attributes.insert(key, value);
    }
    
    pub fn get_element_type(&self) -> &str {
        &self.element_type
    }
    
    pub fn get_content(&self) -> &str {
        &self.content
    }
    
    pub fn get_attributes(&self) -> &std::collections::HashMap<String, String> {
        &self.attributes
    }
}

impl fmt::Display for DocumentElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DocumentElement(type: {}, content: '{}')", 
               self.element_type, self.content)
    }
}

impl GenericElement<DocumentElement, String> for DocumentElement {
    fn accept(&self, visitor: &dyn GenericVisitor<DocumentElement, String>) -> String {
        visitor.visit_element(self)
    }
}

// HTML导出访问者
pub struct HtmlExportVisitor;

impl HtmlExportVisitor {
    pub fn new() -> Self {
        HtmlExportVisitor
    }
}

impl fmt::Display for HtmlExportVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "HtmlExportVisitor")
    }
}

impl GenericVisitor<DocumentElement, String> for HtmlExportVisitor {
    fn visit_element(&self, element: &DocumentElement) -> String {
        let mut html = format!("<{}", element.get_element_type());
        
        // 添加属性
        for (key, value) in element.get_attributes() {
            html.push_str(&format!(" {}=\"{}\"", key, value));
        }
        
        html.push('>');
        html.push_str(element.get_content());
        html.push_str(&format!("</{}>", element.get_element_type()));
        
        html
    }
}

// JSON导出访问者
pub struct JsonExportVisitor;

impl JsonExportVisitor {
    pub fn new() -> Self {
        JsonExportVisitor
    }
}

impl fmt::Display for JsonExportVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "JsonExportVisitor")
    }
}

impl GenericVisitor<DocumentElement, String> for JsonExportVisitor {
    fn visit_element(&self, element: &DocumentElement) -> String {
        let mut json = format!("{{\"type\": \"{}\", \"content\": \"{}\"", 
                              element.get_element_type(), element.get_content());
        
        if !element.get_attributes().is_empty() {
            json.push_str(", \"attributes\": {");
            let attrs: Vec<String> = element.get_attributes()
                .iter()
                .map(|(k, v)| format!("\"{}\": \"{}\"", k, v))
                .collect();
            json.push_str(&attrs.join(", "));
            json.push('}');
        }
        
        json.push('}');
        json
    }
}

// XML导出访问者
pub struct XmlExportVisitor;

impl XmlExportVisitor {
    pub fn new() -> Self {
        XmlExportVisitor
    }
}

impl fmt::Display for XmlExportVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "XmlExportVisitor")
    }
}

impl GenericVisitor<DocumentElement, String> for XmlExportVisitor {
    fn visit_element(&self, element: &DocumentElement) -> String {
        let mut xml = format!("<{}", element.get_element_type());
        
        // 添加属性
        for (key, value) in element.get_attributes() {
            xml.push_str(&format!(" {}=\"{}\"", key, value));
        }
        
        xml.push('>');
        xml.push_str(element.get_content());
        xml.push_str(&format!("</{}>", element.get_element_type()));
        
        xml
    }
}
```

### 5.3 应用场景实现

```rust
// 文件系统访问者
pub trait FileSystemVisitor: fmt::Display {
    fn visit_file(&self, file: &File) -> String;
    fn visit_directory(&self, directory: &Directory) -> String;
    fn visit_symlink(&self, symlink: &Symlink) -> String;
}

// 文件系统元素
pub trait FileSystemElement: fmt::Display {
    fn accept(&self, visitor: &dyn FileSystemVisitor) -> String;
    fn get_name(&self) -> &str;
    fn get_size(&self) -> u64;
    fn get_permissions(&self) -> u32;
}

// 文件
pub struct File {
    name: String,
    size: u64,
    permissions: u32,
    content: String,
}

impl File {
    pub fn new(name: String, size: u64, permissions: u32, content: String) -> Self {
        File {
            name,
            size,
            permissions,
            content,
        }
    }
    
    pub fn get_content(&self) -> &str {
        &self.content
    }
}

impl fmt::Display for File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "File({}, {} bytes)", self.name, self.size)
    }
}

impl FileSystemElement for File {
    fn accept(&self, visitor: &dyn FileSystemVisitor) -> String {
        visitor.visit_file(self)
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_size(&self) -> u64 {
        self.size
    }
    
    fn get_permissions(&self) -> u32 {
        self.permissions
    }
}

// 目录
pub struct Directory {
    name: String,
    size: u64,
    permissions: u32,
    children: Vec<Box<dyn FileSystemElement>>,
}

impl Directory {
    pub fn new(name: String, permissions: u32) -> Self {
        Directory {
            name,
            size: 0,
            permissions,
            children: Vec::new(),
        }
    }
    
    pub fn add_child(&mut self, child: Box<dyn FileSystemElement>) {
        self.size += child.get_size();
        self.children.push(child);
    }
    
    pub fn get_children(&self) -> &Vec<Box<dyn FileSystemElement>> {
        &self.children
    }
}

impl fmt::Display for Directory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Directory({}, {} children)", self.name, self.children.len())
    }
}

impl FileSystemElement for Directory {
    fn accept(&self, visitor: &dyn FileSystemVisitor) -> String {
        visitor.visit_directory(self)
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_size(&self) -> u64 {
        self.size
    }
    
    fn get_permissions(&self) -> u32 {
        self.permissions
    }
}

// 符号链接
pub struct Symlink {
    name: String,
    size: u64,
    permissions: u32,
    target: String,
}

impl Symlink {
    pub fn new(name: String, permissions: u32, target: String) -> Self {
        Symlink {
            name,
            size: target.len() as u64,
            permissions,
            target,
        }
    }
    
    pub fn get_target(&self) -> &str {
        &self.target
    }
}

impl fmt::Display for Symlink {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symlink({} -> {})", self.name, self.target)
    }
}

impl FileSystemElement for Symlink {
    fn accept(&self, visitor: &dyn FileSystemVisitor) -> String {
        visitor.visit_symlink(self)
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_size(&self) -> u64 {
        self.size
    }
    
    fn get_permissions(&self) -> u32 {
        self.permissions
    }
}

// 文件大小计算访问者
pub struct SizeCalculatorVisitor;

impl SizeCalculatorVisitor {
    pub fn new() -> Self {
        SizeCalculatorVisitor
    }
}

impl fmt::Display for SizeCalculatorVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SizeCalculatorVisitor")
    }
}

impl FileSystemVisitor for SizeCalculatorVisitor {
    fn visit_file(&self, file: &File) -> String {
        format!("File '{}' size: {} bytes", file.get_name(), file.get_size())
    }
    
    fn visit_directory(&self, directory: &Directory) -> String {
        let total_size = directory.get_children().iter()
            .map(|child| child.get_size())
            .sum::<u64>();
        format!("Directory '{}' total size: {} bytes ({} children)", 
                directory.get_name(), total_size, directory.get_children().len())
    }
    
    fn visit_symlink(&self, symlink: &Symlink) -> String {
        format!("Symlink '{}' size: {} bytes (target: {})", 
                symlink.get_name(), symlink.get_size(), symlink.get_target())
    }
}

// 权限检查访问者
pub struct PermissionCheckerVisitor {
    required_permissions: u32,
}

impl PermissionCheckerVisitor {
    pub fn new(required_permissions: u32) -> Self {
        PermissionCheckerVisitor {
            required_permissions,
        }
    }
}

impl fmt::Display for PermissionCheckerVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PermissionCheckerVisitor(required: {:o})", self.required_permissions)
    }
}

impl FileSystemVisitor for PermissionCheckerVisitor {
    fn visit_file(&self, file: &File) -> String {
        if file.get_permissions() & self.required_permissions == self.required_permissions {
            format!("File '{}' has required permissions", file.get_name())
        } else {
            format!("File '{}' lacks required permissions", file.get_name())
        }
    }
    
    fn visit_directory(&self, directory: &Directory) -> String {
        if directory.get_permissions() & self.required_permissions == self.required_permissions {
            format!("Directory '{}' has required permissions", directory.get_name())
        } else {
            format!("Directory '{}' lacks required permissions", directory.get_name())
        }
    }
    
    fn visit_symlink(&self, symlink: &Symlink) -> String {
        if symlink.get_permissions() & self.required_permissions == self.required_permissions {
            format!("Symlink '{}' has required permissions", symlink.get_name())
        } else {
            format!("Symlink '{}' lacks required permissions", symlink.get_name())
        }
    }
}

// 文件列表访问者
pub struct FileListVisitor {
    include_hidden: bool,
}

impl FileListVisitor {
    pub fn new(include_hidden: bool) -> Self {
        FileListVisitor {
            include_hidden,
        }
    }
}

impl fmt::Display for FileListVisitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileListVisitor(include_hidden: {})", self.include_hidden)
    }
}

impl FileSystemVisitor for FileListVisitor {
    fn visit_file(&self, file: &File) -> String {
        if self.include_hidden || !file.get_name().starts_with('.') {
            format!("File: {}", file.get_name())
        } else {
            String::new()
        }
    }
    
    fn visit_directory(&self, directory: &Directory) -> String {
        if self.include_hidden || !directory.get_name().starts_with('.') {
            let children_list: Vec<String> = directory.get_children()
                .iter()
                .map(|child| child.accept(self))
                .filter(|s| !s.is_empty())
                .collect();
            format!("Directory: {}\n  {}", 
                    directory.get_name(), 
                    children_list.join("\n  "))
        } else {
            String::new()
        }
    }
    
    fn visit_symlink(&self, symlink: &Symlink) -> String {
        if self.include_hidden || !symlink.get_name().starts_with('.') {
            format!("Symlink: {} -> {}", symlink.get_name(), symlink.get_target())
        } else {
            String::new()
        }
    }
}
```

## 6. 应用场景

### 6.1 编译器设计

访问者模式在编译器设计中广泛应用：

- **语法树遍历**：遍历抽象语法树
- **类型检查**：检查表达式的类型
- **代码生成**：生成目标代码
- **优化分析**：分析代码优化机会

### 6.2 文档处理

在文档处理中，访问者模式用于：

- **格式转换**：转换文档格式
- **内容提取**：提取文档内容
- **样式应用**：应用文档样式
- **验证检查**：验证文档结构

### 6.3 文件系统

在文件系统中，访问者模式用于：

- **文件遍历**：遍历文件系统
- **权限检查**：检查文件权限
- **大小计算**：计算文件大小
- **备份操作**：执行备份操作

## 7. 变体模式

### 7.1 反射访问者模式

```rust
pub trait ReflectiveVisitor {
    fn visit(&self, element: &dyn std::any::Any) -> String;
}
```

### 7.2 组合访问者模式

```rust
pub trait CompositeVisitor: Visitor {
    fn visit_composite(&self, composite: &CompositeElement) -> String;
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **访问操作**：$O(1)$，直接方法调用
- **双重分发**：$O(1)$，两次虚函数调用
- **元素遍历**：$O(n)$，其中 $n$ 是元素数量
- **访问者切换**：$O(1)$，直接访问者替换

### 8.2 空间复杂度

- **访问者对象**：$O(v)$，其中 $v$ 是访问者大小
- **元素对象**：$O(e)$，其中 $e$ 是元素大小
- **调用栈**：$O(d)$，其中 $d$ 是调用深度
- **结果缓存**：$O(r)$，其中 $r$ 是结果大小

### 8.3 优化策略

1. **访问者缓存**：缓存访问者对象
2. **结果缓存**：缓存访问结果
3. **批量访问**：批量处理多个元素
4. **并行访问**：并行执行访问操作

## 9. 总结

访问者模式通过将操作从对象结构中分离出来，实现了操作与对象结构的解耦，具有以下优势：

1. **操作分离**：将操作从对象结构中分离出来
2. **双重分发**：支持基于对象类型和访问者类型的双重分发
3. **开闭原则**：对扩展开放，对修改封闭
4. **类型安全**：编译时类型检查

通过形式化的数学理论和完整的Rust实现，我们建立了访问者模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。
