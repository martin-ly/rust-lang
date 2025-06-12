# 模板方法模式 (Template Method Pattern) - 形式化重构

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

模板方法模式是一种行为型设计模式，它定义了一个算法的骨架，将一些步骤延迟到子类中实现。模板方法使得子类可以在不改变算法结构的情况下，重新定义算法的某些特定步骤。

### 1.2 模式特征

- **算法骨架**：定义算法的整体结构
- **步骤抽象**：将可变步骤抽象为方法
- **子类实现**：子类实现具体的步骤
- **不变性**：算法结构保持不变

## 2. 形式化定义

### 2.1 模板方法模式五元组

**定义2.1 (模板方法模式五元组)**
设 $T = (A, S, I, H, C)$ 为一个模板方法模式，其中：

- $A = \{a_1, a_2, ..., a_n\}$ 是算法集合
- $S = \{s_1, s_2, ..., s_m\}$ 是步骤集合
- $I = \{i_1, i_2, ..., i_k\}$ 是接口集合
- $H = \{h_1, h_2, ..., h_l\}$ 是钩子集合
- $C = \{c_1, c_2, ..., c_p\}$ 是约束集合

### 2.2 模板接口定义

**定义2.2 (模板接口)**
模板接口 $I_{tmpl}$ 定义为：

$$I_{tmpl} = \{\text{templateMethod}() \rightarrow R, \text{primitiveOperation}() \rightarrow \text{void}, \text{hook}() \rightarrow \text{bool}\}$$

### 2.3 算法骨架定义

**定义2.3 (算法骨架)**
算法骨架 $S_{alg}$ 定义为：

$$S_{alg} = (s_1, s_2, ..., s_n) \text{ where } s_i \text{ is a step}$$

### 2.4 步骤执行函数

**定义2.4 (步骤执行函数)**
步骤执行函数 $f_S: S \times C \rightarrow R$ 定义为：

$$f_S(s, c) = \text{execute}(s, c)$$

## 3. 数学理论

### 3.1 算法不变性理论

**定义3.1 (算法不变性)**
算法 $A$ 的结构是不变的，当且仅当：

$$\forall \text{subclass}: \text{templateMethod}() \text{ has same structure}$$

### 3.2 步骤替换理论

**定义3.2 (步骤替换)**
步骤 $s_1$ 可以被步骤 $s_2$ 替换，当且仅当：

$$\text{implements}(s_2, I_s) \land \text{compatible}(s_1, s_2)$$

### 3.3 钩子条件理论

**定义3.3 (钩子条件)**
钩子函数 $h$ 的条件是：

$$h() \rightarrow \text{bool} \land \text{optional}(h)$$

### 3.4 算法完整性理论

**定义3.4 (算法完整性)**
算法 $A$ 是完整的，当且仅当：

$$\forall s \in S: \text{implemented}(s) \lor \text{optional}(s)$$

## 4. 核心定理

### 4.1 算法结构不变性定理

**定理4.1 (算法结构不变性)**
如果模板方法定义了算法骨架，则子类不能改变算法结构：

$$\text{templateMethod}() \text{ is final} \Rightarrow \text{structureInvariant}()$$

**证明：**

1. 根据定义2.3，算法骨架是固定的
2. 模板方法不允许被重写
3. 算法结构不变性定理得证。

### 4.2 步骤替换安全性定理

**定理4.2 (步骤替换安全性)**
如果步骤 $s_2$ 实现了相同的接口，则替换是安全的：

$$\text{implements}(s_2, I_s) \Rightarrow \text{safeReplace}(s_1, s_2)$$

**证明：**

1. 根据定义3.2，步骤替换满足接口约束
2. 替换后的步骤保持兼容性
3. 步骤替换安全性定理得证。

### 4.3 钩子条件定理

**定理4.3 (钩子条件)**
钩子函数是可选的，不影响算法的主要流程：

$$\text{optional}(h) \Rightarrow \text{algorithmWorks}(h() \lor \neg h())$$

**证明：**

1. 根据定义3.3，钩子函数是可选的
2. 无论钩子返回什么，算法都能正常工作
3. 钩子条件定理得证。

### 4.4 算法完整性定理

**定理4.4 (算法完整性)**
如果所有必需步骤都被实现，则算法是完整的：

$$\forall s \in S_{required}: \text{implemented}(s) \Rightarrow \text{complete}(A)$$

**证明：**

1. 根据定义3.4，所有必需步骤都已实现
2. 可选步骤不影响算法完整性
3. 算法完整性定理得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;

// 抽象模板类
pub trait TemplateMethod: fmt::Display {
    // 模板方法（算法骨架）
    fn template_method(&self) -> String {
        let mut result = String::new();
        
        // 步骤1：初始化
        result.push_str(&self.initialize());
        result.push('\n');
        
        // 步骤2：处理数据
        result.push_str(&self.process_data());
        result.push('\n');
        
        // 钩子：可选的预处理
        if self.should_preprocess() {
            result.push_str(&self.preprocess());
            result.push('\n');
        }
        
        // 步骤3：核心处理
        result.push_str(&self.core_processing());
        result.push('\n');
        
        // 步骤4：清理
        result.push_str(&self.cleanup());
        result.push('\n');
        
        result
    }
    
    // 抽象方法（必须由子类实现）
    fn initialize(&self) -> String;
    fn process_data(&self) -> String;
    fn core_processing(&self) -> String;
    fn cleanup(&self) -> String;
    
    // 钩子方法（可选重写）
    fn should_preprocess(&self) -> bool {
        false // 默认不预处理
    }
    
    fn preprocess(&self) -> String {
        "Default preprocessing".to_string()
    }
}

// 具体实现：数据处理算法
pub struct DataProcessor {
    data: Vec<i32>,
}

impl DataProcessor {
    pub fn new(data: Vec<i32>) -> Self {
        DataProcessor { data }
    }
    
    pub fn get_data(&self) -> &Vec<i32> {
        &self.data
    }
}

impl fmt::Display for DataProcessor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DataProcessor(data: {:?})", self.data)
    }
}

impl TemplateMethod for DataProcessor {
    fn initialize(&self) -> String {
        format!("[DataProcessor] Initializing with {} elements", self.data.len())
    }
    
    fn process_data(&self) -> String {
        let sum: i32 = self.data.iter().sum();
        format!("[DataProcessor] Processing data, sum: {}", sum)
    }
    
    fn core_processing(&self) -> String {
        let avg = if !self.data.is_empty() {
            self.data.iter().sum::<i32>() as f64 / self.data.len() as f64
        } else {
            0.0
        };
        format!("[DataProcessor] Core processing, average: {:.2}", avg)
    }
    
    fn cleanup(&self) -> String {
        format!("[DataProcessor] Cleaning up {} elements", self.data.len())
    }
}

// 具体实现：排序算法
pub struct SortProcessor {
    data: Vec<i32>,
    use_optimization: bool,
}

impl SortProcessor {
    pub fn new(data: Vec<i32>, use_optimization: bool) -> Self {
        SortProcessor {
            data,
            use_optimization,
        }
    }
    
    pub fn get_data(&self) -> &Vec<i32> {
        &self.data
    }
}

impl fmt::Display for SortProcessor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SortProcessor(data: {:?}, optimization: {})", 
               self.data, self.use_optimization)
    }
}

impl TemplateMethod for SortProcessor {
    fn initialize(&self) -> String {
        format!("[SortProcessor] Initializing sort with {} elements", self.data.len())
    }
    
    fn process_data(&self) -> String {
        let mut sorted_data = self.data.clone();
        sorted_data.sort();
        format!("[SortProcessor] Processing data, sorted: {:?}", sorted_data)
    }
    
    fn core_processing(&self) -> String {
        let mut sorted_data = self.data.clone();
        if self.use_optimization {
            sorted_data.sort_unstable(); // 使用不稳定排序优化
            format!("[SortProcessor] Core processing with optimization")
        } else {
            sorted_data.sort(); // 使用稳定排序
            format!("[SortProcessor] Core processing without optimization")
        }
    }
    
    fn cleanup(&self) -> String {
        format!("[SortProcessor] Cleaning up sorted data")
    }
    
    // 重写钩子方法
    fn should_preprocess(&self) -> bool {
        self.use_optimization && self.data.len() > 1000
    }
    
    fn preprocess(&self) -> String {
        format!("[SortProcessor] Preprocessing large dataset ({} elements)", self.data.len())
    }
}

// 具体实现：搜索算法
pub struct SearchProcessor {
    data: Vec<i32>,
    target: i32,
    use_binary_search: bool,
}

impl SearchProcessor {
    pub fn new(data: Vec<i32>, target: i32, use_binary_search: bool) -> Self {
        SearchProcessor {
            data,
            target,
            use_binary_search,
        }
    }
    
    pub fn get_data(&self) -> &Vec<i32> {
        &self.data
    }
    
    pub fn get_target(&self) -> i32 {
        self.target
    }
}

impl fmt::Display for SearchProcessor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SearchProcessor(data: {:?}, target: {}, binary: {})", 
               self.data, self.target, self.use_binary_search)
    }
}

impl TemplateMethod for SearchProcessor {
    fn initialize(&self) -> String {
        format!("[SearchProcessor] Initializing search for target {}", self.target)
    }
    
    fn process_data(&self) -> String {
        if self.use_binary_search {
            let mut sorted_data = self.data.clone();
            sorted_data.sort();
            format!("[SearchProcessor] Processing data for binary search, sorted: {:?}", sorted_data)
        } else {
            format!("[SearchProcessor] Processing data for linear search: {:?}", self.data)
        }
    }
    
    fn core_processing(&self) -> String {
        if self.use_binary_search {
            let mut sorted_data = self.data.clone();
            sorted_data.sort();
            match sorted_data.binary_search(&self.target) {
                Ok(index) => format!("[SearchProcessor] Binary search found target at index {}", index),
                Err(_) => format!("[SearchProcessor] Binary search: target not found"),
            }
        } else {
            match self.data.iter().position(|&x| x == self.target) {
                Some(index) => format!("[SearchProcessor] Linear search found target at index {}", index),
                None => format!("[SearchProcessor] Linear search: target not found"),
            }
        }
    }
    
    fn cleanup(&self) -> String {
        format!("[SearchProcessor] Cleaning up search results")
    }
    
    // 重写钩子方法
    fn should_preprocess(&self) -> bool {
        self.use_binary_search && !self.data.is_sorted()
    }
    
    fn preprocess(&self) -> String {
        format!("[SearchProcessor] Preprocessing: sorting data for binary search")
    }
}

// 为Vec<i32>添加is_sorted方法
trait SortedCheck {
    fn is_sorted(&self) -> bool;
}

impl SortedCheck for Vec<i32> {
    fn is_sorted(&self) -> bool {
        self.windows(2).all(|window| window[0] <= window[1])
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;
use std::cmp::Ord;

// 泛型模板方法trait
pub trait GenericTemplateMethod<T, R>: fmt::Display {
    // 模板方法
    fn template_method(&self, input: &[T]) -> R {
        // 步骤1：验证输入
        if !self.validate_input(input) {
            return self.handle_invalid_input(input);
        }
        
        // 步骤2：预处理
        let processed_input = if self.should_preprocess(input) {
            self.preprocess(input)
        } else {
            input.to_vec()
        };
        
        // 步骤3：核心处理
        let result = self.core_processing(&processed_input);
        
        // 步骤4：后处理
        let final_result = if self.should_postprocess(&result) {
            self.postprocess(result)
        } else {
            result
        };
        
        // 步骤5：清理
        self.cleanup(&processed_input);
        
        final_result
    }
    
    // 抽象方法
    fn validate_input(&self, input: &[T]) -> bool;
    fn core_processing(&self, input: &[T]) -> R;
    
    // 可选方法（默认实现）
    fn handle_invalid_input(&self, _input: &[T]) -> R {
        panic!("Invalid input provided")
    }
    
    fn should_preprocess(&self, _input: &[T]) -> bool {
        false
    }
    
    fn preprocess(&self, input: &[T]) -> Vec<T> {
        input.to_vec()
    }
    
    fn should_postprocess(&self, _result: &R) -> bool {
        false
    }
    
    fn postprocess(&self, result: R) -> R {
        result
    }
    
    fn cleanup(&self, _input: &[T]) {
        // 默认无清理操作
    }
}

// 排序模板
pub struct SortTemplate<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T> SortTemplate<T> {
    pub fn new() -> Self {
        SortTemplate {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: fmt::Debug> fmt::Display for SortTemplate<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SortTemplate")
    }
}

impl<T: Ord + Clone> GenericTemplateMethod<T, Vec<T>> for SortTemplate<T> {
    fn validate_input(&self, input: &[T]) -> bool {
        !input.is_empty()
    }
    
    fn core_processing(&self, input: &[T]) -> Vec<T> {
        let mut result = input.to_vec();
        result.sort();
        result
    }
    
    fn should_preprocess(&self, input: &[T]) -> bool {
        input.len() > 1000 // 大数据集需要预处理
    }
    
    fn preprocess(&self, input: &[T]) -> Vec<T> {
        // 预处理：去重
        let mut result = input.to_vec();
        result.sort();
        result.dedup();
        result
    }
}

// 搜索模板
pub struct SearchTemplate<T> {
    target: T,
    use_binary: bool,
}

impl<T> SearchTemplate<T> {
    pub fn new(target: T, use_binary: bool) -> Self {
        SearchTemplate {
            target,
            use_binary,
        }
    }
}

impl<T: fmt::Debug> fmt::Display for SearchTemplate<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SearchTemplate(target: {:?}, binary: {})", self.target, self.use_binary)
    }
}

impl<T: Ord + Clone + PartialEq> GenericTemplateMethod<T, Option<usize>> for SearchTemplate<T> {
    fn validate_input(&self, input: &[T]) -> bool {
        !input.is_empty()
    }
    
    fn core_processing(&self, input: &[T]) -> Option<usize> {
        if self.use_binary {
            input.binary_search(&self.target).ok()
        } else {
            input.iter().position(|x| x == &self.target)
        }
    }
    
    fn should_preprocess(&self, input: &[T]) -> bool {
        self.use_binary && !input.is_sorted()
    }
    
    fn preprocess(&self, input: &[T]) -> Vec<T> {
        let mut result = input.to_vec();
        result.sort();
        result
    }
    
    fn handle_invalid_input(&self, _input: &[T]) -> Option<usize> {
        None
    }
}

// 为Vec<T>添加is_sorted方法
trait GenericSortedCheck<T> {
    fn is_sorted(&self) -> bool;
}

impl<T: Ord> GenericSortedCheck<T> for Vec<T> {
    fn is_sorted(&self) -> bool {
        self.windows(2).all(|window| window[0] <= window[1])
    }
}
```

### 5.3 应用场景实现

```rust
// 文档处理模板
pub trait DocumentProcessor: fmt::Display {
    // 模板方法
    fn process_document(&self, content: &str) -> String {
        let mut result = String::new();
        
        // 步骤1：解析文档
        result.push_str(&self.parse_document(content));
        result.push('\n');
        
        // 步骤2：验证文档
        if !self.validate_document(content) {
            return format!("{}[ERROR] Document validation failed", result);
        }
        
        // 步骤3：处理文档
        result.push_str(&self.process_content(content));
        result.push('\n');
        
        // 钩子：可选的格式化
        if self.should_format() {
            result.push_str(&self.format_document(&result));
            result.push('\n');
        }
        
        // 步骤4：生成输出
        result.push_str(&self.generate_output(&result));
        result.push('\n');
        
        result
    }
    
    // 抽象方法
    fn parse_document(&self, content: &str) -> String;
    fn validate_document(&self, content: &str) -> bool;
    fn process_content(&self, content: &str) -> String;
    fn generate_output(&self, processed: &str) -> String;
    
    // 钩子方法
    fn should_format(&self) -> bool {
        false
    }
    
    fn format_document(&self, content: &str) -> String {
        format!("[FORMATTED] {}", content)
    }
}

// 文本处理器
pub struct TextProcessor {
    remove_whitespace: bool,
    convert_uppercase: bool,
}

impl TextProcessor {
    pub fn new(remove_whitespace: bool, convert_uppercase: bool) -> Self {
        TextProcessor {
            remove_whitespace,
            convert_uppercase,
        }
    }
}

impl fmt::Display for TextProcessor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TextProcessor(remove_ws: {}, uppercase: {})", 
               self.remove_whitespace, self.convert_uppercase)
    }
}

impl DocumentProcessor for TextProcessor {
    fn parse_document(&self, content: &str) -> String {
        format!("[TextProcessor] Parsing text document ({} characters)", content.len())
    }
    
    fn validate_document(&self, content: &str) -> bool {
        !content.is_empty() && content.len() <= 10000
    }
    
    fn process_content(&self, content: &str) -> String {
        let mut processed = content.to_string();
        
        if self.remove_whitespace {
            processed = processed.split_whitespace().collect::<Vec<_>>().join(" ");
        }
        
        if self.convert_uppercase {
            processed = processed.to_uppercase();
        }
        
        format!("[TextProcessor] Processed content: {}", processed)
    }
    
    fn generate_output(&self, processed: &str) -> String {
        format!("[TextProcessor] Generated text output: {}", processed)
    }
    
    fn should_format(&self) -> bool {
        self.convert_uppercase
    }
    
    fn format_document(&self, content: &str) -> String {
        format!("[TextProcessor] Formatted document: {}", content.to_uppercase())
    }
}

// HTML处理器
pub struct HtmlProcessor {
    strip_tags: bool,
    extract_links: bool,
}

impl HtmlProcessor {
    pub fn new(strip_tags: bool, extract_links: bool) -> Self {
        HtmlProcessor {
            strip_tags,
            extract_links,
        }
    }
}

impl fmt::Display for HtmlProcessor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "HtmlProcessor(strip_tags: {}, extract_links: {})", 
               self.strip_tags, self.extract_links)
    }
}

impl DocumentProcessor for HtmlProcessor {
    fn parse_document(&self, content: &str) -> String {
        format!("[HtmlProcessor] Parsing HTML document ({} characters)", content.len())
    }
    
    fn validate_document(&self, content: &str) -> bool {
        !content.is_empty() && (content.contains('<') || content.contains('>'))
    }
    
    fn process_content(&self, content: &str) -> String {
        let mut processed = content.to_string();
        
        if self.strip_tags {
            // 简单的标签移除（实际应用中应使用HTML解析器）
            processed = processed.replace("<", "").replace(">", "");
        }
        
        if self.extract_links {
            // 简单的链接提取
            let links: Vec<&str> = content
                .split("href=\"")
                .skip(1)
                .filter_map(|s| s.split('"').next())
                .collect();
            processed = format!("{} [Links: {:?}]", processed, links);
        }
        
        format!("[HtmlProcessor] Processed content: {}", processed)
    }
    
    fn generate_output(&self, processed: &str) -> String {
        format!("[HtmlProcessor] Generated HTML output: {}", processed)
    }
    
    fn should_format(&self) -> bool {
        self.strip_tags
    }
    
    fn format_document(&self, content: &str) -> String {
        format!("[HtmlProcessor] Formatted document (tags stripped): {}", 
                content.replace("<", "").replace(">", ""))
    }
}
```

## 6. 应用场景

### 6.1 算法框架

模板方法模式在算法框架中广泛应用：

- **排序算法**：定义排序的通用步骤
- **搜索算法**：定义搜索的通用流程
- **数据处理**：定义数据处理的通用步骤
- **文件处理**：定义文件处理的通用流程

### 6.2 框架设计

在框架设计中，模板方法模式用于：

- **生命周期管理**：定义对象的生命周期
- **事件处理**：定义事件处理的通用流程
- **资源管理**：定义资源管理的通用步骤
- **配置管理**：定义配置管理的通用流程

### 6.3 工具类设计

在工具类设计中，模板方法模式用于：

- **文档处理**：定义文档处理的通用步骤
- **图像处理**：定义图像处理的通用流程
- **网络请求**：定义网络请求的通用步骤
- **数据库操作**：定义数据库操作的通用流程

## 7. 变体模式

### 7.1 策略模板模式

```rust
pub trait StrategyTemplate {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.step1());
        result.push_str(&self.step2());
        result.push_str(&self.step3());
        result
    }
    
    fn step1(&self) -> String;
    fn step2(&self) -> String;
    fn step3(&self) -> String;
}
```

### 7.2 钩子模板模式

```rust
pub trait HookTemplate {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.required_step());
        
        if self.optional_hook() {
            result.push_str(&self.optional_step());
        }
        
        result.push_str(&self.final_step());
        result
    }
    
    fn required_step(&self) -> String;
    fn optional_hook(&self) -> bool { false }
    fn optional_step(&self) -> String { String::new() }
    fn final_step(&self) -> String;
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **模板方法调用**：$O(1)$，直接方法调用
- **步骤执行**：取决于具体步骤的复杂度
- **钩子检查**：$O(1)$，简单的条件检查
- **算法执行**：$O(n)$，其中 $n$ 是输入大小

### 8.2 空间复杂度

- **模板对象**：$O(s)$，其中 $s$ 是对象大小
- **步骤数据**：$O(d)$，其中 $d$ 是数据大小
- **中间结果**：$O(m)$，其中 $m$ 是中间结果大小
- **最终结果**：$O(r)$，其中 $r$ 是结果大小

### 8.3 优化策略

1. **步骤缓存**：缓存步骤结果
2. **延迟计算**：延迟计算可选步骤
3. **内存池**：重用对象减少分配
4. **并行处理**：并行执行独立步骤

## 9. 总结

模板方法模式通过定义算法的骨架，将可变步骤延迟到子类实现，具有以下优势：

1. **算法骨架**：定义算法的整体结构
2. **步骤抽象**：将可变步骤抽象为方法
3. **子类实现**：子类实现具体的步骤
4. **不变性**：算法结构保持不变

通过形式化的数学理论和完整的Rust实现，我们建立了模板方法模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。
