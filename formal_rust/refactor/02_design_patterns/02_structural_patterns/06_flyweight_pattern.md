# 06. 享元模式形式化理论

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

享元模式是一种结构型设计模式，它通过共享技术有效地支持大量细粒度对象的复用。

**形式化定义**：
设 $\mathcal{O}$ 为对象集合，$\mathcal{S}$ 为共享状态集合，$\mathcal{U}$ 为唯一状态集合，则享元模式可定义为：

$$\text{Flyweight} : \mathcal{S} \times \mathcal{U} \rightarrow \mathcal{O}$$

其中：
- $\mathcal{S}$ 为共享状态集合
- $\mathcal{U}$ 为唯一状态集合
- $\mathcal{O}$ 为目标对象集合

### 1.2 类型签名

```haskell
class Flyweight where
  operation :: Flyweight -> UniqueState -> String

class FlyweightFactory where
  getFlyweight :: FlyweightFactory -> SharedState -> Flyweight
```

### 1.3 模式结构

```
Flyweight
├── sharedState: SharedState
└── operation(uniqueState) -> String

ConcreteFlyweight
├── sharedState: SharedState
└── operation(uniqueState) -> String

FlyweightFactory
├── flyweights: Map<SharedState, Flyweight>
└── getFlyweight(sharedState) -> Flyweight
```

## 2. 数学基础

### 2.1 共享理论

**定义 2.1**：共享状态
共享状态 $S$ 是一个可以被多个对象共享的状态：
$$S \in \mathcal{S}$$

**定义 2.2**：唯一状态
唯一状态 $U$ 是每个对象独有的状态：
$$U \in \mathcal{U}$$

### 2.2 享元性质

**性质 2.1**：共享的传递性
$$\forall s \in \mathcal{S}, u_1, u_2 \in \mathcal{U} : F(s, u_1) \sim F(s, u_2)$$

**性质 2.2**：状态的分离性
$$\forall o \in \mathcal{O} : o = (s, u) \text{ 其中 } s \in \mathcal{S}, u \in \mathcal{U}$$

**定理 2.1**：享元的唯一性
对于任意共享状态 $s$ 和唯一状态 $u$，享元 $F(s, u)$ 是唯一的。

## 3. 类型系统分析

### 3.1 类型构造器

在 Rust 中，享元模式可以通过 trait 和 HashMap 实现：

```rust
use std::collections::HashMap;

// 享元接口
trait Flyweight {
    fn operation(&self, unique_state: &str) -> String;
}

// 具体享元
struct ConcreteFlyweight {
    shared_state: String,
}

impl ConcreteFlyweight {
    fn new(shared_state: String) -> Self {
        ConcreteFlyweight { shared_state }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, unique_state: &str) -> String {
        format!("ConcreteFlyweight: shared={}, unique={}", 
                self.shared_state, unique_state)
    }
}

// 享元工厂
struct FlyweightFactory {
    flyweights: HashMap<String, Box<dyn Flyweight>>,
}

impl FlyweightFactory {
    fn new() -> Self {
        FlyweightFactory {
            flyweights: HashMap::new(),
        }
    }
    
    fn get_flyweight(&mut self, shared_state: String) -> &Box<dyn Flyweight> {
        if !self.flyweights.contains_key(&shared_state) {
            self.flyweights.insert(
                shared_state.clone(),
                Box::new(ConcreteFlyweight::new(shared_state.clone()))
            );
        }
        
        self.flyweights.get(&shared_state).unwrap()
    }
}
```

### 3.2 类型约束

**约束 1**：享元类型约束
$$\text{Flyweight} \subseteq \text{Trait} \land \text{ConcreteFlyweight} \subseteq \text{Flyweight}$$

**约束 2**：工厂类型约束
$$\text{FlyweightFactory} \subseteq \text{Struct} \land \text{FlyweightFactory} \text{ 管理享元}$$

### 3.3 类型推导

给定享元类型 $F$，类型推导规则为：

$$\frac{F : \text{Flyweight} \quad F \vdash \text{operation} : \text{String} \rightarrow \text{String}}{F.\text{operation}(s) : \text{String}}$$

## 4. 范畴论视角

### 4.1 函子映射

享元模式可以看作是一个函子：
$$F : \mathcal{C}_S \times \mathcal{C}_U \rightarrow \mathcal{C}_O$$

其中：
- $\mathcal{C}_S$ 是共享状态范畴
- $\mathcal{C}_U$ 是唯一状态范畴
- $\mathcal{C}_O$ 是对象范畴

### 4.2 自然变换

不同享元之间的转换可以表示为自然变换：
$$\eta : F \Rightarrow G$$

**定理 4.1**：享元转换的一致性
对于任意自然变换 $\eta$，满足：
$$\eta_{(s_1, u_1) \circ (s_2, u_2)} = \eta_{(s_1, u_1)} \circ \eta_{(s_2, u_2)}$$

## 5. Rust 类型系统映射

### 5.1 实现架构

```rust
use std::collections::HashMap;

// 字符享元
trait Character {
    fn display(&self, font_size: u32, color: &str) -> String;
}

// 具体字符享元
struct CharacterFlyweight {
    character: char,
}

impl CharacterFlyweight {
    fn new(character: char) -> Self {
        CharacterFlyweight { character }
    }
}

impl Character for CharacterFlyweight {
    fn display(&self, font_size: u32, color: &str) -> String {
        format!("Character '{}' with font size {} and color {}", 
                self.character, font_size, color)
    }
}

// 字符工厂
struct CharacterFactory {
    characters: HashMap<char, Box<dyn Character>>,
}

impl CharacterFactory {
    fn new() -> Self {
        CharacterFactory {
            characters: HashMap::new(),
        }
    }
    
    fn get_character(&mut self, character: char) -> &Box<dyn Character> {
        if !self.characters.contains_key(&character) {
            self.characters.insert(
                character,
                Box::new(CharacterFlyweight::new(character))
            );
        }
        
        self.characters.get(&character).unwrap()
    }
    
    fn get_character_count(&self) -> usize {
        self.characters.len()
    }
}

// 文本编辑器（使用享元）
struct TextEditor {
    factory: CharacterFactory,
    text: Vec<(char, u32, String)>, // (character, font_size, color)
}

impl TextEditor {
    fn new() -> Self {
        TextEditor {
            factory: CharacterFactory::new(),
            text: Vec::new(),
        }
    }
    
    fn add_character(&mut self, character: char, font_size: u32, color: String) {
        self.text.push((character, font_size, color));
    }
    
    fn display_text(&mut self) -> String {
        let mut result = String::new();
        
        for (character, font_size, color) in &self.text {
            let flyweight = self.factory.get_character(*character);
            result.push_str(&flyweight.display(*font_size, color));
            result.push('\n');
        }
        
        result
    }
    
    fn get_unique_characters_count(&self) -> usize {
        self.factory.get_character_count()
    }
}
```

### 5.2 类型安全保证

**定理 5.1**：类型安全
对于任意享元 $F$：
$$\text{TypeOf}(F.\text{operation}(u)) = \text{ExpectedType}(\text{String})$$

## 6. 实现策略

### 6.1 策略选择

1. **工厂策略**：使用工厂管理享元对象
2. **缓存策略**：缓存已创建的享元对象
3. **状态分离策略**：将共享状态和唯一状态分离

### 6.2 性能分析

**时间复杂度**：
- 享元创建：$O(1)$
- 享元查找：$O(1)$（使用 HashMap）
- 享元操作：$O(1)$

**空间复杂度**：
- 享元存储：$O(n)$，其中 $n$ 为唯一享元数量
- 状态存储：$O(m)$，其中 $m$ 为对象数量

## 7. 形式化证明

### 7.1 享元正确性证明

**命题 7.1**：享元正确性
对于任意共享状态 $s$ 和唯一状态 $u$，享元 $F(s, u)$ 满足：
1. 共享状态被多个对象共享
2. 唯一状态是每个对象独有的
3. 享元对象被正确复用

**证明**：
1. 工厂使用 HashMap 缓存享元对象
2. 相同共享状态的对象共享同一个享元
3. 唯一状态通过参数传递
4. 因此享元是正确的。$\square$

### 7.2 内存优化证明

**命题 7.2**：内存优化
享元模式显著减少了内存使用。

**证明**：
1. 共享状态只存储一份
2. 唯一状态通过参数传递
3. 相同共享状态的对象共享享元
4. 因此内存使用被优化了。$\square$

## 8. 应用场景

### 8.1 文本编辑器

```rust
// 应用示例
fn main() {
    let mut editor = TextEditor::new();
    
    // 添加文本
    editor.add_character('H', 12, "black".to_string());
    editor.add_character('e', 12, "black".to_string());
    editor.add_character('l', 12, "black".to_string());
    editor.add_character('l', 12, "black".to_string());
    editor.add_character('o', 12, "black".to_string());
    editor.add_character(' ', 12, "black".to_string());
    editor.add_character('W', 16, "blue".to_string());
    editor.add_character('o', 16, "blue".to_string());
    editor.add_character('r', 16, "blue".to_string());
    editor.add_character('l', 16, "blue".to_string());
    editor.add_character('d', 16, "blue".to_string());
    editor.add_character('!', 16, "red".to_string());
    
    // 显示文本
    println!("Text Display:");
    println!("{}", editor.display_text());
    
    // 显示统计信息
    println!("\nStatistics:");
    println!("Total characters: {}", editor.text.len());
    println!("Unique characters: {}", editor.get_unique_characters_count());
    println!("Memory saved: {} objects", 
             editor.text.len() - editor.get_unique_characters_count());
}
```

### 8.2 游戏图形系统

```rust
trait TreeModel {
    fn render(&self, position: (f32, f32), season: &str) -> String;
}

struct TreeFlyweight {
    model_type: String,
    texture: String,
}

impl TreeFlyweight {
    fn new(model_type: String, texture: String) -> Self {
        TreeFlyweight { model_type, texture }
    }
}

impl TreeModel for TreeFlyweight {
    fn render(&self, position: (f32, f32), season: &str) -> String {
        format!("Rendering {} tree at ({:.1}, {:.1}) in {} season with texture: {}", 
                self.model_type, position.0, position.1, season, self.texture)
    }
}

struct TreeFactory {
    trees: HashMap<String, Box<dyn TreeModel>>,
}

impl TreeFactory {
    fn new() -> Self {
        TreeFactory {
            trees: HashMap::new(),
        }
    }
    
    fn get_tree(&mut self, tree_type: &str) -> &Box<dyn TreeModel> {
        if !self.trees.contains_key(tree_type) {
            let texture = match tree_type {
                "oak" => "oak_texture.png",
                "pine" => "pine_texture.png",
                "maple" => "maple_texture.png",
                _ => "default_texture.png",
            };
            
            self.trees.insert(
                tree_type.to_string(),
                Box::new(TreeFlyweight::new(tree_type.to_string(), texture.to_string()))
            );
        }
        
        self.trees.get(tree_type).unwrap()
    }
}

struct Forest {
    factory: TreeFactory,
    trees: Vec<(String, (f32, f32), String)>, // (type, position, season)
}

impl Forest {
    fn new() -> Self {
        Forest {
            factory: TreeFactory::new(),
            trees: Vec::new(),
        }
    }
    
    fn plant_tree(&mut self, tree_type: &str, position: (f32, f32), season: &str) {
        self.trees.push((tree_type.to_string(), position, season.to_string()));
    }
    
    fn render_forest(&mut self) -> String {
        let mut result = String::new();
        
        for (tree_type, position, season) in &self.trees {
            let tree = self.factory.get_tree(tree_type);
            result.push_str(&tree.render(*position, season));
            result.push('\n');
        }
        
        result
    }
}
```

## 9. 总结

享元模式通过以下方式提供形式化保证：

1. **内存优化**：通过共享减少内存使用
2. **对象复用**：相同状态的对象共享享元
3. **类型安全**：通过 Rust 的类型系统确保享元的正确性
4. **性能提升**：减少对象创建和内存分配

该模式在 Rust 中的实现充分利用了 HashMap 和 trait 系统的优势，提供了高效的对象复用机制。

---

**参考文献**：
1. Gamma, E., et al. "Design Patterns: Elements of Reusable Object-Oriented Software"
2. Pierce, B. C. "Types and Programming Languages"
3. Mac Lane, S. "Categories for the Working Mathematician" 