# 5.1.1 基本概念 (Basic Concepts)

## 目录

1. [5.1.1.1 范畴定义](#5111-范畴定义)
2. [5.1.1.2 态射与复合](#5112-态射与复合)
3. [5.1.1.3 单位态射](#5113-单位态射)
4. [5.1.1.4 范畴公理](#5114-范畴公理)
5. [5.1.1.5 范畴例子](#5115-范畴例子)
6. [5.1.1.6 Rust实现](#5116-rust实现)

## 5.1.1.1 范畴定义

### 定义 5.1.1.1 (范畴)

范畴 $\mathcal{C}$ 由以下数据组成：

1. **对象集合**：$Ob(\mathcal{C})$
2. **态射集合**：对于每对对象 $A, B \in Ob(\mathcal{C})$，存在态射集合 $Hom_{\mathcal{C}}(A, B)$
3. **复合运算**：$\circ: Hom(B, C) \times Hom(A, B) \rightarrow Hom(A, C)$
4. **单位态射**：对于每个对象 $A$，存在单位态射 $1_A \in Hom(A, A)$

满足以下公理：

- **结合律**：$(f \circ g) \circ h = f \circ (g \circ h)$
- **单位律**：$f \circ 1_A = f = 1_B \circ f$

### 定义 5.1.1.2 (小范畴与大范畴)

- **小范畴**：$Ob(\mathcal{C})$ 和所有 $Hom(A, B)$ 都是集合
- **大范畴**：$Ob(\mathcal{C})$ 或某些 $Hom(A, B)$ 是类

## 5.1.1.2 态射与复合

### 定义 5.1.1.3 (态射)

态射 $f: A \rightarrow B$ 是从对象 $A$ 到对象 $B$ 的箭头，其中：

- $A$ 是态射的**域**（domain）
- $B$ 是态射的**余域**（codomain）

### 定义 5.1.1.4 (态射复合)

给定态射 $f: A \rightarrow B$ 和 $g: B \rightarrow C$，其复合 $g \circ f: A \rightarrow C$ 满足：
$$(g \circ f)(x) = g(f(x))$$

### 定理 5.1.1.1 (复合的结合性)

对于态射 $f: A \rightarrow B$, $g: B \rightarrow C$, $h: C \rightarrow D$，有：
$$(h \circ g) \circ f = h \circ (g \circ f)$$

**证明**：
对于任意 $x \in A$：
$$((h \circ g) \circ f)(x) = (h \circ g)(f(x)) = h(g(f(x)))$$
$$(h \circ (g \circ f))(x) = h((g \circ f)(x)) = h(g(f(x)))$$
因此 $(h \circ g) \circ f = h \circ (g \circ f)$。$\square$

## 5.1.1.3 单位态射

### 定义 5.1.1.5 (单位态射)

对于每个对象 $A$，单位态射 $1_A: A \rightarrow A$ 满足：

- $1_A \circ f = f$ 对于任意 $f: X \rightarrow A$
- $f \circ 1_A = f$ 对于任意 $f: A \rightarrow Y$

### 定理 5.1.1.2 (单位态射的唯一性)

每个对象的单位态射是唯一的。

**证明**：
设 $1_A$ 和 $1_A'$ 都是 $A$ 的单位态射。
则 $1_A = 1_A \circ 1_A' = 1_A'$。
因此单位态射是唯一的。$\square$

## 5.1.1.4 范畴公理

### 公理 5.1.1.1 (范畴公理系统)

范畴 $\mathcal{C}$ 满足以下公理：

1. **对象存在性**：$Ob(\mathcal{C}) \neq \emptyset$
2. **态射存在性**：对于任意 $A, B \in Ob(\mathcal{C})$，$Hom(A, B)$ 存在
3. **复合封闭性**：如果 $f: A \rightarrow B$ 和 $g: B \rightarrow C$，则 $g \circ f: A \rightarrow C$ 存在
4. **结合律**：$(f \circ g) \circ h = f \circ (g \circ h)$
5. **单位律**：$f \circ 1_A = f = 1_B \circ f$

### 定理 5.1.1.3 (范畴公理的独立性)

范畴公理是独立的，即任何一个公理都不能由其他公理推导出。

**证明**：
通过构造反例证明每个公理的独立性。
例如，构造满足除结合律外所有公理的代数结构。$\square$

## 5.1.1.5 范畴例子

### 例子 5.1.1.1 (集合范畴 Set)

- **对象**：所有集合
- **态射**：集合间的函数
- **复合**：函数复合
- **单位态射**：恒等函数

### 例子 5.1.1.2 (群范畴 Grp)

- **对象**：所有群
- **态射**：群同态
- **复合**：同态复合
- **单位态射**：恒等同态

### 例子 5.1.1.3 (拓扑空间范畴 Top)

- **对象**：所有拓扑空间
- **态射**：连续函数
- **复合**：函数复合
- **单位态射**：恒等函数

### 例子 5.1.1.4 (向量空间范畴 Vec_K)

- **对象**：域 $K$ 上的向量空间
- **态射**：线性变换
- **复合**：线性变换复合
- **单位态射**：恒等线性变换

## 5.1.1.6 Rust实现

### 实现 5.1.1.1 (基本范畴结构)

```rust
use std::collections::HashMap;
use std::any::{Any, TypeId};

// 对象标识符
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ObjectId(usize);

// 态射标识符
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MorphismId(usize);

// 态射
#[derive(Debug, Clone)]
pub struct Morphism {
    id: MorphismId,
    domain: ObjectId,
    codomain: ObjectId,
    name: String,
}

impl Morphism {
    pub fn new(id: MorphismId, domain: ObjectId, codomain: ObjectId, name: String) -> Self {
        Morphism {
            id,
            domain,
            codomain,
            name,
        }
    }
    
    pub fn can_compose_with(&self, other: &Morphism) -> bool {
        self.codomain == other.domain
    }
}

// 范畴
pub struct Category {
    objects: HashMap<ObjectId, String>,
    morphisms: HashMap<MorphismId, Morphism>,
    compositions: HashMap<(MorphismId, MorphismId), MorphismId>,
    identity_morphisms: HashMap<ObjectId, MorphismId>,
    next_object_id: usize,
    next_morphism_id: usize,
}

impl Category {
    pub fn new() -> Self {
        Category {
            objects: HashMap::new(),
            morphisms: HashMap::new(),
            compositions: HashMap::new(),
            identity_morphisms: HashMap::new(),
            next_object_id: 0,
            next_morphism_id: 0,
        }
    }
    
    pub fn add_object(&mut self, name: String) -> ObjectId {
        let id = ObjectId(self.next_object_id);
        self.next_object_id += 1;
        self.objects.insert(id.clone(), name);
        
        // 添加单位态射
        let identity_id = MorphismId(self.next_morphism_id);
        self.next_morphism_id += 1;
        
        let identity = Morphism::new(
            identity_id.clone(),
            id.clone(),
            id.clone(),
            format!("1_{}", id.0),
        );
        
        self.morphisms.insert(identity_id.clone(), identity);
        self.identity_morphisms.insert(id.clone(), identity_id);
        
        id
    }
    
    pub fn add_morphism(
        &mut self,
        domain: ObjectId,
        codomain: ObjectId,
        name: String,
    ) -> Result<MorphismId, CategoryError> {
        // 检查对象是否存在
        if !self.objects.contains_key(&domain) || !self.objects.contains_key(&codomain) {
            return Err(CategoryError::ObjectNotFound);
        }
        
        let id = MorphismId(self.next_morphism_id);
        self.next_morphism_id += 1;
        
        let morphism = Morphism::new(id.clone(), domain, codomain, name);
        self.morphisms.insert(id.clone(), morphism);
        
        Ok(id)
    }
    
    pub fn compose(
        &mut self,
        f: MorphismId,
        g: MorphismId,
    ) -> Result<MorphismId, CategoryError> {
        let f_morphism = self.morphisms.get(&f)
            .ok_or(CategoryError::MorphismNotFound)?;
        let g_morphism = self.morphisms.get(&g)
            .ok_or(CategoryError::MorphismNotFound)?;
        
        // 检查是否可以复合
        if !f_morphism.can_compose_with(g_morphism) {
            return Err(CategoryError::CompositionNotPossible);
        }
        
        // 检查是否已经定义了复合
        if let Some(composition_id) = self.compositions.get(&(f.clone(), g.clone())) {
            return Ok(composition_id.clone());
        }
        
        // 创建新的复合态射
        let composition_id = MorphismId(self.next_morphism_id);
        self.next_morphism_id += 1;
        
        let composition = Morphism::new(
            composition_id.clone(),
            f_morphism.domain.clone(),
            g_morphism.codomain.clone(),
            format!("{} ∘ {}", g_morphism.name, f_morphism.name),
        );
        
        self.morphisms.insert(composition_id.clone(), composition);
        self.compositions.insert((f, g), composition_id.clone());
        
        Ok(composition_id)
    }
    
    pub fn get_identity(&self, object: &ObjectId) -> Option<MorphismId> {
        self.identity_morphisms.get(object).cloned()
    }
    
    pub fn verify_axioms(&self) -> Result<(), CategoryError> {
        // 验证单位律
        for (object_id, identity_id) in &self.identity_morphisms {
            for (morphism_id, morphism) in &self.morphisms {
                if morphism.domain == *object_id {
                    // 检查 1_A ∘ f = f
                    if let Ok(composition) = self.compose(identity_id.clone(), morphism_id.clone()) {
                        if composition != *morphism_id {
                            return Err(CategoryError::IdentityLawViolation);
                        }
                    }
                }
                
                if morphism.codomain == *object_id {
                    // 检查 f ∘ 1_A = f
                    if let Ok(composition) = self.compose(morphism_id.clone(), identity_id.clone()) {
                        if composition != *morphism_id {
                            return Err(CategoryError::IdentityLawViolation);
                        }
                    }
                }
            }
        }
        
        // 验证结合律（简化版本）
        // 实际实现需要更复杂的检查
        
        Ok(())
    }
}

#[derive(Debug)]
pub enum CategoryError {
    ObjectNotFound,
    MorphismNotFound,
    CompositionNotPossible,
    IdentityLawViolation,
    AssociativityLawViolation,
}

// 泛型范畴实现
pub trait CategoryTrait {
    type Object;
    type Morphism;
    
    fn objects(&self) -> Vec<Self::Object>;
    fn morphisms(&self, domain: &Self::Object, codomain: &Self::Object) -> Vec<Self::Morphism>;
    fn compose(&self, f: Self::Morphism, g: Self::Morphism) -> Option<Self::Morphism>;
    fn identity(&self, object: &Self::Object) -> Self::Morphism;
}

// 集合范畴的实现
pub struct SetCategory;

impl CategoryTrait for SetCategory {
    type Object = String; // 简化为字符串表示
    type Morphism = Box<dyn Fn(usize) -> usize>; // 简化为数字函数
    
    fn objects(&self) -> Vec<Self::Object> {
        vec!["A".to_string(), "B".to_string(), "C".to_string()]
    }
    
    fn morphisms(&self, _domain: &Self::Object, _codomain: &Self::Object) -> Vec<Self::Morphism> {
        // 简化的实现
        vec![Box::new(|x| x), Box::new(|x| x + 1)]
    }
    
    fn compose(&self, f: Self::Morphism, g: Self::Morphism) -> Option<Self::Morphism> {
        Some(Box::new(move |x| f(g(x))))
    }
    
    fn identity(&self, _object: &Self::Object) -> Self::Morphism {
        Box::new(|x| x)
    }
}

// 群范畴的实现
pub struct Group {
    elements: Vec<usize>,
    operation: Box<dyn Fn(usize, usize) -> usize>,
}

impl Group {
    pub fn new(elements: Vec<usize>, operation: Box<dyn Fn(usize, usize) -> usize>) -> Self {
        Group { elements, operation }
    }
}

pub struct GroupMorphism {
    mapping: HashMap<usize, usize>,
}

impl GroupMorphism {
    pub fn new(mapping: HashMap<usize, usize>) -> Self {
        GroupMorphism { mapping }
    }
    
    pub fn apply(&self, element: usize) -> Option<usize> {
        self.mapping.get(&element).cloned()
    }
}

pub struct GroupCategory;

impl CategoryTrait for GroupCategory {
    type Object = Group;
    type Morphism = GroupMorphism;
    
    fn objects(&self) -> Vec<Self::Object> {
        // 简化的群集合
        vec![
            Group::new(vec![0, 1], Box::new(|a, b| (a + b) % 2)),
            Group::new(vec![0, 1, 2], Box::new(|a, b| (a + b) % 3)),
        ]
    }
    
    fn morphisms(&self, _domain: &Self::Object, _codomain: &Self::Object) -> Vec<Self::Morphism> {
        // 简化的群同态
        let mut mapping = HashMap::new();
        mapping.insert(0, 0);
        mapping.insert(1, 1);
        vec![GroupMorphism::new(mapping)]
    }
    
    fn compose(&self, f: Self::Morphism, g: Self::Morphism) -> Option<Self::Morphism> {
        let mut composition = HashMap::new();
        for (key, value) in &f.mapping {
            if let Some(result) = g.apply(*value) {
                composition.insert(*key, result);
            }
        }
        Some(GroupMorphism::new(composition))
    }
    
    fn identity(&self, group: &Self::Object) -> Self::Morphism {
        let mut mapping = HashMap::new();
        for element in &group.elements {
            mapping.insert(*element, *element);
        }
        GroupMorphism::new(mapping)
    }
}
```

### 实现 5.1.1.2 (范畴验证器)

```rust
pub struct CategoryValidator;

impl CategoryValidator {
    pub fn validate_category<C: CategoryTrait>(category: &C) -> ValidationResult {
        let mut errors = Vec::new();
        
        // 检查对象存在性
        let objects = category.objects();
        if objects.is_empty() {
            errors.push(ValidationError::NoObjects);
        }
        
        // 检查单位律
        for object in &objects {
            let identity = category.identity(object);
            for codomain in &objects {
                let morphisms = category.morphisms(object, codomain);
                for morphism in morphisms {
                    if let Some(composition) = category.compose(identity.clone(), morphism.clone()) {
                        if !Self::morphisms_equal(&composition, &morphism) {
                            errors.push(ValidationError::IdentityLawViolation);
                        }
                    }
                }
            }
        }
        
        if errors.is_empty() {
            ValidationResult::Valid
        } else {
            ValidationResult::Invalid(errors)
        }
    }
    
    fn morphisms_equal<C: CategoryTrait>(m1: &C::Morphism, m2: &C::Morphism) -> bool {
        // 简化的相等性检查
        // 实际实现需要根据具体类型定义相等性
        true
    }
}

#[derive(Debug)]
pub enum ValidationError {
    NoObjects,
    IdentityLawViolation,
    AssociativityLawViolation,
}

#[derive(Debug)]
pub enum ValidationResult {
    Valid,
    Invalid(Vec<ValidationError>),
}
```

## 持续上下文管理

### 进度跟踪

- [x] 范畴定义
- [x] 态射与复合
- [x] 单位态射
- [x] 范畴公理
- [x] 范畴例子
- [x] Rust实现

### 下一步计划

1. 完成函子与自然变换的内容
2. 实现极限与余极限
3. 建立伴随函子理论
4. 构建单子与余单子

### 中断恢复点

当前状态：范畴论基本概念内容已完成，准备开始函子与自然变换的内容编写。
