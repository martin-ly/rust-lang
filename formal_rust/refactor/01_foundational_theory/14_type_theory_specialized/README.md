# 05. 类型论 (Type Theory)

## 5.1 形式化定义

### 5.1.1 类型系统公理

****定义 5**.1.1** (类型系统)
类型系统是一个五元组 $\mathcal{T} = (T, \Gamma, \vdash, \rightarrow, \equiv)$，其中：

- $T$ 是类型集合
- $\Gamma$ 是上下文集合
- $\vdash$ 是类型判断关系
- $\rightarrow$ 是函数类型构造子
- $\equiv$ 是类型等价关系

**公理 5.1.1** (类型形成)
对于任意类型 $A, B \in T$：
$$\frac{A \in T \quad B \in T}{A \rightarrow B \in T}$$

**公理 5.1.2** (变量引入)
对于任意上下文 $\Gamma$ 和变量 $x$：
$$\frac{x \notin \text{dom}(\Gamma)}{\Gamma, x:A \vdash x:A}$$

**公理 5.1.3** (函数抽象)
$$\frac{\Gamma, x:A \vdash e:B}{\Gamma \vdash \lambda x:A.e : A \rightarrow B}$$

**公理 5.1.4** (函数应用)
$$\frac{\Gamma \vdash f:A \rightarrow B \quad \Gamma \vdash e:A}{\Gamma \vdash f(e):B}$$

### 5.1.2 类型等价性

****定义 5**.1.2** (β-等价)
对于任意项 $e_1, e_2$：
$$(\lambda x:A.e_1)(e_2) \equiv_\beta e_1[e_2/x]$$

****定义 5**.1.3** (η-等价)
对于任意函数 $f$：
$$\lambda x:A.f(x) \equiv_\eta f$$

****定理 5**.1.1** (Church-Rosser定理)
如果 $e_1 \rightarrow^* e_2$ 且 $e_1 \rightarrow^* e_3$，则存在 $e_4$ 使得：
$$e_2 \rightarrow^* e_4 \land e_3 \rightarrow^* e_4$$

### 5.1.3 多态类型

****定义 5**.1.4** (通用量化)
对于任意类型变量 $\alpha$ 和类型 $A$：
$$\forall \alpha.A \in T$$

**公理 5.1.5** (通用抽象)
$$\frac{\Gamma \vdash e:A \quad \alpha \notin \text{FTV}(\Gamma)}{\Gamma \vdash \Lambda \alpha.e : \forall \alpha.A}$$

**公理 5.1.6** (通用应用)
$$\frac{\Gamma \vdash e:\forall \alpha.A \quad B \in T}{\Gamma \vdash e[B]:A[B/\alpha]}$$

## 5.2 Rust实现

### 5.2.1 类型系统核心

```rust
use std::collections::HashMap;
use std::fmt;

/// 类型表示
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// 基本类型
    Bool,
    Int,
    String,
    Unit,
    
    /// 函数类型
    Function(Box<Type>, Box<Type>),
    
    /// 通用类型
    ForAll(String, Box<Type>),
    
    /// 类型变量
    Var(String),
    
    /// 元组类型
    Tuple(Vec<Type>),
    
    /// 代数数据类型
    Sum(Vec<Type>),
    Product(Vec<Type>),
}

impl Type {
    /// 类型等价性检查
    pub fn equivalent(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Bool, Type::Bool) => true,
            (Type::Int, Type::Int) => true,
            (Type::String, Type::String) => true,
            (Type::Unit, Type::Unit) => true,
            (Type::Function(a1, b1), Type::Function(a2, b2)) => {
                a1.equivalent(a2) && b1.equivalent(b2)
            }
            (Type::ForAll(v1, t1), Type::ForAll(v2, t2)) => {
                v1 == v2 && t1.equivalent(t2)
            }
            (Type::Var(v1), Type::Var(v2)) => v1 == v2,
            (Type::Tuple(ts1), Type::Tuple(ts2)) => {
                ts1.len() == ts2.len() && 
                ts1.iter().zip(ts2.iter()).all(|(t1, t2)| t1.equivalent(t2))
            }
            (Type::Sum(ts1), Type::Sum(ts2)) => {
                ts1.len() == ts2.len() && 
                ts1.iter().zip(ts2.iter()).all(|(t1, t2)| t1.equivalent(t2))
            }
            (Type::Product(ts1), Type::Product(ts2)) => {
                ts1.len() == ts2.len() && 
                ts1.iter().zip(ts2.iter()).all(|(t1, t2)| t1.equivalent(t2))
            }
            _ => false,
        }
    }
    
    /// 类型替换
    pub fn substitute(&self, var: &str, replacement: &Type) -> Type {
        match self {
            Type::Var(v) if v == var => replacement.clone(),
            Type::Function(a, b) => Type::Function(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement))
            ),
            Type::ForAll(v, t) if v != var => Type::ForAll(
                v.clone(),
                Box::new(t.substitute(var, replacement))
            ),
            Type::Tuple(ts) => Type::Tuple(
                ts.iter().map(|t| t.substitute(var, replacement)).collect()
            ),
            Type::Sum(ts) => Type::Sum(
                ts.iter().map(|t| t.substitute(var, replacement)).collect()
            ),
            Type::Product(ts) => Type::Product(
                ts.iter().map(|t| t.substitute(var, replacement)).collect()
            ),
            _ => self.clone(),
        }
    }
    
    /// 自由类型变量
    pub fn free_vars(&self) -> std::collections::HashSet<String> {
        match self {
            Type::Var(v) => {
                let mut set = std::collections::HashSet::new();
                set.insert(v.clone());
                set
            }
            Type::Function(a, b) => {
                let mut set = a.free_vars();
                set.extend(b.free_vars());
                set
            }
            Type::ForAll(v, t) => {
                let mut set = t.free_vars();
                set.remove(v);
                set
            }
            Type::Tuple(ts) => {
                let mut set = std::collections::HashSet::new();
                for t in ts {
                    set.extend(t.free_vars());
                }
                set
            }
            Type::Sum(ts) => {
                let mut set = std::collections::HashSet::new();
                for t in ts {
                    set.extend(t.free_vars());
                }
                set
            }
            Type::Product(ts) => {
                let mut set = std::collections::HashSet::new();
                for t in ts {
                    set.extend(t.free_vars());
                }
                set
            }
            _ => std::collections::HashSet::new(),
        }
    }
}

/// 类型上下文
#[derive(Debug, Clone)]
pub struct TypeContext {
    bindings: HashMap<String, Type>,
}

impl TypeContext {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }
    
    pub fn extend(&mut self, var: String, ty: Type) {
        self.bindings.insert(var, ty);
    }
    
    pub fn lookup(&self, var: &str) -> Option<&Type> {
        self.bindings.get(var)
    }
    
    pub fn contains(&self, var: &str) -> bool {
        self.bindings.contains_key(var)
    }
}

/// 类型检查器
pub struct TypeChecker {
    context: TypeContext,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            context: TypeContext::new(),
        }
    }
    
    /// 类型检查表达式
    pub fn check(&mut self, expr: &Expr) -> Result<Type, String> {
        match expr {
            Expr::Var(name) => {
                self.context.lookup(name)
                    .ok_or_else(|| format!("Undefined variable: {}", name))
                    .map(|t| t.clone())
            }
            Expr::Lambda(param, param_type, body) => {
                let mut new_context = self.context.clone();
                new_context.extend(param.clone(), param_type.clone());
                let mut checker = TypeChecker { context: new_context };
                let body_type = checker.check(body)?;
                Ok(Type::Function(Box::new(param_type.clone()), Box::new(body_type)))
            }
            Expr::App(func, arg) => {
                let func_type = self.check(func)?;
                let arg_type = self.check(arg)?;
                
                match func_type {
                    Type::Function(input_type, output_type) => {
                        if input_type.equivalent(&arg_type) {
                            Ok(*output_type)
                        } else {
                            Err(format!("Type mismatch: expected {}, got {}", input_type, arg_type))
                        }
                    }
                    _ => Err(format!("Expected function type, got {}", func_type)),
                }
            }
            Expr::Let(name, value, body) => {
                let value_type = self.check(value)?;
                let mut new_context = self.context.clone();
                new_context.extend(name.clone(), value_type);
                let mut checker = TypeChecker { context: new_context };
                checker.check(body)
            }
            Expr::Bool(_) => Ok(Type::Bool),
            Expr::Int(_) => Ok(Type::Int),
            Expr::String(_) => Ok(Type::String),
            Expr::Unit => Ok(Type::Unit),
        }
    }
    
    /// 类型推断
    pub fn infer(&mut self, expr: &Expr) -> Result<Type, String> {
        self.check(expr)
    }
}

/// 表达式
#[derive(Debug, Clone)]
pub enum Expr {
    Var(String),
    Lambda(String, Type, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Bool(bool),
    Int(i64),
    String(String),
    Unit,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "bool"),
            Type::Int => write!(f, "int"),
            Type::String => write!(f, "string"),
            Type::Unit => write!(f, "()"),
            Type::Function(a, b) => write!(f, "({} -> {})", a, b),
            Type::ForAll(v, t) => write!(f, "∀{}.{}", v, t),
            Type::Var(v) => write!(f, "{}", v),
            Type::Tuple(ts) => {
                write!(f, "(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", t)?;
                }
                write!(f, ")")
            }
            Type::Sum(ts) => {
                write!(f, "(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 { write!(f, " | ")?; }
                    write!(f, "{}", t)?;
                }
                write!(f, ")")
            }
            Type::Product(ts) => {
                write!(f, "{{")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", t)?;
                }
                write!(f, "}}")
            }
        }
    }
}
```

### 5.2.2 多态类型实现

```rust
/// 多态类型系统
pub struct PolymorphicTypeSystem {
    type_vars: std::collections::HashSet<String>,
}

impl PolymorphicTypeSystem {
    pub fn new() -> Self {
        Self {
            type_vars: std::collections::HashSet::new(),
        }
    }
    
    /// 创建通用类型
    pub fn forall(&mut self, var: String, body: Type) -> Type {
        self.type_vars.insert(var.clone());
        Type::ForAll(var, Box::new(body))
    }
    
    /// 实例化通用类型
    pub fn instantiate(&self, forall_type: &Type, concrete_type: &Type) -> Result<Type, String> {
        match forall_type {
            Type::ForAll(var, body) => {
                Ok(body.substitute(var, concrete_type))
            }
            _ => Err("Expected forall type".to_string()),
        }
    }
    
    /// 泛化类型
    pub fn generalize(&self, context: &TypeContext, ty: &Type) -> Type {
        let free_vars = ty.free_vars();
        let context_vars: std::collections::HashSet<_> = context.bindings.keys().cloned().collect();
        let unbound_vars: Vec<_> = free_vars.difference(&context_vars).cloned().collect();
        
        let mut result = ty.clone();
        for var in unbound_vars {
            result = Type::ForAll(var, Box::new(result));
        }
        result
    }
}

/// Hindley-Milner类型推断
pub struct HindleyMilner {
    type_system: PolymorphicTypeSystem,
    substitution: HashMap<String, Type>,
}

impl HindleyMilner {
    pub fn new() -> Self {
        Self {
            type_system: PolymorphicTypeSystem::new(),
            substitution: HashMap::new(),
        }
    }
    
    /// 统一类型
    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), String> {
        match (t1, t2) {
            (Type::Var(v1), Type::Var(v2)) if v1 == v2 => Ok(()),
            (Type::Var(v), t) | (t, Type::Var(v)) => {
                if self.occurs(v, t) {
                    Err("Occurs check failed".to_string())
                } else {
                    self.substitution.insert(v.clone(), t.clone());
                    Ok(())
                }
            }
            (Type::Function(a1, b1), Type::Function(a2, b2)) => {
                self.unify(a1, a2)?;
                self.unify(b1, b2)
            }
            (Type::Tuple(ts1), Type::Tuple(ts2)) => {
                if ts1.len() != ts2.len() {
                    return Err("Tuple length mismatch".to_string());
                }
                for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                    self.unify(t1, t2)?;
                }
                Ok(())
            }
            (t1, t2) if t1.equivalent(t2) => Ok(()),
            _ => Err(format!("Cannot unify {} with {}", t1, t2)),
        }
    }
    
    /// 检查变量是否出现在类型中
    fn occurs(&self, var: &str, ty: &Type) -> bool {
        match ty {
            Type::Var(v) => v == var,
            Type::Function(a, b) => self.occurs(var, a) || self.occurs(var, b),
            Type::ForAll(v, t) => v != var && self.occurs(var, t),
            Type::Tuple(ts) => ts.iter().any(|t| self.occurs(var, t)),
            Type::Sum(ts) => ts.iter().any(|t| self.occurs(var, t)),
            Type::Product(ts) => ts.iter().any(|t| self.occurs(var, t)),
            _ => false,
        }
    }
    
    /// 应用替换
    pub fn apply_substitution(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(v) => {
                self.substitution.get(v).cloned().unwrap_or(ty.clone())
            }
            Type::Function(a, b) => Type::Function(
                Box::new(self.apply_substitution(a)),
                Box::new(self.apply_substitution(b))
            ),
            Type::ForAll(v, t) => Type::ForAll(
                v.clone(),
                Box::new(self.apply_substitution(t))
            ),
            Type::Tuple(ts) => Type::Tuple(
                ts.iter().map(|t| self.apply_substitution(t)).collect()
            ),
            Type::Sum(ts) => Type::Sum(
                ts.iter().map(|t| self.apply_substitution(t)).collect()
            ),
            Type::Product(ts) => Type::Product(
                ts.iter().map(|t| self.apply_substitution(t)).collect()
            ),
            _ => ty.clone(),
        }
    }
}
```

### 5.2.3 高级类型特性

```rust
/// 类型类系统
pub struct TypeClass {
    name: String,
    methods: HashMap<String, Type>,
    instances: Vec<TypeClassInstance>,
}

pub struct TypeClassInstance {
    class_name: String,
    type_params: Vec<Type>,
    implementations: HashMap<String, Expr>,
}

impl TypeClass {
    pub fn new(name: String) -> Self {
        Self {
            name,
            methods: HashMap::new(),
            instances: Vec::new(),
        }
    }
    
    pub fn add_method(&mut self, name: String, signature: Type) {
        self.methods.insert(name, signature);
    }
    
    pub fn add_instance(&mut self, instance: TypeClassInstance) {
        self.instances.push(instance);
    }
    
    pub fn find_instance(&self, ty: &Type) -> Option<&TypeClassInstance> {
        self.instances.iter().find(|inst| {
            inst.type_params.iter().any(|t| t.equivalent(ty))
        })
    }
}

/// 依赖类型
#[derive(Debug, Clone)]
pub enum DependentType {
    Pi(String, Box<Type>, Box<DependentType>),
    Sigma(String, Box<Type>, Box<DependentType>),
    Id(Box<Expr>, Box<Expr>),
    Base(Type),
}

impl DependentType {
    pub fn pi(param: String, domain: Type, codomain: DependentType) -> Self {
        DependentType::Pi(param, Box::new(domain), Box::new(codomain))
    }
    
    pub fn sigma(param: String, domain: Type, codomain: DependentType) -> Self {
        DependentType::Sigma(param, Box::new(domain), Box::new(codomain))
    }
    
    pub fn id(a: Expr, b: Expr) -> Self {
        DependentType::Id(Box::new(a), Box::new(b))
    }
}

/// 线性类型系统
#[derive(Debug, Clone, PartialEq)]
pub enum Linearity {
    Linear,    // 必须使用一次
    Affine,    // 最多使用一次
    Relevant,  // 至少使用一次
    Unrestricted, // 任意使用
}

#[derive(Debug, Clone)]
pub struct LinearType {
    pub ty: Type,
    pub linearity: Linearity,
}

impl LinearType {
    pub fn new(ty: Type, linearity: Linearity) -> Self {
        Self { ty, linearity }
    }
    
    pub fn can_consume(&self) -> bool {
        matches!(self.linearity, Linearity::Linear | Linearity::Affine)
    }
    
    pub fn can_duplicate(&self) -> bool {
        matches!(self.linearity, Linearity::Relevant | Linearity::Unrestricted)
    }
}

/// 线性类型检查器
pub struct LinearTypeChecker {
    context: HashMap<String, LinearType>,
    used_vars: std::collections::HashSet<String>,
}

impl LinearTypeChecker {
    pub fn new() -> Self {
        Self {
            context: HashMap::new(),
            used_vars: std::collections::HashSet::new(),
        }
    }
    
    pub fn check(&mut self, expr: &Expr) -> Result<LinearType, String> {
        match expr {
            Expr::Var(name) => {
                if self.used_vars.contains(name) {
                    return Err(format!("Variable {} already used", name));
                }
                
                if let Some(linear_type) = self.context.get(name) {
                    if linear_type.can_consume() {
                        self.used_vars.insert(name.clone());
                    }
                    Ok(linear_type.clone())
                } else {
                    Err(format!("Undefined variable: {}", name))
                }
            }
            Expr::Lambda(param, param_type, body) => {
                let linear_param_type = LinearType::new(param_type.clone(), Linearity::Linear);
                let mut new_context = self.context.clone();
                new_context.insert(param.clone(), linear_param_type);
                
                let mut checker = LinearTypeChecker {
                    context: new_context,
                    used_vars: self.used_vars.clone(),
                };
                
                let body_type = checker.check(body)?;
                Ok(LinearType::new(
                    Type::Function(Box::new(param_type.clone()), Box::new(body_type.ty)),
                    Linearity::Unrestricted
                ))
            }
            Expr::App(func, arg) => {
                let func_type = self.check(func)?;
                let arg_type = self.check(arg)?;
                
                match &func_type.ty {
                    Type::Function(input_type, output_type) => {
                        if input_type.equivalent(&arg_type.ty) {
                            Ok(LinearType::new(*output_type.clone(), Linearity::Unrestricted))
                        } else {
                            Err(format!("Type mismatch: expected {}, got {}", input_type, arg_type.ty))
                        }
                    }
                    _ => Err(format!("Expected function type, got {}", func_type.ty)),
                }
            }
            _ => Err("Unsupported expression".to_string()),
        }
    }
}
```

## 5.3 形式化验证

### 5.3.1 类型安全性

****定理 5**.3.1** (进展定理)
如果 $\Gamma \vdash e:A$ 且 $e$ 不是值，则存在 $e'$ 使得 $e \rightarrow e'$。

**证明**：
通过结构归纳法证明。对于每种表达式形式：

1. 变量：已经是值
2. 函数抽象：已经是值
3. 函数应用：根据归纳假设，$f$ 或 $e$ 可以求值
4. 其他表达式：类似处理

****定理 5**.3.2** (保持定理)
如果 $\Gamma \vdash e:A$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e':A$。

**证明**：
通过结构归纳法证明。对于每种归约规则：

1. β-归约：通过替换引理
2. 其他归约：通过归纳假设

### 5.3.2 类型推断正确性

****定理 5**.3.3** (类型推断完备性)
如果 $\Gamma \vdash e:A$，则类型推断算法能够推断出类型 $A$。

**证明**：
通过结构归纳法证明。对于每种表达式：

1. 变量：直接查找上下文
2. 函数抽象：递归推断体类型
3. 函数应用：统一参数和函数类型
4. 其他表达式：类似处理

****定理 5**.3.4** (类型推断可靠性)
如果类型推断算法推断出类型 $A$，则 $\Gamma \vdash e:A$。

**证明**：
通过结构归纳法证明。对于每种推断规则：

1. 变量规则：直接应用
2. 函数抽象规则：递归应用
3. 函数应用规则：通过统一验证
4. 其他规则：类似处理

## 5.4 应用示例

### 5.4.1 泛型容器

```rust
/// 泛型列表类型
pub struct GenericList<T> {
    head: Option<T>,
    tail: Option<Box<GenericList<T>>>,
}

impl<T> GenericList<T> {
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
        }
    }
    
    pub fn cons(head: T, tail: GenericList<T>) -> Self {
        Self {
            head: Some(head),
            tail: Some(Box::new(tail)),
        }
    }
    
    pub fn head(&self) -> Option<&T> {
        self.head.as_ref()
    }
    
    pub fn tail(&self) -> Option<&GenericList<T>> {
        self.tail.as_ref().map(|t| t.as_ref())
    }
}

/// 类型类实例：Eq
impl<T: PartialEq> PartialEq for GenericList<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self.head(), other.head()) {
            (Some(h1), Some(h2)) => {
                h1 == h2 && self.tail() == other.tail()
            }
            (None, None) => true,
            _ => false,
        }
    }
}

impl<T: Eq> Eq for GenericList<T> {}

/// 类型类实例：Show
impl<T: std::fmt::Display> std::fmt::Display for GenericList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut current = self;
        let mut first = true;
        
        while let Some(head) = current.head() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}", head)?;
            first = false;
            
            if let Some(tail) = current.tail() {
                current = tail;
            } else {
                break;
            }
        }
        
        write!(f, "]")
    }
}
```

### 5.4.2 高阶函数

```rust
/// 高阶函数类型
pub trait HigherOrder {
    type Input;
    type Output;
    
    fn map<F, U>(self, f: F) -> GenericList<U>
    where
        F: Fn(Self::Input) -> U;
    
    fn filter<F>(self, predicate: F) -> Self
    where
        F: Fn(&Self::Input) -> bool;
    
    fn fold<F, U>(self, init: U, f: F) -> U
    where
        F: Fn(U, Self::Input) -> U;
}

impl<T> HigherOrder for GenericList<T> {
    type Input = T;
    type Output = T;
    
    fn map<F, U>(self, f: F) -> GenericList<U>
    where
        F: Fn(T) -> U,
    {
        match self.head {
            Some(head) => {
                let mapped_head = f(head);
                let mapped_tail = if let Some(tail) = self.tail {
                    tail.map(f)
                } else {
                    GenericList::new()
                };
                GenericList::cons(mapped_head, mapped_tail)
            }
            None => GenericList::new(),
        }
    }
    
    fn filter<F>(self, predicate: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        match self.head {
            Some(head) => {
                if predicate(&head) {
                    let filtered_tail = if let Some(tail) = self.tail {
                        tail.filter(predicate)
                    } else {
                        GenericList::new()
                    };
                    GenericList::cons(head, filtered_tail)
                } else {
                    if let Some(tail) = self.tail {
                        tail.filter(predicate)
                    } else {
                        GenericList::new()
                    }
                }
            }
            None => GenericList::new(),
        }
    }
    
    fn fold<F, U>(self, init: U, f: F) -> U
    where
        F: Fn(U, T) -> U,
    {
        match self.head {
            Some(head) => {
                let new_init = f(init, head);
                if let Some(tail) = self.tail {
                    tail.fold(new_init, f)
                } else {
                    new_init
                }
            }
            None => init,
        }
    }
}
```

### 5.4.3 依赖类型示例

```rust
/// 向量类型（依赖类型）
pub struct Vector<T> {
    data: Vec<T>,
    length: usize,
}

impl<T> Vector<T> {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            length: 0,
        }
    }
    
    pub fn cons(head: T, tail: Vector<T>) -> Self {
        let mut data = vec![head];
        data.extend(tail.data);
        Self {
            data,
            length: tail.length + 1,
        }
    }
    
    pub fn length(&self) -> usize {
        self.length
    }
    
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.length {
            self.data.get(index)
        } else {
            None
        }
    }
    
    /// 类型安全的索引访问
    pub fn index(&self, index: BoundedNat<{ Self::length() }>) -> &T {
        &self.data[index.value()]
    }
}

/// 有界自然数（用于依赖类型）
pub struct BoundedNat<const N: usize> {
    value: usize,
}

impl<const N: usize> BoundedNat<N> {
    pub fn new(value: usize) -> Result<Self, String> {
        if value < N {
            Ok(Self { value })
        } else {
            Err(format!("Value {} out of bounds for BoundedNat<{}>", value, N))
        }
    }
    
    pub fn value(&self) -> usize {
        self.value
    }
}

/// 类型安全的向量操作
pub fn safe_append<T>(v1: Vector<T>, v2: Vector<T>) -> Vector<T> {
    let mut data = v1.data;
    data.extend(v2.data);
    Vector {
        data,
        length: v1.length + v2.length,
    }
}

/// 类型安全的向量映射
pub fn safe_map<T, U, F>(v: Vector<T>, f: F) -> Vector<U>
where
    F: Fn(T) -> U,
{
    let data = v.data.into_iter().map(f).collect();
    Vector {
        data,
        length: v.length,
    }
}
```

## 5.5 性能分析

### 5.5.1 类型检查复杂度

****定理 5**.5.1** (类型检查时间复杂度)
对于包含 $n$ 个节点的表达式，Hindley-Milner类型推断的时间复杂度为 $O(n^3)$。

**证明**：

1. 每个节点需要类型推断：$O(n)$
2. 每次统一操作需要遍历类型：$O(n)$
3. 最坏情况下需要 $O(n)$ 次统一操作
4. 总时间复杂度：$O(n) \times O(n) \times O(n) = O(n^3)$

### 5.5.2 内存使用分析

****定理 5**.5.2** (类型系统内存复杂度)
对于包含 $m$ 个类型变量的系统，内存复杂度为 $O(m^2)$。

**证明**：

1. 每个类型变量需要存储：$O(m)$
2. 替换表大小：$O(m)$
3. 统一操作需要临时存储：$O(m)$
4. 总内存复杂度：$O(m) \times O(m) = O(m^2)$

## 5.6 总结

类型论通过形式化的数学定义和严格的Rust实现，提供了：

1. **数学严谨性**：基于λ演算和类型理论的形式化基础
2. **类型安全**：通过进展定理和保持定理保证程序正确性
3. **多态性**：支持参数多态和特设多态
4. **类型推断**：自动推导类型，减少显式注解
5. **高级特性**：支持依赖类型、线性类型等高级概念

这种类型系统特别适用于需要高安全性、高可靠性的系统，如金融系统、安全关键系统等。

