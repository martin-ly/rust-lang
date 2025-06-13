# Rust类型系统形式化重构

## 目录

1. [理论基础](#1-理论基础)
2. [类型系统五元组定义](#2-类型系统五元组定义)
3. [基础类型理论](#3-基础类型理论)
4. [复合类型理论](#4-复合类型理论)
5. [泛型类型理论](#5-泛型类型理论)
6. [Trait系统理论](#6-trait系统理论)
7. [类型推断理论](#7-类型推断理论)
8. [核心定理证明](#8-核心定理证明)
9. [Rust实现](#9-rust实现)

## 1. 理论基础

### 1.1 类型论基础

**定义1.1 (类型)**
类型 $T$ 是一个值的集合，满足：
$$T = \{v \mid \text{TypeOf}(v) = T\}$$

**定义1.2 (类型关系)**
类型关系 $\text{TypeRelation}: \text{Type} \times \text{Type} \rightarrow \text{Boolean}$ 定义为：
$$\text{TypeRelation}(T_1, T_2) = \begin{cases}
\text{true} & \text{if } T_1 \subseteq T_2 \\
\text{false} & \text{otherwise}
\end{cases}$$

**定义1.3 (类型函数)**
类型函数 $\text{TypeOf}: \text{Value} \rightarrow \text{Type}$ 定义为：
$$\text{TypeOf}(v) = T \text{ where } v \in T$$

### 1.2 类型系统基础

**定义1.4 (类型系统)**
类型系统 $TS = (T, R, C, I)$ 包含：
- $T$: 类型集合
- $R$: 类型规则集合
- $C$: 类型约束集合
- $I$: 类型推断规则集合

**定义1.5 (类型环境)**
类型环境 $\Gamma: \text{Variable} \rightarrow \text{Type}$ 定义为：
$$\Gamma(x) = T \text{ where } x: T$$

## 2. 类型系统五元组定义

**定义2.1 (Rust类型系统)**
Rust类型系统 $RTS = (B, C, G, T, L)$ 包含：

- **B (Basic Types)**: 基础类型系统 $B = (I, F, B, C, S)$
  - $I$: 整数类型集合
  - $F$: 浮点类型集合
  - $B$: 布尔类型
  - $C$: 字符类型
  - $S$: 字符串类型

- **C (Compound Types)**: 复合类型系统 $C = (A, T, E, S)$
  - $A$: 数组类型
  - $T$: 元组类型
  - $E$: 枚举类型
  - $S$: 结构体类型

- **G (Generic Types)**: 泛型类型系统 $G = (P, C, I, B)$
  - $P$: 类型参数集合
  - $C$: 类型约束集合
  - $I$: 类型推断
  - $B$: 类型绑定

- **T (Trait System)**: Trait系统 $T = (T, I, D, A)$
  - $T$: Trait定义集合
  - $I$: Trait实现集合
  - $D$: Trait派生集合
  - $A$: Trait关联类型

- **L (Lifetime System)**: 生命周期系统 $L = (L, R, C, I)$
  - $L$: 生命周期参数集合
  - $R$: 生命周期规则集合
  - $C$: 生命周期约束集合
  - $I$: 生命周期推断

## 3. 基础类型理论

### 3.1 整数类型理论

**定义3.1 (整数类型)**
整数类型集合 $I = \{i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize\}$

**定义3.2 (整数类型关系)**
整数类型关系 $\text{IntTypeRelation}: I \times I \rightarrow \text{Boolean}$ 定义为：
$$\text{IntTypeRelation}(i_1, i_2) = \begin{cases}
\text{true} & \text{if } \text{Size}(i_1) \leq \text{Size}(i_2) \\
\text{false} & \text{otherwise}
\end{cases}$$

**定义3.3 (整数类型大小)**
整数类型大小函数 $\text{Size}: I \rightarrow \mathbb{N}$ 定义为：
$$\text{Size}(i) = \begin{cases}
8 & \text{if } i = i8 \text{ or } u8 \\
16 & \text{if } i = i16 \text{ or } u16 \\
32 & \text{if } i = i32 \text{ or } u32 \\
64 & \text{if } i = i64 \text{ or } u64 \\
128 & \text{if } i = i128 \text{ or } u128 \\
\text{platform} & \text{if } i = isize \text{ or } usize
\end{cases}$$

### 3.2 浮点类型理论

**定义3.4 (浮点类型)**
浮点类型集合 $F = \{f32, f64\}$

**定义3.5 (浮点精度)**
浮点精度函数 $\text{Precision}: F \rightarrow \mathbb{N}$ 定义为：
$$\text{Precision}(f) = \begin{cases}
24 & \text{if } f = f32 \\
53 & \text{if } f = f64
\end{cases}$$

### 3.3 布尔类型理论

**定义3.6 (布尔类型)**
布尔类型 $B = \{\text{true}, \text{false}\}$

**定义3.7 (布尔运算)**
布尔运算函数 $\text{BoolOp}: B \times B \times \text{Operator} \rightarrow B$ 定义为：
$$\text{BoolOp}(b_1, b_2, op) = \begin{cases}
b_1 \land b_2 & \text{if } op = \text{AND} \\
b_1 \lor b_2 & \text{if } op = \text{OR} \\
\neg b_1 & \text{if } op = \text{NOT}
\end{cases}$$

## 4. 复合类型理论

### 4.1 数组类型理论

**定义4.1 (数组类型)**
数组类型 $A = T[n]$ 定义为：
$$A = \{(v_0, v_1, \ldots, v_{n-1}) \mid v_i \in T, i \in [0, n-1]\}$$

**定义4.2 (数组访问)**
数组访问函数 $\text{ArrayAccess}: A \times \mathbb{N} \rightarrow T$ 定义为：
$$\text{ArrayAccess}(arr, i) = arr[i] \text{ where } 0 \leq i < n$$

**定义4.3 (数组长度)**
数组长度函数 $\text{ArrayLength}: A \rightarrow \mathbb{N}$ 定义为：
$$\text{ArrayLength}(arr) = n$$

### 4.2 元组类型理论

**定义4.2 (元组类型)**
元组类型 $T = (T_1, T_2, \ldots, T_n)$ 定义为：
$$T = \{(v_1, v_2, \ldots, v_n) \mid v_i \in T_i, i \in [1, n]\}$$

**定义4.3 (元组投影)**
元组投影函数 $\text{TupleProject}: T \times \mathbb{N} \rightarrow T_i$ 定义为：
$$\text{TupleProject}(t, i) = t.i \text{ where } 1 \leq i \leq n$$

### 4.3 枚举类型理论

**定义4.4 (枚举类型)**
枚举类型 $E = \text{enum} \{V_1(T_1), V_2(T_2), \ldots, V_n(T_n)\}$ 定义为：
$$E = \bigcup_{i=1}^{n} \{V_i(v) \mid v \in T_i\}$$

**定义4.5 (枚举变体)**
枚举变体函数 $\text{EnumVariant}: E \rightarrow \{V_1, V_2, \ldots, V_n\}$ 定义为：
$$\text{EnumVariant}(V_i(v)) = V_i$$

**定义4.6 (枚举值)**
枚举值函数 $\text{EnumValue}: E \rightarrow \bigcup_{i=1}^{n} T_i$ 定义为：
$$\text{EnumValue}(V_i(v)) = v$$

### 4.4 结构体类型理论

**定义4.7 (结构体类型)**
结构体类型 $S = \text{struct} \{f_1: T_1, f_2: T_2, \ldots, f_n: T_n\}$ 定义为：
$$S = \{(f_1: v_1, f_2: v_2, \ldots, f_n: v_n) \mid v_i \in T_i, i \in [1, n]\}$$

**定义4.8 (字段访问)**
字段访问函数 $\text{FieldAccess}: S \times \text{Field} \rightarrow T_i$ 定义为：
$$\text{FieldAccess}(s, f_i) = s.f_i$$

## 5. 泛型类型理论

### 5.1 泛型类型定义

**定义5.1 (泛型类型)**
泛型类型 $G = \forall \alpha_1, \alpha_2, \ldots, \alpha_n. T(\alpha_1, \alpha_2, \ldots, \alpha_n)$ 定义为：
$$G = \{T(\tau_1, \tau_2, \ldots, \tau_n) \mid \tau_i \in \text{Type}, i \in [1, n]\}$$

**定义5.2 (类型参数)**
类型参数 $\alpha$ 是一个类型变量，可以绑定到任意类型。

**定义5.3 (类型实例化)**
类型实例化函数 $\text{Instantiate}: G \times \text{Type}^n \rightarrow T$ 定义为：
$$\text{Instantiate}(G, \tau_1, \tau_2, \ldots, \tau_n) = T(\tau_1, \tau_2, \ldots, \tau_n)$$

### 5.2 类型约束理论

**定义5.4 (类型约束)**
类型约束 $C = \alpha: \text{Trait}$ 定义为：
$$C = \{\tau \mid \tau \text{ implements Trait}\}$$

**定义5.5 (约束满足)**
约束满足关系 $\text{Satisfies}: \text{Type} \times \text{Constraint} \rightarrow \text{Boolean}$ 定义为：
$$\text{Satisfies}(\tau, C) = \begin{cases}
\text{true} & \text{if } \tau \text{ implements the trait in } C \\
\text{false} & \text{otherwise}
\end{cases}$$

### 5.3 泛型函数理论

**定义5.6 (泛型函数)**
泛型函数 $F = \forall \alpha: C. T_1 \rightarrow T_2$ 定义为：
$$F = \{\lambda x: \tau_1. e \mid \tau_1 \in C, e: \tau_2\}$$

**定义5.7 (函数应用)**
函数应用 $\text{Apply}: F \times T_1 \rightarrow T_2$ 定义为：
$$\text{Apply}(f, v) = f(v)$$

## 6. Trait系统理论

### 6.1 Trait定义理论

**定义6.1 (Trait)**
Trait $T = \text{trait} \{m_1: T_1 \rightarrow T_2, m_2: T_3 \rightarrow T_4, \ldots\}$ 定义为：
$$T = \{\text{methods} \mid \text{methods implement the trait interface}\}$$

**定义6.2 (Trait方法)**
Trait方法 $m: T_1 \rightarrow T_2$ 是一个函数签名，定义了方法的输入和输出类型。

**定义6.3 (Trait实现)**
Trait实现 $\text{Impl}: \text{Type} \times \text{Trait} \rightarrow \text{Boolean}$ 定义为：
$$\text{Impl}(\tau, T) = \begin{cases}
\text{true} & \text{if } \tau \text{ implements } T \\
\text{false} & \text{otherwise}
\end{cases}$$

### 6.2 关联类型理论

**定义6.4 (关联类型)**
关联类型 $\text{AssociatedType}: \text{Trait} \times \text{TypeParam} \rightarrow \text{Type}$ 定义为：
$$\text{AssociatedType}(T, \alpha) = \text{the type associated with } \alpha \text{ in } T$$

**定义6.5 (关联类型约束)**
关联类型约束 $\text{AssociatedTypeConstraint}: \text{AssociatedType} \times \text{Constraint} \rightarrow \text{Boolean}$ 定义为：
$$\text{AssociatedTypeConstraint}(AT, C) = AT \text{ satisfies } C$$

### 6.3 Trait对象理论

**定义6.6 (Trait对象)**
Trait对象 $\text{TraitObject} = \text{dyn Trait}$ 定义为：
$$\text{TraitObject} = \{\text{values that implement Trait}\}$$

**定义6.7 (Trait对象方法调用)**
Trait对象方法调用 $\text{TraitMethodCall}: \text{TraitObject} \times \text{Method} \times \text{Args} \rightarrow \text{Result}$ 定义为：
$$\text{TraitMethodCall}(obj, m, args) = \text{dynamic dispatch of method } m$$

## 7. 类型推断理论

### 7.1 类型推断算法

**定义7.1 (类型推断)**
类型推断函数 $\text{Infer}: \text{Expression} \times \Gamma \rightarrow \text{Type}$ 定义为：
$$\text{Infer}(e, \Gamma) = T \text{ where } \Gamma \vdash e: T$$

**定义7.2 (类型推断规则)**
类型推断规则集合 $IR = \{IR_1, IR_2, \ldots, IR_n\}$ 包含：

1. **变量规则**: $\frac{x: T \in \Gamma}{\Gamma \vdash x: T}$
2. **函数规则**: $\frac{\Gamma \vdash e_1: T_1 \rightarrow T_2 \quad \Gamma \vdash e_2: T_1}{\Gamma \vdash e_1(e_2): T_2}$
3. **抽象规则**: $\frac{\Gamma, x: T_1 \vdash e: T_2}{\Gamma \vdash \lambda x. e: T_1 \rightarrow T_2}$

### 7.2 统一算法

**定义7.3 (类型统一)**
类型统一函数 $\text{Unify}: \text{Type} \times \text{Type} \rightarrow \text{Substitution}$ 定义为：
$$\text{Unify}(T_1, T_2) = \sigma \text{ where } \sigma(T_1) = \sigma(T_2)$$

**定义7.4 (替换)**
替换函数 $\text{Substitute}: \text{Type} \times \text{Substitution} \rightarrow \text{Type}$ 定义为：
$$\text{Substitute}(T, \sigma) = \sigma(T)$$

## 8. 核心定理证明

### 8.1 类型安全定理

**定理8.1 (类型安全)**
如果表达式 $e$ 通过类型检查，则 $e$ 不会出现类型错误。

**证明**:
设 $e$ 为通过类型检查的表达式，即 $\Gamma \vdash e: T$。

根据类型推断规则，所有子表达式都有明确的类型，且类型关系满足：
$$\forall e' \subseteq e: \Gamma \vdash e': T'$$

这意味着：
1. 所有变量都有明确的类型
2. 所有操作都满足类型约束
3. 所有函数调用都满足类型签名

因此表达式不会出现类型错误。$\square$

### 8.2 类型推断完备性定理

**定理8.2 (类型推断完备性)**
如果表达式 $e$ 有类型 $T$，则类型推断算法能够推断出 $T$。

**证明**:
设 $e$ 为有类型 $T$ 的表达式，即 $\Gamma \vdash e: T$。

根据类型推断算法的定义，算法会遍历表达式的所有子表达式，应用相应的类型推断规则。

由于所有类型推断规则都是完备的，算法最终会推断出类型 $T$。

因此类型推断算法是完备的。$\square$

### 8.3 泛型类型安全定理

**定理8.3 (泛型类型安全)**
如果泛型函数 $f$ 通过类型检查，则 $f$ 的所有实例化都是类型安全的。

**证明**:
设 $f = \forall \alpha: C. T_1 \rightarrow T_2$ 为通过类型检查的泛型函数。

对于任意类型 $\tau$ 满足约束 $C$，实例化 $f(\tau)$ 的类型为 $\tau_1 \rightarrow \tau_2$。

由于 $\tau$ 满足约束 $C$，函数体中的所有操作都是类型安全的。

因此泛型函数的所有实例化都是类型安全的。$\square$

### 8.4 Trait实现一致性定理

**定理8.4 (Trait实现一致性)**
如果类型 $\tau$ 实现Trait $T$，则 $\tau$ 的所有Trait方法实现都满足Trait的接口规范。

**证明**:
设 $\tau$ 为实现Trait $T$ 的类型，即 $\text{Impl}(\tau, T) = \text{true}$。

根据Trait实现的定义，$\tau$ 必须提供所有Trait方法的实现，且这些实现必须满足方法签名。

因此 $\tau$ 的所有Trait方法实现都满足Trait的接口规范。$\square$

### 8.5 生命周期安全定理

**定理8.5 (生命周期安全)**
如果引用 $r$ 通过生命周期检查，则 $r$ 不会出现悬垂引用。

**证明**:
设 $r$ 为通过生命周期检查的引用，即 $\text{LifetimeCheck}(r) = \text{true}$。

根据生命周期检查的定义，$r$ 的生命周期必须包含在其指向值的生命周期内：
$$\text{Lifetime}(r) \subseteq \text{Lifetime}(\text{Value}(r))$$

这意味着 $r$ 在其生命周期内始终指向有效的值。

因此 $r$ 不会出现悬垂引用。$\square$

## 9. Rust实现

### 9.1 基础类型实现

```rust
/// 基础类型枚举
#[derive(Debug, Clone, PartialEq)]
pub enum BasicType {
    Integer(IntegerType),
    Float(FloatType),
    Boolean,
    Character,
    String,
}

/// 整数类型
#[derive(Debug, Clone, PartialEq)]
pub enum IntegerType {
    I8, I16, I32, I64, I128, ISize,
    U8, U16, U32, U64, U128, USize,
}

/// 浮点类型
#[derive(Debug, Clone, PartialEq)]
pub enum FloatType {
    F32, F64,
}

impl BasicType {
    /// 获取类型大小
    pub fn size(&self) -> usize {
        match self {
            BasicType::Integer(i) => match i {
                IntegerType::I8 | IntegerType::U8 => 1,
                IntegerType::I16 | IntegerType::U16 => 2,
                IntegerType::I32 | IntegerType::U32 => 4,
                IntegerType::I64 | IntegerType::U64 => 8,
                IntegerType::I128 | IntegerType::U128 => 16,
                IntegerType::ISize | IntegerType::USize => std::mem::size_of::<isize>(),
            },
            BasicType::Float(f) => match f {
                FloatType::F32 => 4,
                FloatType::F64 => 8,
            },
            BasicType::Boolean => 1,
            BasicType::Character => 4,
            BasicType::String => std::mem::size_of::<String>(),
        }
    }
}
```

### 9.2 复合类型实现

```rust
/// 复合类型枚举
#[derive(Debug, Clone, PartialEq)]
pub enum CompoundType {
    Array(Box<Type>, usize),
    Tuple(Vec<Type>),
    Enum(EnumType),
    Struct(StructType),
}

/// 枚举类型
#[derive(Debug, Clone, PartialEq)]
pub struct EnumType {
    pub name: String,
    pub variants: Vec<EnumVariant>,
}

/// 枚举变体
#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    pub data_type: Option<Type>,
}

/// 结构体类型
#[derive(Debug, Clone, PartialEq)]
pub struct StructType {
    pub name: String,
    pub fields: Vec<StructField>,
}

/// 结构体字段
#[derive(Debug, Clone, PartialEq)]
pub struct StructField {
    pub name: String,
    pub field_type: Type,
}

impl CompoundType {
    /// 获取数组元素类型
    pub fn array_element_type(&self) -> Option<&Type> {
        match self {
            CompoundType::Array(element_type, _) => Some(element_type),
            _ => None,
        }
    }
    
    /// 获取数组长度
    pub fn array_length(&self) -> Option<usize> {
        match self {
            CompoundType::Array(_, length) => Some(*length),
            _ => None,
        }
    }
    
    /// 获取元组字段类型
    pub fn tuple_field_types(&self) -> Option<&Vec<Type>> {
        match self {
            CompoundType::Tuple(field_types) => Some(field_types),
            _ => None,
        }
    }
}
```

### 9.3 泛型类型实现

```rust
/// 泛型类型
#[derive(Debug, Clone, PartialEq)]
pub struct GenericType {
    pub type_params: Vec<TypeParam>,
    pub constraints: Vec<TypeConstraint>,
    pub base_type: Type,
}

/// 类型参数
#[derive(Debug, Clone, PartialEq)]
pub struct TypeParam {
    pub name: String,
    pub bounds: Vec<TraitBound>,
}

/// 类型约束
#[derive(Debug, Clone, PartialEq)]
pub struct TypeConstraint {
    pub param: String,
    pub trait_bound: TraitBound,
}

/// Trait约束
#[derive(Debug, Clone, PartialEq)]
pub struct TraitBound {
    pub trait_name: String,
    pub associated_types: Vec<AssociatedType>,
}

/// 关联类型
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedType {
    pub name: String,
    pub bound: Option<Type>,
}

impl GenericType {
    /// 实例化泛型类型
    pub fn instantiate(&self, type_args: &[Type]) -> Result<Type, TypeError> {
        if type_args.len() != self.type_params.len() {
            return Err(TypeError::TypeArgCountMismatch);
        }
        
        // 创建类型替换映射
        let mut substitutions = HashMap::new();
        for (param, arg) in self.type_params.iter().zip(type_args.iter()) {
            substitutions.insert(param.name.clone(), arg.clone());
        }
        
        // 应用替换到基础类型
        self.base_type.substitute(&substitutions)
    }
    
    /// 检查类型约束
    pub fn check_constraints(&self, type_args: &[Type]) -> Result<(), TypeError> {
        for constraint in &self.constraints {
            let arg = type_args.iter()
                .find(|arg| arg.name() == constraint.param)
                .ok_or(TypeError::TypeParamNotFound)?;
            
            if !arg.implements_trait(&constraint.trait_bound.trait_name) {
                return Err(TypeError::TraitConstraintViolation);
            }
        }
        Ok(())
    }
}
```

### 9.4 Trait系统实现

```rust
/// Trait定义
#[derive(Debug, Clone, PartialEq)]
pub struct Trait {
    pub name: String,
    pub methods: Vec<TraitMethod>,
    pub associated_types: Vec<AssociatedTypeDef>,
}

/// Trait方法
#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethod {
    pub name: String,
    pub signature: FunctionSignature,
}

/// 函数签名
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionSignature {
    pub params: Vec<Type>,
    pub return_type: Type,
}

/// 关联类型定义
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedTypeDef {
    pub name: String,
    pub bound: Option<Type>,
}

/// Trait实现
#[derive(Debug, Clone, PartialEq)]
pub struct TraitImpl {
    pub trait_name: String,
    pub for_type: Type,
    pub methods: Vec<MethodImpl>,
    pub associated_types: Vec<AssociatedTypeImpl>,
}

/// 方法实现
#[derive(Debug, Clone, PartialEq)]
pub struct MethodImpl {
    pub name: String,
    pub implementation: FunctionBody,
}

/// 关联类型实现
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedTypeImpl {
    pub name: String,
    pub type_value: Type,
}

impl Trait {
    /// 检查方法实现
    pub fn check_implementation(&self, impl_block: &TraitImpl) -> Result<(), TraitError> {
        // 检查所有必需的方法都已实现
        for method in &self.methods {
            let impl_method = impl_block.methods.iter()
                .find(|m| m.name == method.name)
                .ok_or(TraitError::MissingMethod(method.name.clone()))?;
            
            // 检查方法签名匹配
            if impl_method.implementation.signature != method.signature {
                return Err(TraitError::SignatureMismatch(method.name.clone()));
            }
        }
        
        // 检查所有关联类型都已实现
        for assoc_type in &self.associated_types {
            let impl_assoc_type = impl_block.associated_types.iter()
                .find(|at| at.name == assoc_type.name)
                .ok_or(TraitError::MissingAssociatedType(assoc_type.name.clone()))?;
            
            // 检查关联类型约束
            if let Some(bound) = &assoc_type.bound {
                if !impl_assoc_type.type_value.satisfies_constraint(bound) {
                    return Err(TraitError::AssociatedTypeConstraintViolation(assoc_type.name.clone()));
                }
            }
        }
        
        Ok(())
    }
}
```

### 9.5 类型推断实现

```rust
/// 类型推断器
pub struct TypeInferrer {
    type_env: HashMap<String, Type>,
    constraints: Vec<TypeConstraint>,
}

impl TypeInferrer {
    /// 推断表达式类型
    pub fn infer_type(&mut self, expr: &Expression) -> Result<Type, TypeError> {
        match expr {
            Expression::Variable(name) => {
                self.type_env.get(name)
                    .cloned()
                    .ok_or(TypeError::UnboundVariable(name.clone()))
            },
            Expression::Literal(lit) => {
                Ok(self.infer_literal_type(lit))
            },
            Expression::BinaryOp(op, left, right) => {
                self.infer_binary_op_type(op, left, right)
            },
            Expression::FunctionCall(func, args) => {
                self.infer_function_call_type(func, args)
            },
            Expression::Lambda(param, body) => {
                self.infer_lambda_type(param, body)
            },
        }
    }
    
    /// 推断字面量类型
    fn infer_literal_type(&self, lit: &Literal) -> Type {
        match lit {
            Literal::Integer(_) => Type::Basic(BasicType::Integer(IntegerType::I32)),
            Literal::Float(_) => Type::Basic(BasicType::Float(FloatType::F64)),
            Literal::Boolean(_) => Type::Basic(BasicType::Boolean),
            Literal::String(_) => Type::Basic(BasicType::String),
            Literal::Character(_) => Type::Basic(BasicType::Character),
        }
    }
    
    /// 推断二元操作类型
    fn infer_binary_op_type(&mut self, op: &BinaryOp, left: &Expression, right: &Expression) -> Result<Type, TypeError> {
        let left_type = self.infer_type(left)?;
        let right_type = self.infer_type(right)?;
        
        // 添加类型约束
        self.constraints.push(TypeConstraint {
            left: left_type.clone(),
            right: right_type.clone(),
            constraint: ConstraintKind::Equal,
        });
        
        // 根据操作符推断返回类型
        match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                if left_type.is_numeric() && right_type.is_numeric() {
                    Ok(self.unify_numeric_types(&left_type, &right_type))
                } else {
                    Err(TypeError::TypeMismatch)
                }
            },
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                if left_type == right_type {
                    Ok(Type::Basic(BasicType::Boolean))
                } else {
                    Err(TypeError::TypeMismatch)
                }
            },
            BinaryOp::And | BinaryOp::Or => {
                if left_type == Type::Basic(BasicType::Boolean) && right_type == Type::Basic(BasicType::Boolean) {
                    Ok(Type::Basic(BasicType::Boolean))
                } else {
                    Err(TypeError::TypeMismatch)
                }
            },
        }
    }
    
    /// 统一数值类型
    fn unify_numeric_types(&self, t1: &Type, t2: &Type) -> Type {
        // 实现数值类型统一逻辑
        match (t1, t2) {
            (Type::Basic(BasicType::Integer(i1)), Type::Basic(BasicType::Integer(i2))) => {
                // 选择更大的整数类型
                if i1.size() >= i2.size() {
                    Type::Basic(BasicType::Integer(i1.clone()))
                } else {
                    Type::Basic(BasicType::Integer(i2.clone()))
                }
            },
            (Type::Basic(BasicType::Float(f1)), Type::Basic(BasicType::Float(f2))) => {
                // 选择更大的浮点类型
                if f1.size() >= f2.size() {
                    Type::Basic(BasicType::Float(f1.clone()))
                } else {
                    Type::Basic(BasicType::Float(f2.clone()))
                }
            },
            (Type::Basic(BasicType::Integer(_)), Type::Basic(BasicType::Float(_))) => {
                // 整数和浮点运算返回浮点类型
                t2.clone()
            },
            (Type::Basic(BasicType::Float(_)), Type::Basic(BasicType::Integer(_))) => {
                // 浮点和整数运算返回浮点类型
                t1.clone()
            },
            _ => t1.clone(), // 默认返回第一个类型
        }
    }
}
```

---

**结论**: Rust类型系统通过严格的形式化定义和类型检查，确保了程序的安全性和正确性，体现了现代编程语言类型理论的深度和严谨性。 