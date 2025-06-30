# 可见性与隐私性：模块系统的安全边界理论

## 文档状态

- **版本**: 1.0
- **最后更新**: 2025-01-01
- **维护者**: Rust模块系统工作组
- **审核状态**: 待审核

## 概述

本文档建立Rust模块系统中可见性和隐私性的形式化理论基础，分析隐私边界的安全性保证和封装机制。

## 可见性级别的形式化定义

### 基础可见性分类

```
Visibility ::= Private | Pub(Scope)
Scope ::= Crate | Super | SelfMod | Path(ModulePath)
```

### 可见性层次结构

```
VisibilityHierarchy: Module → PowerSet(Module)
  Private: {self}
  pub(self): {self}
  pub(super): {self, parent(self)}
  pub(crate): {m | same_crate(m, self)}
  pub: Universe
```

### 可见性关系的数学模型

```
Visible: (Item, Module) → Boolean
Visible(item, observer) ⟺ 
  observer ∈ VisibilityScope(visibility(item))
```

## 隐私边界的形式化

### 隐私边界定义

```
PrivacyBoundary ::= ModuleBoundary | CrateBoundary
ModuleBoundary: Module → Boolean
CrateBoundary: Crate → Boolean
```

### 边界穿越规则

**隐私边界定理**：

```
∀ item ∈ Module, ∀ observer ∈ Module:
  crosses_privacy_boundary(item, observer) ⇒
  requires_explicit_visibility(item)
```

## 可见性规则系统

### 规则1：默认隐私性

```
∀ item ∈ Module:
  ¬explicit_visibility(item) ⇒ visibility(item) = Private
```

### 规则2：可见性传播

```
∀ parent, child ∈ Item:
  contains(parent, child) ∧ visibility(parent) < visibility(child)
  ⇒ effective_visibility(child) = visibility(parent)
```

### 规则3：重导出可见性

```
pub use path::Item;
⇒ visibility(Item_in_current_module) = pub
```

## 结构体字段的可见性

### 字段可见性模型

```rust
struct Example {
    pub public_field: i32,       // pub
    pub(crate) crate_field: i32, // pub(crate)
    private_field: i32,          // private
}
```

### 字段访问的形式化

```
FieldAccess: (Struct, Field, Module) → Boolean
FieldAccess(s, f, m) ⟺ 
  Visible(s, m) ∧ Visible(f, m)
```

### 结构体构造的可见性约束

**结构体构造定理**：

```
∀ struct S, ∀ constructor_site:
  can_construct(S, constructor_site) ⇔
  (∀ field ∈ private_fields(S): 
    ¬Visible(field, constructor_site)) ⇒
  ∃ constructor_function(S)
```

## 函数和类型的可见性

### 函数可见性

```rust
mod inner {
    pub fn public_fn() {}
    fn private_fn() {}
    
    pub(super) fn super_visible() {}
    pub(crate) fn crate_visible() {}
}
```

### 类型可见性的复杂性

```rust
mod private_mod {
    pub struct PublicStruct; // 类型公开，模块私有
}

// 类型泄漏问题：
// pub fn expose() -> private_mod::PublicStruct { ... }
```

### 类型泄漏的形式化

**类型泄漏检测定理**：

```
∀ function f, ∀ type T:
  appears_in_signature(T, f) ∧ 
  visibility(f) > visibility(T) ⇒
  type_leak_error(f, T)
```

## 特质实现的可见性

### 特质实现可见性规则

```
ImplVisibility: (Trait, Type, Module) → Boolean
ImplVisibility(trait, type, module) ⟺
  Visible(trait, module) ∧ Visible(type, module)
```

### 孤儿规则与可见性

**孤儿规则**：

```
∀ impl Trait for Type:
  (local_to_crate(Trait) ∨ local_to_crate(Type)) ∨
  covered_by_local_type(Type)
```

### 相干性与可见性

```
∀ impl1, impl2:
  overlaps(impl1, impl2) ∧ 
  same_visibility_scope(impl1, impl2) ⇒
  coherence_conflict(impl1, impl2)
```

## 宏的可见性

### 宏可见性模型

```rust
macro_rules! private_macro { ... }      // 模块私有
#[macro_export] 
macro_rules! public_macro { ... }       // 全局可见

pub(crate) macro_rules! crate_macro { ... } // crate可见
```

### 宏展开中的可见性

**宏展开可见性定理**：

```
∀ macro_call, ∀ expanded_code:
  expand(macro_call) = expanded_code ⇒
  visibility_context(expanded_code) = 
    visibility_context(macro_definition)
```

## 隐私性的安全保证

### 封装不变量

**封装保护定理**：

```
∀ module M, ∀ invariant I:
  maintains(M, I) ∧ 
  (∀ external_access: ¬violates(external_access, I)) ⇒
  global_invariant(I)
```

### 信息隐藏的形式化

```
InformationHiding: (Module, Implementation) → Boolean
InformationHiding(M, impl) ⟺
  ∀ external_observer:
    observable(impl, external_observer) ⊆ 
    public_interface(M)
```

## 可见性与生命周期

### 生命周期参数的可见性

```rust
struct Container<'a> {
    pub data: &'a str,        // 生命周期随结构体可见
}

fn hidden_lifetime() -> impl Iterator<Item = i32> {
    // 隐藏的生命周期参数
}
```

### 生命周期可见性定理

```
∀ lifetime 'a, ∀ type T:
  appears_in(T, 'a) ∧ visibility(T) = pub ⇒
  effective_visibility('a) ≥ pub
```

## 模块重组的可见性影响

### 模块移动的可见性保持

```
ModuleMove: (Module, NewParent) → VisibilityChange
∀ move_operation:
  preserve_external_visibility(move_operation) ⇒
  valid_refactoring(move_operation)
```

### 可见性变更的影响分析

```rust
// 变更前
mod a {
    pub struct S;
}

// 变更后  
pub mod a {
    struct S;  // 可见性降级
}
```

**影响分析定理**：

```
∀ visibility_change:
  reduces_visibility(change) ⇒
  potential_breaking_change(change)
```

## 跨crate可见性

### Crate边界的可见性

```
CrateBoundary: (Item, ExternalCrate) → Boolean
CrateBoundary(item, ext_crate) ⟺
  visibility(item) = pub ∧ 
  reachable_from_root(item)
```

### 依赖关系的可见性传播

```
DependencyVisibility: (CrateA, CrateB) → VisibilityRelation
depends_on(A, B) ⇒ can_access(A, pub_items(B))
```

## 可见性检查算法

### 静态可见性检查

```
Algorithm: VisibilityCheck(item, access_site)
1. path ← compute_access_path(item, access_site)
2. for each segment in path:
3.   if ¬visible_from(segment, access_site):
4.     return VisibilityError
5. return Ok
```

### 可见性图的构建

```
VisibilityGraph: (Crate) → DirectedGraph
nodes ← all_items(crate)
edges ← {(a, b) | can_access(a, b)}
```

## 隐私性验证

### 封装完整性检查

```
EncapsulationIntegrity: Module → Boolean
∀ module M:
  EncapsulationIntegrity(M) ⟺
  (∀ invariant ∈ module_invariants(M):
    ∀ external_path: ¬can_violate(external_path, invariant))
```

### 隐私泄漏检测

```
PrivacyLeakDetection: (PublicAPI) → Set<PrivacyLeak>
leaks ← ∅
for each public_item in PublicAPI:
  for each referenced_type in signature(public_item):
    if visibility(referenced_type) < visibility(public_item):
      leaks.add(PrivacyLeak(public_item, referenced_type))
return leaks
```

## 实际应用案例

### 案例1：API设计的隐私边界

```rust
pub mod api {
    use super::internal::Helper;
    
    pub struct PublicType {
        helper: Helper,  // 私有字段引用内部类型
    }
    
    impl PublicType {
        pub fn new() -> Self { ... }
        pub fn operate(&self) -> i32 { ... }
    }
}

mod internal {
    pub(super) struct Helper { ... }
}
```

### 案例2：库的版本兼容性

```rust
// v1.0
pub mod old_api {
    pub struct Data;
}

// v2.0 - 向后兼容的重构
pub mod new_api {
    pub struct Data;
}

pub use new_api::*;  // 重导出保持兼容性
pub mod old_api {
    pub use crate::new_api::Data;
}
```

## 工具支持

### rustc的可见性检查

- 编译时可见性验证
- 隐私泄漏检测
- 未使用项目检测

### 外部工具

- `cargo-unused-deps`: 未使用依赖检测
- `rust-analyzer`: IDE可见性分析
- 自定义lint: 可见性最佳实践检查

## 相关模块

- [[01_formal_theory.md]] - 模块系统基础理论
- [[02_module_resolution_theory.md]] - 模块解析理论
- [[../02_type_system/README.md]] - 类型系统与可见性
- [[../05_formal_verification/README.md]] - 隐私性验证方法

## 参考文献

1. **The Rust Reference - Visibility and Privacy**
2. **Information Hiding in Programming Languages**
3. **Module Systems and Separate Compilation**
4. **Rust RFC: Privacy and Visibility**

## 维护信息

- **依赖关系**: 模块解析、类型检查器
- **更新频率**: 随模块系统演进更新
- **测试覆盖**: 可见性规则的完整测试套件
- **工具支持**: rustc, rust-analyzer, cargo tools

---

*本文档建立了Rust模块系统隐私性和可见性的完整形式化基础，确保封装边界的安全性。*
