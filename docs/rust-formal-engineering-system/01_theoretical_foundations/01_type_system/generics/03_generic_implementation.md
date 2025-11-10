# Rust泛型实现

## 目录

- [Rust泛型实现](#rust泛型实现)
  - [目录](#目录)
  - [1. 编译器实现](#1-编译器实现)
    - [1.1 类型推导实现](#11-类型推导实现)
    - [1.2 单态化实现](#12-单态化实现)
    - [1.3 Trait约束检查](#13-trait约束检查)
  - [2. 运行时实现](#2-运行时实现)
    - [2.1 泛型函数调用](#21-泛型函数调用)
    - [2.2 泛型数据结构体体体](#22-泛型数据结构体体体)
    - [2.3 关联类型实现](#23-关联类型实现)
  - [3. 性能优化](#3-性能优化)
    - [3.1 编译时优化](#31-编译时优化)
    - [3.2 内存布局优化](#32-内存布局优化)
    - [3.3 代码生成优化](#33-代码生成优化)
  - [4. 错误处理](#4-错误处理)
    - [4.1 类型错误检测](#41-类型错误检测)
    - [4.2 编译时错误报告](#42-编译时错误报告)
  - [5. 调试支持](#5-调试支持)
    - [5.1 泛型调试信息](#51-泛型调试信息)
    - [5.2 运行时类型信息](#52-运行时类型信息)
  - [6. 实际应用示例](#6-实际应用示例)
    - [6.1 泛型算法库](#61-泛型算法库)
    - [6.2 泛型数据结构体体体](#62-泛型数据结构体体体)
  - [7. 总结](#7-总结)

## 1. 编译器实现

### 1.1 类型推导实现

Rust编译器使用Hindley-Milner类型推导算法实现泛型类型推导：

```rust
struct TypeInferrer {
    type_vars: HashMap<String, Type>,
    constraints: Vec<Constraint>,
    fresh_counter: usize,
}

impl TypeInferrer {
    fn fresh_type_var(&mut self) -> Type {
        let name = format!("T{}", self.fresh_counter);
        self.fresh_counter += 1;
        Type::Var(name)
    }

    fn infer_expr(&mut self, expr: &Expr, env: &TypeEnv) -> Result<Type, TypeError> {
        match expr {
            Expr::Var(name) => {
                env.lookup(name)
                    .cloned()
                    .ok_or(TypeError::UnboundVariable(name.clone()))
            }
            Expr::Lambda(param, body) => {
                let param_type = self.fresh_type_var();
                let mut new_env = env.clone();
                new_env.insert(param.clone(), param_type.clone());
                let body_type = self.infer_expr(body, &new_env)?;
                Ok(Type::Function(Box::new(param_type), Box::new(body_type)))
            }
            Expr::Application(func, arg) => {
                let func_type = self.infer_expr(func, env)?;
                let arg_type = self.infer_expr(arg, env)?;
                let result_type = self.fresh_type_var();

                self.constraints.push(Constraint::FunctionCall(
                    func_type,
                    arg_type,
                    result_type.clone(),
                ));

                Ok(result_type)
            }
            Expr::GenericInstantiation(generic, type_args) => {
                let generic_type = self.infer_expr(generic, env)?;
                let concrete_type = self.instantiate_generic(&generic_type, type_args)?;
                Ok(concrete_type)
            }
        }
    }

    fn solve_constraints(&self) -> Result<Substitution, ConstraintError> {
        let mut substitution = Substitution::empty();
        let mut worklist = self.constraints.clone();

        while let Some(constraint) = worklist.pop() {
            match constraint {
                Constraint::Equality(type1, type2) => {
                    let sub = unify(&type1, &type2)?;
                    substitution = substitution.compose(&sub);

                    // 应用替换到剩余约束
                    for constraint in &mut worklist {
                        *constraint = constraint.apply(&sub);
                    }
                }
                Constraint::TraitBound(type_var, trait_name) => {
                    if !self.check_trait_bound(&type_var, &trait_name) {
                        return Err(ConstraintError::TraitNotImplemented);
                    }
                }
            }
        }

        Ok(substitution)
    }
}
```

### 1.2 单态化实现

单态化过程将泛型代码转换为具体类型代码：

```rust
struct Monomorphizer {
    concrete_functions: HashMap<String, ConcreteFunction>,
    type_cache: HashMap<Type, Type>,
}

impl Monomorphizer {
    fn monomorphize_function(
        &mut self,
        generic_fn: &GenericFunction,
        type_args: &[Type],
    ) -> ConcreteFunction {
        let key = self.generate_key(generic_fn, type_args);

        if let Some(cached) = self.concrete_functions.get(&key) {
            return cached.clone();
        }

        let mut substitutions = HashMap::new();
        for (param, arg) in generic_fn.type_params.iter().zip(type_args.iter()) {
            substitutions.insert(param.clone(), arg.clone());
        }

        let concrete_body = self.substitute_types(&generic_fn.body, &substitutions);

        let concrete_fn = ConcreteFunction {
            name: key.clone(),
            body: concrete_body,
            type_args: type_args.to_vec(),
        };

        self.concrete_functions.insert(key, concrete_fn.clone());
        concrete_fn
    }

    fn substitute_types(&self, expr: &Expr, substitutions: &HashMap<String, Type>) -> Expr {
        match expr {
            Expr::TypeVar(name) => {
                if let Some(concrete_type) = substitutions.get(name) {
                    Expr::Type(concrete_type.clone())
                } else {
                    Expr::TypeVar(name.clone())
                }
            }
            Expr::FunctionCall(func, args) => {
                Expr::FunctionCall(
                    Box::new(self.substitute_types(func, substitutions)),
                    args.iter().map(|arg| self.substitute_types(arg, substitutions)).collect(),
                )
            }
            Expr::StructConstruction(name, fields) => {
                Expr::StructConstruction(
                    name.clone(),
                    fields.iter().map(|(field, expr)| {
                        (field.clone(), self.substitute_types(expr, substitutions))
                    }).collect(),
                )
            }
            Expr::MethodCall(obj, method, args) => {
                Expr::MethodCall(
                    Box::new(self.substitute_types(obj, substitutions)),
                    method.clone(),
                    args.iter().map(|arg| self.substitute_types(arg, substitutions)).collect(),
                )
            }
            _ => expr.clone(),
        }
    }

    fn generate_key(&self, generic_fn: &GenericFunction, type_args: &[Type]) -> String {
        let type_names: Vec<String> = type_args.iter().map(|t| t.to_string()).collect();
        format!("{}_{}", generic_fn.name, type_names.join("_"))
    }
}
```

### 1.3 Trait约束检查

```rust
struct TraitChecker {
    trait_implementations: HashMap<(Type, String), TraitImpl>,
}

impl TraitChecker {
    fn check_trait_bound(&self, type_var: &Type, trait_name: &str) -> bool {
        if let Some(impl_) = self.trait_implementations.get(&(type_var.clone(), trait_name.to_string())) {
            self.verify_trait_impl(impl_)
        } else {
            false
        }
    }

    fn verify_trait_impl(&self, impl_: &TraitImpl) -> bool {
        // 检查所有必需的方法实现
        for method in &impl_.trait_methods {
            if !self.check_method_implementation(impl_, method) {
                return false;
            }
        }
        true
    }

    fn check_method_implementation(&self, impl_: &TraitImpl, method: &TraitMethod) -> bool {
        // 检查方法签名匹配
        if let Some(impl_method) = impl_.methods.get(&method.name) {
            self.signatures_compatible(&method.signature, &impl_method.signature)
        } else {
            false
        }
    }

    fn signatures_compatible(&self, trait_sig: &MethodSignature, impl_sig: &MethodSignature) -> bool {
        // 检查参数类型和返回类型兼容性
        trait_sig.parameters.len() == impl_sig.parameters.len() &&
        trait_sig.parameters.iter().zip(&impl_sig.parameters).all(|(t, i)| {
            self.types_compatible(t, i)
        }) &&
        self.types_compatible(&trait_sig.return_type, &impl_sig.return_type)
    }
}
```

## 2. 运行时实现

### 2.1 泛型函数调用

```rust
// 编译时生成的泛型函数调用代码
fn call_generic_function<T: Trait>(arg: T) -> T {
    // 编译器生成的具体类型代码
    let result = arg.trait_method();
    result
}

// 单态化后的具体实现
fn call_generic_function_i32(arg: i32) -> i32 {
    // 针对i32类型优化的代码
    arg + 1
}

fn call_generic_function_string(arg: String) -> String {
    // 针对String类型优化的代码
    arg + " processed"
}
```

### 2.2 泛型数据结构体体体

```rust
// 泛型向量实现
struct Vec<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
    _phantom: std::marker::PhantomData<T>,
}

impl<T> Vec<T> {
    fn new() -> Self {
        Vec {
            ptr: std::ptr::null_mut(),
            len: 0,
            capacity: 0,
            _phantom: std::marker::PhantomData,
        }
    }

    fn push(&mut self, item: T) {
        if self.len == self.capacity {
            self.grow();
        }

        unsafe {
            std::ptr::write(self.ptr.add(self.len), item);
        }
        self.len += 1;
    }

    fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe {
                Some(std::ptr::read(self.ptr.add(self.len)))
            }
        }
    }

    fn grow(&mut self) {
        let new_capacity = if self.capacity == 0 { 1 } else { self.capacity * 2 };
        let new_ptr = unsafe {
            std::alloc::alloc(
                std::alloc::Layout::array::<T>(new_capacity).unwrap()
            ) as *mut T
        };

        if !self.ptr.is_null() {
            unsafe {
                std::ptr::copy_nonoverlapping(self.ptr, new_ptr, self.len);
                std::alloc::dealloc(
                    self.ptr as *mut u8,
                    std::alloc::Layout::array::<T>(self.capacity).unwrap()
                );
            }
        }

        self.ptr = new_ptr;
        self.capacity = new_capacity;
    }
}

impl<T> Drop for Vec<T> {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe {
                // 调用所有元素的析构函数
                for i in 0..self.len {
                    std::ptr::drop_in_place(self.ptr.add(i));
                }
                std::alloc::dealloc(
                    self.ptr as *mut u8,
                    std::alloc::Layout::array::<T>(self.capacity).unwrap()
                );
            }
        }
    }
}
```

### 2.3 关联类型实现

```rust
trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
}

struct VecIterator<T> {
    vec: Vec<T>,
    index: usize,
}

impl<T> Iterator for VecIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.index < self.vec.len() {
            let item = unsafe {
                std::ptr::read(self.vec.as_ptr().add(self.index))
            };
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

// 编译器生成的关联类型访问代码
fn get_iterator_item<I: Iterator>(iter: &mut I) -> Option<I::Item> {
    iter.next()
}
```

## 3. 性能优化

### 3.1 编译时优化

```rust
// 内联优化
#[inline(always)]
fn generic_add<T: Add<Output = T> + Copy>(a: T, b: T) -> T {
    a + b
}

// 编译时单态化优化
fn optimized_add_i32(a: i32, b: i32) -> i32 {
    // 编译器生成的优化代码
    a + b
}

fn optimized_add_f64(a: f64, b: f64) -> f64 {
    // 编译器生成的优化代码
    a + b
}
```

### 3.2 内存布局优化

```rust
// 零大小类型优化
struct PhantomData<T> {
    _phantom: std::marker::PhantomData<T>,
}

// 编译器优化后的内存布局
struct OptimizedVec<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
    // PhantomData<T> 不占用内存空间
}

// 对齐优化
#[repr(align(8))]
struct AlignedStruct<T> {
    data: T,
    padding: [u8; 8],
}
```

### 3.3 代码生成优化

```rust
// 编译器生成的优化代码
fn optimized_generic_algorithm<T: Ord + Copy>(slice: &mut [T]) {
    // 针对具体类型优化的排序算法
    if std::mem::size_of::<T>() <= 8 {
        // 小类型使用快速排序
        quick_sort_optimized(slice);
    } else {
        // 大类型使用归并排序
        merge_sort_optimized(slice);
    }
}

fn quick_sort_optimized<T: Ord + Copy>(slice: &mut [T]) {
    // 针对小类型优化的快速排序
    if slice.len() <= 1 {
        return;
    }

    let pivot = slice[0];
    let mut left = 0;
    let mut right = slice.len() - 1;

    while left < right {
        while left < right && slice[right] >= pivot {
            right -= 1;
        }
        slice[left] = slice[right];

        while left < right && slice[left] <= pivot {
            left += 1;
        }
        slice[right] = slice[left];
    }

    slice[left] = pivot;
    quick_sort_optimized(&mut slice[..left]);
    quick_sort_optimized(&mut slice[left + 1..]);
}
```

## 4. 错误处理

### 4.1 类型错误检测

```rust
enum GenericError {
    TypeMismatch(Type, Type),
    TraitNotImplemented(Type, String),
    LifetimeMismatch(Lifetime, Lifetime),
    ConstraintViolation(String),
}

struct GenericErrorChecker {
    errors: Vec<GenericError>,
}

impl GenericErrorChecker {
    fn check_generic_function(&mut self, func: &GenericFunction) -> Result<(), Vec<GenericError>> {
        // 检查类型参数约束
        for param in &func.type_params {
            for constraint in &param.constraints {
                if !self.check_constraint(param, constraint) {
                    self.errors.push(GenericError::TraitNotImplemented(
                        param.type_var.clone(),
                        constraint.trait_name.clone(),
                    ));
                }
            }
        }

        // 检查函数体类型一致性
        self.check_function_body(&func.body, &func.signature)?;

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors.clone())
        }
    }

    fn check_constraint(&self, param: &TypeParam, constraint: &TraitConstraint) -> bool {
        // 检查类型参数是否满足Trait约束
        self.trait_implementations.contains_key(&(param.type_var.clone(), constraint.trait_name.clone()))
    }
}
```

### 4.2 编译时错误报告

```rust
struct ErrorReporter {
    errors: Vec<CompileError>,
}

impl ErrorReporter {
    fn report_generic_error(&mut self, error: &GenericError, span: Span) {
        match error {
            GenericError::TypeMismatch(expected, found) => {
                self.errors.push(CompileError::new(
                    span,
                    format!("expected type `{}`, found type `{}`", expected, found),
                    ErrorKind::TypeMismatch,
                ));
            }
            GenericError::TraitNotImplemented(type_var, trait_name) => {
                self.errors.push(CompileError::new(
                    span,
                    format!("the trait `{}` is not implemented for `{}`", trait_name, type_var),
                    ErrorKind::TraitNotImplemented,
                ));
            }
            GenericError::LifetimeMismatch(expected, found) => {
                self.errors.push(CompileError::new(
                    span,
                    format!("lifetime mismatch: expected `{}`, found `{}`", expected, found),
                    ErrorKind::LifetimeMismatch,
                ));
            }
        }
    }
}
```

## 5. 调试支持

### 5.1 泛型调试信息

```rust
struct GenericDebugInfo {
    type_params: Vec<TypeParamInfo>,
    constraints: Vec<ConstraintInfo>,
    instantiations: Vec<InstantiationInfo>,
}

struct TypeParamInfo {
    name: String,
    bounds: Vec<String>,
    span: Span,
}

struct ConstraintInfo {
    type_var: String,
    trait_name: String,
    span: Span,
}

struct InstantiationInfo {
    generic_name: String,
    type_args: Vec<Type>,
    concrete_name: String,
    span: Span,
}

impl GenericDebugInfo {
    fn generate_debug_info(&self) -> String {
        let mut info = String::new();

        info.push_str("Generic Function Debug Info:\n");
        info.push_str("Type Parameters:\n");
        for param in &self.type_params {
            info.push_str(&format!("  {}: {}\n", param.name, param.bounds.join(" + ")));
        }

        info.push_str("Constraints:\n");
        for constraint in &self.constraints {
            info.push_str(&format!("  {}: {}\n", constraint.type_var, constraint.trait_name));
        }

        info.push_str("Instantiations:\n");
        for instantiation in &self.instantiations {
            info.push_str(&format!("  {}<{}> -> {}\n",
                instantiation.generic_name,
                instantiation.type_args.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(", "),
                instantiation.concrete_name
            ));
        }

        info
    }
}
```

### 5.2 运行时类型信息

```rust
// 编译时生成的类型信息
struct TypeInfo {
    name: &'static str,
    size: usize,
    align: usize,
    drop_fn: Option<fn(*mut u8)>,
}

impl<T> TypeInfo {
    const fn new() -> Self {
        TypeInfo {
            name: std::any::type_name::<T>(),
            size: std::mem::size_of::<T>(),
            align: std::mem::align_of::<T>(),
            drop_fn: if std::mem::needs_drop::<T>() {
                Some(Self::drop_impl::<T>)
            } else {
                None
            },
        }
    }

    fn drop_impl<T>(ptr: *mut u8) {
        unsafe {
            std::ptr::drop_in_place(ptr as *mut T);
        }
    }
}

// 泛型函数的类型信息
struct GenericFunctionInfo {
    name: &'static str,
    type_params: Vec<TypeParamInfo>,
    instantiations: HashMap<Vec<Type>, ConcreteFunctionInfo>,
}

struct ConcreteFunctionInfo {
    name: String,
    type_info: TypeInfo,
    code_ptr: *const u8,
}
```

## 6. 实际应用示例

### 6.1 泛型算法库

```rust
// 泛型排序算法
pub trait Sortable {
    fn sort(&mut self);
}

impl<T: Ord> Sortable for Vec<T> {
    fn sort(&mut self) {
        self.sort_unstable();
    }
}

// 泛型查找算法
pub fn binary_search<T: Ord>(slice: &[T], target: &T) -> Result<usize, usize> {
    let mut left = 0;
    let mut right = slice.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match slice[mid].cmp(target) {
            std::cmp::Ordering::Equal => return Ok(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }

    Err(left)
}

// 泛型容器
pub struct Container<T> {
    data: Vec<T>,
}

impl<T> Container<T> {
    pub fn new() -> Self {
        Container { data: Vec::new() }
    }

    pub fn push(&mut self, item: T) {
        self.data.push(item);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl<T: Clone> Container<T> {
    pub fn clone_all(&self) -> Container<T> {
        Container {
            data: self.data.clone(),
        }
    }
}

impl<T: Ord> Container<T> {
    pub fn sort(&mut self) {
        self.data.sort();
    }

    pub fn find(&self, target: &T) -> Option<usize> {
        self.data.binary_search(target).ok()
    }
}
```

### 6.2 泛型数据结构体体体

```rust
// 泛型链表
pub struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
    len: usize,
}

struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        LinkedList { head: None, len: 0 }
    }

    pub fn push_front(&mut self, data: T) {
        let new_node = Box::new(Node {
            data,
            next: self.head.take(),
        });
        self.head = Some(new_node);
        self.len += 1;
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            self.len -= 1;
            node.data
        })
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }
}

// 泛型树
pub struct BinaryTree<T> {
    root: Option<Box<TreeNode<T>>>,
}

struct TreeNode<T> {
    data: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

impl<T: Ord> BinaryTree<T> {
    pub fn new() -> Self {
        BinaryTree { root: None }
    }

    pub fn insert(&mut self, data: T) {
        self.root = Some(Box::new(self.insert_recursive(self.root.take(), data)));
    }

    fn insert_recursive(&self, node: Option<Box<TreeNode<T>>>, data: T) -> TreeNode<T> {
        match node {
            None => TreeNode {
                data,
                left: None,
                right: None,
            },
            Some(mut node) => {
                if data < node.data {
                    node.left = Some(Box::new(self.insert_recursive(node.left.take(), data)));
                } else {
                    node.right = Some(Box::new(self.insert_recursive(node.right.take(), data)));
                }
                *node
            }
        }
    }

    pub fn contains(&self, data: &T) -> bool {
        self.contains_recursive(&self.root, data)
    }

    fn contains_recursive(&self, node: &Option<Box<TreeNode<T>>>, data: &T) -> bool {
        match node {
            None => false,
            Some(node) => {
                if data == &node.data {
                    true
                } else if data < &node.data {
                    self.contains_recursive(&node.left, data)
                } else {
                    self.contains_recursive(&node.right, data)
                }
            }
        }
    }
}
```

## 7. 总结

Rust泛型实现通过编译时类型推导、单态化和运行时优化提供了高效的泛型编程支持。主要特点包括：

1. **编译时优化**: 单态化消除运行时开销
2. **类型安全**: 编译时类型检查保证正确性
3. **性能优化**: 针对具体类型进行优化
4. **调试支持**: 完整的调试信息和错误报告
5. **内存安全**: 自动内存管理和资源清理

泛型实现的核心优势是提供了零成本抽象，同时保持了类型安全和性能优化。

---

**文档版本**: 1.0.0
**最后更新**: 2025-01-27
**维护者**: Rust语言形式化理论项目组
