# Type Parameters System

## 1. Type Parameter Fundamentals

### 1.1 Type Parameter Declaration

#### Definition 1.1: Type Parameter Declaration

A type parameter declaration introduces a type variable in a generic context.

**Formal Definition:**

```
<T₁, T₂, ..., Tₙ> where:
- Tᵢ are type parameter identifiers
- Each Tᵢ ranges over the set of all types
- Tᵢ are distinct (no duplicates)
```

#### Example 1.1: Basic Type Parameters

```rust
struct Container<T> {
    value: T,
}

fn identity<T>(x: T) -> T {
    x
}

enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

### 1.2 Type Parameter Scope

#### Definition 1.2: Type Parameter Scope

The scope of a type parameter is the region where it can be referenced.

**Formal Definition:**

```
scope(T) = { declaration_site, ..., end_of_generic_item }
where:
- T is a type parameter
- scope(T) includes all references to T
- scope(T) ends at the end of the generic item
```

#### Example 1.2: Scope Examples

```rust
struct Outer<T> {
    // T is in scope here
    inner: Inner<T>,
}

struct Inner<U> {
    // U is in scope here, T is not
    value: U,
}

impl<T> Outer<T> {
    // T is in scope here
    fn new(value: T) -> Self {
        Outer { inner: Inner { value } }
    }
}
```

## 2. Type Parameter Constraints

### 2.1 Trait Bounds

#### Definition 2.1: Trait Bound

A trait bound constrains a type parameter to implement specific traits.

**Formal Definition:**

```
T : Trait₁ + Trait₂ + ... + Traitₙ where:
- T must implement all Traitᵢ
- All methods from all traits are available on T
- T satisfies the trait constraint system
```

#### Example 2.1: Single Trait Bound

```rust
fn print<T: Display>(item: T) {
    println!("{}", item);
}

struct SortedVec<T: Ord> {
    data: Vec<T>,
}

impl<T: Ord> SortedVec<T> {
    fn insert(&mut self, item: T) {
        // Can use <, >, ==, etc. because T: Ord
        let pos = self.data.binary_search(&item).unwrap_or_else(|e| e);
        self.data.insert(pos, item);
    }
}
```

### 2.2 Multiple Trait Bounds

#### Definition 2.2: Multiple Trait Bounds

Multiple trait bounds require a type parameter to implement several traits.

**Formal Definition:**

```
T : Trait₁ + Trait₂ + ... + Traitₙ where:
- T must implement all Traitᵢ simultaneously
- All methods from all traits are available
- Trait bounds are conjunctive (AND logic)
```

#### Example 2.2: Multiple Bounds

```rust
fn process<T: Clone + Display + Debug>(item: T) -> T {
    println!("Processing: {:?}", item);
    println!("Display: {}", item);
    item.clone()
}

struct DataProcessor<T> 
where
    T: Clone + Send + Sync + 'static
{
    processor: Box<dyn Fn(T) -> T + Send + Sync>,
}
```

### 2.3 Where Clauses

#### Definition 2.3: Where Clause

A where clause provides additional constraints on type parameters.

**Formal Definition:**

```
where
    T₁: Trait₁,
    T₂: Trait₂,
    T₁::AssocType: Trait₃,
    T₂::AssocType = U
where:
- Each constraint is specified separately
- Associated type constraints are supported
- Constraints can reference multiple type parameters
```

#### Example 2.3: Complex Where Clauses

```rust
fn complex_function<T, U, V>(t: T, u: U) -> V
where
    T: Iterator<Item = U>,
    U: Clone + Display,
    V: FromIterator<U>,
    T::Item: Debug
{
    t.map(|item| {
        println!("Processing: {:?}", item);
        item
    }).collect()
}
```

## 3. Type Parameter Variance

### 3.1 Variance Definitions

#### Definition 3.1: Covariance

A type parameter is covariant if it preserves the subtyping relationship.

**Formal Definition:**

```
If T₁ <: T₂, then G<T₁> <: G<T₂>
where G is covariant in its type parameter
```

#### Definition 3.2: Contravariance

A type parameter is contravariant if it reverses the subtyping relationship.

**Formal Definition:**

```
If T₁ <: T₂, then G<T₂> <: G<T₁>
where G is contravariant in its type parameter
```

#### Definition 3.3: Invariance

A type parameter is invariant if it neither preserves nor reverses subtyping.

**Formal Definition:**

```
G<T₁> and G<T₂> are unrelated regardless of T₁ <: T₂
where G is invariant in its type parameter
```

### 3.2 Variance Rules

#### Theorem 3.1: Variance Rules

Rust's variance rules are determined by how the type parameter is used.

**Rules:**

```
1. Output positions (return types) are covariant
2. Input positions (parameter types) are contravariant
3. Both input and output positions make the type invariant
4. PhantomData<T> is covariant in T
```

#### Example 3.1: Variance Examples

```rust
// Covariant: T only appears in output position
struct Covariant<T> {
    data: PhantomData<T>,
}

// Contravariant: T only appears in input position
struct Contravariant<T> {
    func: fn(T),
}

// Invariant: T appears in both input and output positions
struct Invariant<T> {
    data: T,
    func: fn(T) -> T,
}
```

## 4. Type Parameter Inference

### 4.1 Type Inference Algorithm

#### Definition 4.1: Type Inference

Type inference automatically determines concrete types for type parameters.

**Formal Definition:**

```
Given: f<T>(x: T) -> R
When: f(42) is called
Then: T is inferred as i32
```

#### Example 4.1: Basic Inference

```rust
fn identity<T>(x: T) -> T {
    x
}

// Type inference examples:
let a = identity(42);        // T = i32
let b = identity("hello");   // T = &str
let c = identity(vec![1,2]); // T = Vec<i32>
```

### 4.2 Constraint Collection

#### Definition 4.2: Constraint Collection

The type checker collects constraints during type inference.

**Algorithm:**

```
1. For each expression, collect type constraints
2. Unify types where possible
3. Check trait bounds are satisfied
4. Report errors for unsatisfiable constraints
```

#### Example 4.2: Constraint Collection

```rust
fn process<T: Display>(x: T) -> String {
    x.to_string()
}

// When called with process(42):
// 1. T must be i32 (from argument)
// 2. T must implement Display (from bound)
// 3. Check: i32 implements Display ✓
// 4. Result: T = i32
```

## 5. Type Parameter Bounds

### 5.1 Lifetime Bounds

#### Definition 5.1: Lifetime Bound

A lifetime bound constrains the lifetime of a type parameter.

**Formal Definition:**

```
T: 'a where:
- T must not contain any references with lifetime shorter than 'a
- T is valid for at least lifetime 'a
```

#### Example 5.1: Lifetime Bounds

```rust
struct Container<T: 'static> {
    data: T,
}

fn process_static<T: 'static>(item: T) {
    // T can be stored in static variables
    static mut STORAGE: Option<T> = None;
    unsafe {
        STORAGE = Some(item);
    }
}
```

### 5.2 Sized Bounds

#### Definition 5.2: Sized Bound

A sized bound requires a type parameter to have a known size at compile time.

**Formal Definition:**

```
T: Sized where:
- T has a known size at compile time
- T can be moved by value
- T implements the Sized trait
```

#### Example 5.2: Sized Bounds

```rust
fn process_sized<T: Sized>(item: T) {
    // T has known size, can be moved
    let moved = item;
}

// Without Sized bound:
fn process_unsized<T: ?Sized>(item: &T) {
    // T might not have known size
    // Must use reference
}
```

## 6. Type Parameter Specialization

### 6.1 Specialization Rules

#### Definition 6.1: Specialization

Specialization allows more specific implementations to override more general ones.

**Formal Definition:**

```
impl<T> Trait for Container<T> { /* general */ }
impl Trait for Container<i32> { /* specific */ }

When Container<i32> is used, the specific impl is chosen
```

#### Example 6.1: Basic Specialization

```rust
trait Processor {
    fn process(&self) -> String;
}

impl<T: Display> Processor for T {
    fn process(&self) -> String {
        format!("{}", self)
    }
}

impl Processor for i32 {
    fn process(&self) -> String {
        format!("Integer: {}", self)
    }
}

// i32 uses the specific implementation
let x = 42;
println!("{}", x.process()); // "Integer: 42"
```

### 6.2 Specialization Constraints

#### Definition 6.2: Specialization Constraints

Specialization must follow specific rules to maintain coherence.

**Rules:**

```
1. More specific impls must be more specific in all type parameters
2. Specialization must be transitive
3. No overlapping impls without specialization
4. Specialization must preserve trait bounds
```

## 7. Type Parameter Patterns

### 7.1 Phantom Type Parameters

#### Definition 7.1: Phantom Type Parameter

A phantom type parameter is used for type-level programming without runtime representation.

**Formal Definition:**

```
struct Phantom<T> {
    _phantom: PhantomData<T>,
}
where T is used only for type-level information
```

#### Example 7.1: Type-Safe Units

```rust
use std::marker::PhantomData;

struct Meter;
struct Second;

struct Distance<T> {
    value: f64,
    _phantom: PhantomData<T>,
}

impl Distance<Meter> {
    fn new_meters(value: f64) -> Self {
        Distance {
            value,
            _phantom: PhantomData,
        }
    }
    
    fn to_meters(&self) -> f64 {
        self.value
    }
}

impl Distance<Second> {
    fn new_seconds(value: f64) -> Self {
        Distance {
            value,
            _phantom: PhantomData,
        }
    }
}

// Type safety prevents mixing units
let distance = Distance::<Meter>::new_meters(5.0);
// let time = Distance::<Second>::new_seconds(10.0);
// let sum = distance + time; // Compile error!
```

### 7.2 Type-Level Functions

#### Definition 7.2: Type-Level Function

A type-level function maps types to types using associated types.

**Formal Definition:**

```
trait TypeFunction {
    type Output;
}
where Output is computed from Self
```

#### Example 7.2: Option Type Function

```rust
trait OptionType {
    type Output;
}

impl<T> OptionType for T {
    type Output = Option<T>;
}

fn wrap_in_option<T: OptionType>(value: T) -> T::Output {
    Some(value)
}

// Usage:
let x = wrap_in_option(42); // x: Option<i32>
```

## 8. Implementation Details

### 8.1 Type Parameter Resolution

```rust
struct TypeParameterResolver {
    constraints: Vec<TypeConstraint>,
    substitutions: HashMap<TypeParam, Type>,
}

impl TypeParameterResolver {
    fn resolve<T>(&mut self, context: &TypeContext) -> Result<Type, Error> {
        // Collect all constraints for T
        let constraints = self.collect_constraints::<T>(context);
        
        // Try to unify types
        for constraint in constraints {
            self.unify_constraint(constraint)?;
        }
        
        // Apply substitutions
        self.apply_substitutions()
    }
    
    fn unify_constraint(&mut self, constraint: TypeConstraint) -> Result<(), Error> {
        match constraint {
            TypeConstraint::TraitBound(bound) => {
                self.check_trait_bound(bound)?;
            }
            TypeConstraint::AssociatedType(assoc) => {
                self.resolve_associated_type(assoc)?;
            }
            TypeConstraint::LifetimeBound(bound) => {
                self.check_lifetime_bound(bound)?;
            }
        }
        Ok(())
    }
}
```

### 8.2 Constraint Checking

```rust
trait ConstraintChecker {
    fn check_trait_bound<T, B>(&self, bound: B) -> Result<(), Error>
    where
        T: ?Sized,
        B: TraitBound;
        
    fn check_lifetime_bound<T>(&self, lifetime: Lifetime) -> Result<(), Error>
    where
        T: ?Sized;
        
    fn check_sized_bound<T>(&self) -> Result<(), Error>
    where
        T: ?Sized;
}

impl ConstraintChecker for TypeChecker {
    fn check_trait_bound<T, B>(&self, bound: B) -> Result<(), Error>
    where
        T: ?Sized,
        B: TraitBound
    {
        // Check if T implements all methods in B
        let required_methods = bound.required_methods();
        
        for method in required_methods {
            if !T::implements_method(method) {
                return Err(Error::TraitBoundNotSatisfied {
                    type_name: std::any::type_name::<T>(),
                    trait_name: bound.name(),
                    method_name: method.name(),
                });
            }
        }
        
        Ok(())
    }
}
```

## 9. Formal Proofs

### 9.1 Type Parameter Soundness

#### Theorem 9.1: Type Parameter Soundness

Type parameters preserve type safety under all valid substitutions.

**Proof:**

```
1. Let G<T> be a generic type with type parameter T
2. Let σ be a valid type substitution
3. Assume T satisfies all constraints of G
4. By constraint preservation: σ(T) satisfies constraints
5. By substitution soundness: G<σ(T)> is type safe
6. Therefore, type parameters preserve type safety
```

### 9.2 Constraint Satisfaction Completeness

#### Theorem 9.2: Constraint Satisfaction Completeness

The constraint system ensures all necessary type information is available.

**Proof:**

```
1. Let f<T: Trait>(x: T) be a generic function
2. T: Trait ensures all Trait methods are available
3. Type checker can verify all method calls on T
4. No runtime errors can occur due to missing methods
5. Therefore, constraint satisfaction is complete
```

## 10. Summary

The type parameter system provides:

1. **Flexibility**: Type parameters enable generic programming
2. **Type Safety**: Constraints ensure type safety at compile time
3. **Expressiveness**: Complex constraint systems support advanced patterns
4. **Performance**: Zero-cost abstractions with no runtime overhead
5. **Correctness**: Formal proofs ensure system soundness

This system enables Rust to provide powerful generic programming capabilities while maintaining compile-time guarantees and zero runtime overhead.

---

**References:**

- [Rust Reference - Type Parameters](https://doc.rust-lang.org/reference/types/parameters.html)
- [Rust Book - Generic Types](https://doc.rust-lang.org/book/ch10-01-syntax.html)
- [Rustonomicon - Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html)
