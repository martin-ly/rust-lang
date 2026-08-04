# Generic Programming Patterns

## 1. Generic Pattern Fundamentals

### 1.1 Generic Pattern Definition

#### Definition 1.1: Generic Pattern

A generic pattern is a reusable design that leverages type parameters to provide type-safe, flexible solutions.

**Formal Definition:**

```
Pattern<T₁, T₂, ..., Tₙ> where:
- Tᵢ are type parameters
- Pattern provides functionality for all valid Tᵢ
- Pattern maintains type safety across all instantiations
```

#### Example 1.1: Basic Generic Pattern

```rust
struct Container<T> {
    data: Vec<T>,
}

impl<T> Container<T> {
    fn new() -> Self {
        Container { data: Vec::new() }
    }
    
    fn push(&mut self, item: T) {
        self.data.push(item);
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
}

// This pattern works for any type T
let int_container = Container::<i32>::new();
let string_container = Container::<String>::new();
let bool_container = Container::<bool>::new();
```

### 1.2 Pattern Classification

#### Definition 1.2: Pattern Classification

Generic patterns can be classified by their purpose and structure.

**Classifications:**

```
1. Container Patterns: Store and manage data of any type
2. Function Patterns: Operate on data of any type
3. Trait Patterns: Define behavior for any type
4. Builder Patterns: Construct objects of any type
5. Iterator Patterns: Process sequences of any type
```

## 2. Container Patterns

### 2.1 Generic Container Pattern

#### Definition 2.1: Generic Container

A container that can hold values of any type while maintaining type safety.

**Formal Definition:**

```
Container<T> where:
- T is the element type
- Container<T> provides storage for T
- Container<T> maintains ownership semantics
- Container<T> is type-safe
```

#### Example 2.1: Generic Container Implementation

```rust
struct GenericContainer<T> {
    data: Vec<T>,
    capacity: usize,
}

impl<T> GenericContainer<T> {
    fn new() -> Self {
        GenericContainer {
            data: Vec::new(),
            capacity: 0,
        }
    }
    
    fn with_capacity(capacity: usize) -> Self {
        GenericContainer {
            data: Vec::with_capacity(capacity),
            capacity,
        }
    }
    
    fn push(&mut self, item: T) {
        self.data.push(item);
    }
    
    fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
    
    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    
    fn clear(&mut self) {
        self.data.clear();
    }
}

// Usage with different types
let mut int_container = GenericContainer::<i32>::new();
int_container.push(1);
int_container.push(2);
int_container.push(3);

let mut string_container = GenericContainer::<String>::new();
string_container.push("hello".to_string());
string_container.push("world".to_string());
```

### 2.2 Constrained Container Pattern

#### Definition 2.2: Constrained Container

A container that requires its elements to satisfy certain constraints.

**Formal Definition:**

```
Container<T: Constraint> where:
- T must satisfy Constraint
- Container provides functionality based on Constraint
- Type safety is enforced at compile time
```

#### Example 2.2: Constrained Container

```rust
struct SortedContainer<T: Ord> {
    data: Vec<T>,
}

impl<T: Ord> SortedContainer<T> {
    fn new() -> Self {
        SortedContainer { data: Vec::new() }
    }
    
    fn insert(&mut self, item: T) {
        let pos = self.data.binary_search(&item).unwrap_or_else(|e| e);
        self.data.insert(pos, item);
    }
    
    fn contains(&self, item: &T) -> bool {
        self.data.binary_search(item).is_ok()
    }
    
    fn remove(&mut self, item: &T) -> bool {
        if let Ok(pos) = self.data.binary_search(item) {
            self.data.remove(pos);
            true
        } else {
            false
        }
    }
}

// Usage
let mut sorted = SortedContainer::<i32>::new();
sorted.insert(3);
sorted.insert(1);
sorted.insert(2);
// Data is automatically kept sorted
```

### 2.3 Multi-Type Container Pattern

#### Definition 2.3: Multi-Type Container

A container that can hold multiple types using type parameters.

**Formal Definition:**

```
Container<T₁, T₂, ..., Tₙ> where:
- Tᵢ are different type parameters
- Container can store values of each type
- Type safety is maintained for each type
```

#### Example 2.3: Multi-Type Container

```rust
struct PairContainer<T, U> {
    first: T,
    second: U,
}

impl<T, U> PairContainer<T, U> {
    fn new(first: T, second: U) -> Self {
        PairContainer { first, second }
    }
    
    fn get_first(&self) -> &T {
        &self.first
    }
    
    fn get_second(&self) -> &U {
        &self.second
    }
    
    fn set_first(&mut self, first: T) {
        self.first = first;
    }
    
    fn set_second(&mut self, second: U) {
        self.second = second;
    }
}

// Usage
let pair = PairContainer::new(42, "hello".to_string());
println!("First: {}, Second: {}", pair.get_first(), pair.get_second());
```

## 3. Function Patterns

### 3.1 Generic Function Pattern

#### Definition 3.1: Generic Function

A function that can operate on multiple types while maintaining type safety.

**Formal Definition:**

```
fn function<T₁, T₂, ..., Tₙ>(args) -> ReturnType where:
- Tᵢ are type parameters
- Function works for all valid Tᵢ
- Type safety is preserved
```

#### Example 3.1: Generic Function Patterns

```rust
// Identity function
fn identity<T>(x: T) -> T {
    x
}

// Swap function
fn swap<T>(a: T, b: T) -> (T, T) {
    (b, a)
}

// Maximum function
fn max<T: Ord>(a: T, b: T) -> T {
    if a > b { a } else { b }
}

// Minimum function
fn min<T: Ord>(a: T, b: T) -> T {
    if a < b { a } else { b }
}

// Usage
let x = identity(42);
let y = identity("hello");
let (a, b) = swap(1, 2);
let max_val = max(10, 20);
let min_val = min(10, 20);
```

### 3.2 Constrained Function Pattern

#### Definition 3.2: Constrained Function

A generic function that requires its type parameters to satisfy constraints.

**Formal Definition:**

```
fn function<T: Constraint>(args) -> ReturnType where:
- T must satisfy Constraint
- Function can use functionality from Constraint
- Type safety is enforced
```

#### Example 3.2: Constrained Functions

```rust
// Display function
fn print<T: Display>(item: T) {
    println!("{}", item);
}

// Clone and display function
fn print_and_clone<T: Clone + Display>(item: T) -> T {
    println!("{}", item);
    item.clone()
}

// Numeric operations
fn add<T: Add<Output = T> + Copy>(a: T, b: T) -> T {
    a + b
}

fn multiply<T: Mul<Output = T> + Copy>(a: T, b: T) -> T {
    a * b
}

// Iterator processing
fn process_items<T, I>(items: I) -> Vec<T>
where
    I: Iterator<Item = T>,
    T: Clone + Display
{
    items.map(|item| {
        println!("Processing: {}", item);
        item
    }).collect()
}

// Usage
print(42);
print("hello");
let cloned = print_and_clone("world");
let sum = add(10, 20);
let product = multiply(5, 6);
```

### 3.3 Higher-Order Function Pattern

#### Definition 3.3: Higher-Order Function

A function that takes or returns other functions.

**Formal Definition:**

```
fn higher_order<F, T, U>(f: F, data: T) -> U where:
- F: Fn(T) -> U
- F is a function type
- Function composition is type-safe
```

#### Example 3.3: Higher-Order Functions

```rust
// Map function
fn map<T, U, F>(items: Vec<T>, f: F) -> Vec<U>
where
    F: Fn(T) -> U
{
    items.into_iter().map(f).collect()
}

// Filter function
fn filter<T, F>(items: Vec<T>, predicate: F) -> Vec<T>
where
    F: Fn(&T) -> bool
{
    items.into_iter().filter(predicate).collect()
}

// Reduce function
fn reduce<T, F>(items: Vec<T>, initial: T, f: F) -> T
where
    F: Fn(T, T) -> T
{
    items.into_iter().fold(initial, f)
}

// Compose function
fn compose<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> C
where
    F: Fn(B) -> C,
    G: Fn(A) -> B
{
    move |x| f(g(x))
}

// Usage
let numbers = vec![1, 2, 3, 4, 5];
let doubled = map(numbers, |x| x * 2);
let evens = filter(doubled, |x| x % 2 == 0);
let sum = reduce(evens, 0, |acc, x| acc + x);

let add_one = |x: i32| x + 1;
let multiply_by_two = |x: i32| x * 2;
let composed = compose(multiply_by_two, add_one);
let result = composed(5); // (5 + 1) * 2 = 12
```

## 4. Trait Patterns

### 4.1 Generic Trait Pattern

#### Definition 4.1: Generic Trait

A trait that defines behavior for generic types.

**Formal Definition:**

```
trait GenericTrait<T₁, T₂, ..., Tₙ> {
    type AssocType;
    fn method(&self, args) -> ReturnType;
}
where:
- Tᵢ are type parameters
- Trait provides functionality for all valid Tᵢ
```

#### Example 4.1: Generic Traits

```rust
trait Processor<T> {
    type Output;
    
    fn process(&self, input: T) -> Self::Output;
    fn can_process(&self, input: &T) -> bool;
}

struct StringProcessor;

impl Processor<String> for StringProcessor {
    type Output = usize;
    
    fn process(&self, input: String) -> usize {
        input.len()
    }
    
    fn can_process(&self, input: &String) -> bool {
        !input.is_empty()
    }
}

struct NumberProcessor;

impl Processor<i32> for NumberProcessor {
    type Output = f64;
    
    fn process(&self, input: i32) -> f64 {
        input as f64 * 2.0
    }
    
    fn can_process(&self, input: &i32) -> bool {
        *input > 0
    }
}

// Usage
let string_proc = StringProcessor;
let number_proc = NumberProcessor;

let result1 = string_proc.process("hello".to_string());
let result2 = number_proc.process(42);
```

### 4.2 Trait Object Pattern

#### Definition 4.2: Trait Object

A trait object that can hold any type implementing a trait.

**Formal Definition:**

```
Box<dyn Trait> or &dyn Trait where:
- Trait is object-safe
- Can hold any type implementing Trait
- Dynamic dispatch is used
```

#### Example 4.2: Trait Objects

```rust
trait Drawable {
    fn draw(&self);
}

struct Circle {
    radius: f64,
}

struct Rectangle {
    width: f64,
    height: f64,
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle with radius {}", self.radius);
    }
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("Drawing rectangle {}x{}", self.width, self.height);
    }
}

// Trait object usage
fn draw_shapes(shapes: Vec<Box<dyn Drawable>>) {
    for shape in shapes {
        shape.draw();
    }
}

let shapes: Vec<Box<dyn Drawable>> = vec![
    Box::new(Circle { radius: 5.0 }),
    Box::new(Rectangle { width: 10.0, height: 5.0 }),
];

draw_shapes(shapes);
```

## 5. Builder Patterns

### 5.1 Generic Builder Pattern

#### Definition 5.1: Generic Builder

A builder that can construct objects of any type with type-safe configuration.

**Formal Definition:**

```
Builder<T> where:
- T is the type to be built
- Builder provides fluent interface
- Type safety is maintained throughout building process
```

#### Example 5.1: Generic Builder

```rust
struct GenericBuilder<T> {
    data: Option<T>,
}

impl<T> GenericBuilder<T> {
    fn new() -> Self {
        GenericBuilder { data: None }
    }
    
    fn with_data(mut self, data: T) -> Self {
        self.data = Some(data);
        self
    }
    
    fn build(self) -> Result<T, String> {
        self.data.ok_or_else(|| "No data provided".to_string())
    }
}

// Usage
let result = GenericBuilder::<i32>::new()
    .with_data(42)
    .build()
    .unwrap();
```

### 5.2 Constrained Builder Pattern

#### Definition 5.2: Constrained Builder

A builder that requires its type parameter to satisfy constraints.

**Formal Definition:**

```
Builder<T: Constraint> where:
- T must satisfy Constraint
- Builder can use functionality from Constraint
- Type safety is enforced
```

#### Example 5.2: Constrained Builder

```rust
struct ValidatedBuilder<T: Clone + Display> {
    data: Option<T>,
    validation_rules: Vec<Box<dyn Fn(&T) -> bool>>,
}

impl<T: Clone + Display> ValidatedBuilder<T> {
    fn new() -> Self {
        ValidatedBuilder {
            data: None,
            validation_rules: Vec::new(),
        }
    }
    
    fn with_data(mut self, data: T) -> Self {
        self.data = Some(data);
        self
    }
    
    fn with_validation<F>(mut self, rule: F) -> Self
    where
        F: Fn(&T) -> bool + 'static
    {
        self.validation_rules.push(Box::new(rule));
        self
    }
    
    fn build(self) -> Result<T, String> {
        let data = self.data.ok_or_else(|| "No data provided".to_string())?;
        
        for (i, rule) in self.validation_rules.iter().enumerate() {
            if !rule(&data) {
                return Err(format!("Validation rule {} failed for {}", i, data));
            }
        }
        
        Ok(data)
    }
}

// Usage
let result = ValidatedBuilder::<i32>::new()
    .with_data(42)
    .with_validation(|x| *x > 0)
    .with_validation(|x| *x < 100)
    .build()
    .unwrap();
```

## 6. Iterator Patterns

### 6.1 Generic Iterator Pattern

#### Definition 6.1: Generic Iterator

An iterator that can iterate over any type while maintaining type safety.

**Formal Definition:**

```
Iterator<T> where:
- T is the element type
- Iterator provides sequential access to T
- Type safety is maintained throughout iteration
```

#### Example 6.1: Generic Iterator

```rust
struct GenericIterator<T> {
    data: Vec<T>,
    index: usize,
}

impl<T> GenericIterator<T> {
    fn new(data: Vec<T>) -> Self {
        GenericIterator { data, index: 0 }
    }
}

impl<T> Iterator for GenericIterator<T> {
    type Item = T;
    
    fn next(&mut self) -> Option<T> {
        if self.index < self.data.len() {
            let item = self.data.remove(self.index);
            Some(item)
        } else {
            None
        }
    }
}

// Usage
let data = vec![1, 2, 3, 4, 5];
let mut iter = GenericIterator::new(data);
while let Some(item) = iter.next() {
    println!("{}", item);
}
```

### 6.2 Iterator Adapter Pattern

#### Definition 6.2: Iterator Adapter

An iterator that transforms or filters another iterator.

**Formal Definition:**

```
Adapter<I, T, U> where:
- I: Iterator<Item = T>
- Adapter transforms T to U
- Type safety is maintained through transformation
```

#### Example 6.2: Iterator Adapters

```rust
struct MapIterator<I, F, T, U>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> U
{
    iter: I,
    f: F,
    _phantom: std::marker::PhantomData<(T, U)>,
}

impl<I, F, T, U> MapIterator<I, F, T, U>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> U
{
    fn new(iter: I, f: F) -> Self {
        MapIterator {
            iter,
            f,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<I, F, T, U> Iterator for MapIterator<I, F, T, U>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> U
{
    type Item = U;
    
    fn next(&mut self) -> Option<U> {
        self.iter.next().map(&self.f)
    }
}

struct FilterIterator<I, F, T>
where
    I: Iterator<Item = T>,
    F: Fn(&T) -> bool
{
    iter: I,
    predicate: F,
}

impl<I, F, T> FilterIterator<I, F, T>
where
    I: Iterator<Item = T>,
    F: Fn(&T) -> bool
{
    fn new(iter: I, predicate: F) -> Self {
        FilterIterator { iter, predicate }
    }
}

impl<I, F, T> Iterator for FilterIterator<I, F, T>
where
    I: Iterator<Item = T>,
    F: Fn(&T) -> bool
{
    type Item = T;
    
    fn next(&mut self) -> Option<T> {
        while let Some(item) = self.iter.next() {
            if (self.predicate)(&item) {
                return Some(item);
            }
        }
        None
    }
}

// Usage
let data = vec![1, 2, 3, 4, 5];
let iter = data.into_iter();
let mapped = MapIterator::new(iter, |x| x * 2);
let filtered = FilterIterator::new(mapped, |x| *x > 5);

for item in filtered {
    println!("{}", item); // Prints 6, 8, 10
}
```

## 7. Advanced Patterns

### 7.1 Type-Level State Pattern

#### Definition 7.1: Type-Level State

A pattern where states are represented as types for compile-time safety.

**Formal Definition:**

```
StateMachine<State> where:
- State represents the current state
- State transitions change the type parameter
- Invalid state transitions cause compile errors
```

#### Example 7.1: Type-Level State

```rust
use std::marker::PhantomData;

struct Uninitialized;
struct Initialized;
struct Running;
struct Stopped;

struct StateMachine<State> {
    data: String,
    _phantom: PhantomData<State>,
}

impl StateMachine<Uninitialized> {
    fn new() -> Self {
        StateMachine {
            data: String::new(),
            _phantom: PhantomData,
        }
    }
    
    fn initialize(self, data: String) -> StateMachine<Initialized> {
        StateMachine {
            data,
            _phantom: PhantomData,
        }
    }
}

impl StateMachine<Initialized> {
    fn start(self) -> StateMachine<Running> {
        StateMachine {
            data: self.data,
            _phantom: PhantomData,
        }
    }
}

impl StateMachine<Running> {
    fn stop(self) -> StateMachine<Stopped> {
        StateMachine {
            data: self.data,
            _phantom: PhantomData,
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// Usage
let machine = StateMachine::<Uninitialized>::new();
let machine = machine.initialize("Hello".to_string());
let machine = machine.start();
println!("Data: {}", machine.get_data());
let machine = machine.stop();
```

### 7.2 Phantom Type Pattern

#### Definition 7.2: Phantom Type

A pattern where type parameters provide compile-time safety without runtime representation.

**Formal Definition:**

```
PhantomType<T> where:
- T is used only at type level
- PhantomData<T> has zero runtime size
- T provides compile-time type information
```

#### Example 7.2: Phantom Types

```rust
use std::marker::PhantomData;

struct Meter;
struct Second;

struct Measurement<T> {
    value: f64,
    _phantom: PhantomData<T>,
}

impl Measurement<Meter> {
    fn new_meters(value: f64) -> Self {
        Measurement {
            value,
            _phantom: PhantomData,
        }
    }
    
    fn to_meters(&self) -> f64 {
        self.value
    }
}

impl Measurement<Second> {
    fn new_seconds(value: f64) -> Self {
        Measurement {
            value,
            _phantom: PhantomData,
        }
    }
    
    fn to_seconds(&self) -> f64 {
        self.value
    }
}

// Type safety prevents mixing units
let distance = Measurement::<Meter>::new_meters(5.0);
let time = Measurement::<Second>::new_seconds(10.0);
// let sum = distance + time; // Compile error: different types
```

## 8. Formal Proofs

### 8.1 Generic Pattern Soundness

#### Theorem 8.1: Generic Pattern Soundness

Generic patterns preserve type safety across all instantiations.

**Proof:**

```
1. Let Pattern<T> be a generic pattern
2. T satisfies all constraints of Pattern
3. Pattern provides functionality based on T's capabilities
4. No runtime errors can occur due to type mismatches
5. Therefore, generic patterns preserve type safety
```

### 8.2 Pattern Completeness

#### Theorem 8.2: Pattern Completeness

Generic patterns can express all necessary programming abstractions.

**Proof:**

```
1. Container patterns handle data storage
2. Function patterns handle computation
3. Trait patterns handle behavior
4. Iterator patterns handle iteration
5. All programming needs are covered
```

### 8.3 Pattern Correctness

#### Theorem 8.3: Pattern Correctness

Generic patterns provide correct behavior for all valid types.

**Proof:**

```
1. Patterns are defined in terms of type constraints
2. Constraints ensure required functionality is available
3. Implementation uses only guaranteed functionality
4. Behavior is correct for all satisfying types
5. Therefore, patterns are correct
```

## 9. Summary

Generic programming patterns provide:

1. **Reusability**: Patterns work with multiple types
2. **Type Safety**: Compile-time guarantees for all types
3. **Expressiveness**: Complex abstractions with simple interfaces
4. **Performance**: Zero-cost abstractions with no runtime overhead
5. **Correctness**: Formal proofs ensure pattern soundness

These patterns enable Rust to provide powerful, type-safe abstractions while maintaining compile-time guarantees and zero runtime overhead.

---

**References:**

- [Rust Book - Generic Types](https://doc.rust-lang.org/book/ch10-01-syntax.html)
- [Rust Book - Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)
- [Rust Reference - Generics](https://doc.rust-lang.org/reference/items/generics.html)
