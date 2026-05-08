//! Type System Frontier Concepts
//!
//! Covers advanced and cutting-edge type system features in Rust:
//! - Never type (`!`)
//! - Type Alias Impl Trait (TAIT)
//! - Return Position Impl Trait In Traits (RPITIT) / Async Fn In Traits (AFIT)
//! - Auto traits and negative impls
//! - Coherence and orphan rules

// ============================================================================
// 1. Never Type (`!`)
// ============================================================================

/// Explains the never type `!` — the bottom type in Rust's type system.
pub struct NeverTypeExplained;

impl NeverTypeExplained {
    /// Theoretical basis of `!`.
    pub fn what_is_never_type() -> &'static str {
        r#"The never type `!` is Rust's bottom type (⊥) in type theory.

It represents a computation that never completes normally:
- Diverging functions (panic, infinite loop)
- It is a subtype of every type (coerces to any type)
- It is the return type of `panic!()`, `todo!()`, `loop {}`, `unreachable!()`"#
    }

    /// `!` in practice.
    pub fn never_in_practice() -> &'static str {
        r#"Common sources of `!` in Rust:

1. `panic!("msg")` — aborts the current thread
2. `todo!()` — placeholder for unimplemented code
3. `loop {}` — infinite loop (if no break)
4. `unreachable!()` — indicates code that should never execute
5. `return`, `break`, `continue` — also produce `!` in expression position

All of these evaluate to `!`, which then coerces to the expected type."#
    }

    /// Demonstrates `!` coercing to any type.
    pub fn never_coercion_example() -> &'static str {
        r#"Because `!` is the bottom type, it coerces to any other type:

```rust
let x: i32 = panic!(); // compiles: `!` coerces to `i32`
let y: String = todo!(); // compiles: `!` coerces to `String`
let z: bool = unreachable!(); // compiles: `!` coerces to `bool`
```

This is why you can write `return val;` in any function regardless of return type."#
    }

    /// `!` in `Result<T, !>` for infallible operations.
    pub fn never_in_result() -> &'static str {
        r#"`Result<T, !>` represents an operation that can never fail.

The `Err` variant is uninhabited, so after checking `Ok`, the compiler
knows the operation succeeded:

```rust
fn always_succeeds() -> Result<String, !> {
    Ok("guaranteed success".into())
}

// No need to handle Err — it can never occur
let ok = always_succeeds().unwrap();
```

Stable alternative: `Result<T, std::convert::Infallible>`"#
    }

    /// `!` in control flow analysis.
    pub fn never_in_control_flow() -> &'static str {
        r#"`!` enables powerful exhaustiveness checking in match arms.

When a match arm diverges (panics/loops forever), it produces `!`.
The compiler uses this to verify all cases are covered:

```rust
match Some(42) {
    Some(v) => v,
    None => panic!("missing"), // `!` coerces to i32
}
```

In `std::process::Termination`, `!` implements `Termination`
so `main() -> !` is valid for servers that loop forever."#
    }

    /// Stability status of `!`.
    pub fn current_stability() -> &'static str {
        r#"`!` stabilization status:

- **1.41.0**: `!` coercions and `Result<T, !>` stabilized for most uses
- **Stable today**: `panic!()`, `todo!()`, `loop {}`, `unreachable!()` all work
- **Nightly edge cases**: Using `!` explicitly as a type annotation in all
  contexts requires `#![feature(never_type)]` (e.g., `let x: ! = panic!();`)
- Future: Full stabilization of explicit `!` type syntax is expected"#
    }

    /// Working example: infallible result using `!`.
    ///
    /// Since `#![feature(never_type)]` is enabled in this crate, we can
    /// use `!` directly in the type system.
    pub fn infallible_result_demo() -> Result<i32, !> {
        // This Result can never be Err.
        Ok(42)
    }
}

// ============================================================================
// 2. Type Alias Impl Trait (TAIT)
// ============================================================================

/// Explains `type Foo = impl Trait;` — Type Alias Impl Trait.
pub struct TypeAliasImplTrait;

impl TypeAliasImplTrait {
    /// What is TAIT.
    pub fn what_is_tait() -> &'static str {
        r#"Type Alias Impl Trait (TAIT) allows naming an opaque type:

```rust
#![feature(type_alias_impl_trait)]

type MyIter<T> = impl Iterator<Item = T>;

fn make_iter() -> MyIter<i32> {
    vec![1, 2, 3].into_iter()
}
```

Unlike `impl Trait` in return position, TAIT gives the opaque type a name
that can be reused across multiple functions and modules."#
    }

    /// Difference from RPIT.
    pub fn difference_from_rpit() -> &'static str {
        r#"Difference from RPIT (Return Position Impl Trait):

| Feature | `impl Trait` in return | `type Foo = impl Trait` |
|---------|----------------------|------------------------|
| Scope | Single function | Module-wide named type |
| Recursion | Limited | Supports recursive types |
| Type identity | Unique per function | Shared alias name |

RPIT: `fn f() -> impl Trait` — caller sees opaque type, unique to `f`.
TAIT: `type Foo = impl Trait; fn f() -> Foo` — caller sees `Foo`, which
may be returned by multiple functions."#
    }

    /// Use case: named opaque return types across modules.
    pub fn use_case_named_opaque() -> &'static str {
        r#"Use case: named opaque return types across modules.

When you want to return an opaque iterator or future from multiple
functions in the same module without exposing the concrete type:

```rust
#![feature(type_alias_impl_trait)]

type ParsedLines = impl Iterator<Item = String>;

fn from_file(path: &str) -> ParsedLines {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|s| s.to_string())
}

fn from_stdin() -> ParsedLines {
    std::io::stdin()
        .lines()
        .map(|l| l.unwrap())
}
```

Both functions return the same opaque `ParsedLines` type."#
    }

    /// Current status of TAIT.
    pub fn current_status() -> &'static str {
        r#"Current status: **Nightly only** (as of Rust 1.95+).

Requires `#![feature(type_alias_impl_trait)]`.

TAIT has been in development for several editions. While RPITIT
stabilized in 1.75, TAIT remains unstable because of open questions
around inference boundaries and recursive type checking.

Pre-research: Monitor the tracking issue for stabilization progress."#
    }

    /// Stable workaround: newtype wrapper around boxed trait objects.
    pub fn stable_workaround() -> Vec<String> {
        // Newtype wrapper to create a named opaque type
        struct Lines(Box<dyn Iterator<Item = String>>);

        impl Iterator for Lines {
            type Item = String;
            fn next(&mut self) -> Option<Self::Item> {
                self.0.next()
            }
        }

        let inner: Box<dyn Iterator<Item = String>> = Box::new(
            ["a", "b"].iter().map(|s| s.to_string()),
        );
        let lines = Lines(inner);
        lines.collect()
    }
}

// ============================================================================
// 3. RPITIT / AFIT
// ============================================================================

/// Explains Return Position Impl Trait In Traits (RPITIT) and
/// Async Fn In Traits (AFIT).
pub struct ImplTraitInAssocType;

/// A trait demonstrating RPITIT.
pub trait Producer {
    /// Produce something implementing `Product`.
    fn make() -> impl Product;
}

/// A product that can be produced.
pub trait Product {
    /// Name of the product.
    fn name(&self) -> &str;
}

struct Widget;

impl Product for Widget {
    fn name(&self) -> &str {
        "Widget"
    }
}

#[allow(dead_code)]
struct Gadget;

impl Product for Gadget {
    fn name(&self) -> &str {
        "Gadget"
    }
}

struct WidgetProducer;

impl Producer for WidgetProducer {
    fn make() -> impl Product {
        Widget
    }
}

#[allow(dead_code)]
struct GadgetProducer;

impl Producer for GadgetProducer {
    fn make() -> impl Product {
        Gadget
    }
}

/// Async trait demonstrating AFIT.
#[allow(async_fn_in_trait)]
pub trait AsyncProducer {
    /// Asynchronously produce a value.
    async fn make() -> i32;
}

struct AsyncWidgetProducer;

impl AsyncProducer for AsyncWidgetProducer {
    async fn make() -> i32 {
        42
    }
}

impl ImplTraitInAssocType {
    /// What is RPITIT.
    pub fn what_is_rpitit() -> &'static str {
        r#"RPITIT (Return Position Impl Trait In Traits) allows writing:

```rust
trait Producer {
    fn make() -> impl Product;
}
```

This is distinct from the associated type approach:

```rust
trait Producer {
    type Output: Product;
    fn make() -> Self::Output;
}
```

RPITIT desugars to an anonymous associated type under the hood,
but the syntax is far more ergonomic."#
    }

    /// Practical RPITIT example.
    pub fn rpitit_example() -> String {
        WidgetProducer::make().name().to_string()
    }

    /// Comparison with associated type approach.
    pub fn associated_type_comparison() -> &'static str {
        r#"Comparison: RPITIT vs Associated Types

**Associated Type approach (pre-1.75 / manual):**
```rust
trait Producer {
    type Output: Product;
    fn make() -> Self::Output;
}
```
- Caller can name the concrete type via `<T as Producer>::Output`
- Each impl chooses exactly one concrete type
- More verbose, leaks implementation detail in type signatures

**RPITIT approach (stable since 1.75):**
```rust
trait Producer {
    fn make() -> impl Product;
}
```
- Opaque return type — caller only knows it implements `Product`
- Cleaner syntax, no extra type parameter
- Same capabilities for most use cases

Recommendation: Use RPITIT for new traits unless you need to reference
the concrete associated type from other trait bounds."#
    }

    /// What is AFIT.
    pub fn what_is_afit() -> &'static str {
        r#"AFIT (Async Fn In Traits) is the ability to write `async fn`
directly in a trait definition.

```rust
trait AsyncProducer {
    async fn make() -> i32;
}
```

Before 1.75, you had to manually return `Pin<Box<dyn Future<Output = ...>>>`
or use the `async-trait` crate. Now it is native and zero-cost.

AFIT builds on RPITIT: `async fn` desugars to `fn() -> impl Future`,
and RPITIT allows that `impl Future` in trait position."#
    }

    /// Practical AFIT example.
    pub async fn afit_example() -> i32 {
        AsyncWidgetProducer::make().await
    }
}

// ============================================================================
// 4. Auto Traits
// ============================================================================

/// Explains auto traits (Send, Sync, Unpin, UnwindSafe) and related concepts.
pub struct AutoTraitsDeepDive;

/// A type that uses `PhantomData` to inherit auto trait bounds from `T`.
#[allow(dead_code)]
pub struct TypedHandle<T> {
    id: u64,
    _marker: std::marker::PhantomData<T>,
}

impl AutoTraitsDeepDive {
    /// What are auto traits.
    pub fn what_are_auto_traits() -> &'static str {
        r#"Auto traits are traits that the compiler automatically implements
for a type if all of its constituent fields implement the trait.

Built-in auto traits:
- `Send`: safe to send to another thread
- `Sync`: safe to share between threads
- `Unpin`: safe to move after pinning
- `UnwindSafe`: safe to survive a panic unwind

The compiler derives these automatically — no `#[derive]` needed."#
    }

    /// How auto impl works.
    pub fn how_auto_impl_works() -> &'static str {
        r#"How auto traits are automatically implemented:

For a struct `Foo<T>`:
- `Foo<T>: Send` if and only if `T: Send` (and all other fields are Send)
- `Foo<T>: Sync` if and only if `T: Sync` (and all other fields are Sync)

For generic types, the compiler adds implicit bounds:
```rust
struct Wrapper<T>(T);
// Implicitly: impl<T: Send> Send for Wrapper<T> {}
```

This is why `Vec<T>: Send` requires `T: Send`."#
    }

    /// Negative impls concept (nightly only).
    pub fn negative_impls_concept() -> &'static str {
        r#"Negative impls allow explicitly opting out of an auto trait:

```rust
#![feature(negative_impls)]

impl !Send for LocalOnly {}
impl !Sync for LocalOnly {}
```

This is useful when a type contains thread-local data or raw pointers
that should prevent cross-thread usage.

**Status: Nightly only** (`#![feature(negative_impls)]`).

Stable workaround: Use `PhantomData<*const ()>` or `PhantomData<Cell<()>>`
to prevent Send/Sync auto-derivation."#
    }

    /// Marker traits with PhantomData (stable working example).
    pub fn marker_traits_with_phantom() -> String {
        use std::marker::PhantomData;

        // TypedHandle<T> uses PhantomData<T> to inherit T's auto trait bounds
        let handle: TypedHandle<String> = TypedHandle {
            id: 1,
            _marker: PhantomData,
        };

        // TypedHandle<String> is Send because String is Send
        let _ = send_check(handle);

        fn send_check<T: Send>(_: T) -> &'static str {
            "Send"
        }

        "TypedHandle<T> inherits Send/Sync from T via PhantomData".to_string()
    }

    /// When custom auto traits are useful.
    pub fn when_custom_auto_trait() -> &'static str {
        r#"When to implement custom auto traits (rare but useful):

Custom auto traits allow creating marker traits that propagate
automatically through the type system. Use cases:

1. **Capability tracking**: Mark types that are 'GPU-safe' or 'network-safe'
2. **Invariant preservation**: Ensure a type maintains a custom invariant
   when wrapped in containers
3. **Feature gating**: Conditionally enable APIs based on auto trait bounds

**Status**: Defining new auto traits requires `#![feature(auto_traits)]`
on nightly.

Stable alternative: Use standard marker traits + manual impls + `PhantomData`."#
    }
}

// ============================================================================
// 5. Coherence and Orphan Rules
// ============================================================================

/// Explains coherence, orphan rules, and workarounds.
pub struct CoherenceAndOrphanRules;

/// Newtype wrapper demonstrating the orphan rule workaround.
pub struct MyString(String);

impl AsRef<str> for MyString {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

/// Another newtype wrapper.
pub struct MyVec<T>(Vec<T>);

impl<T> std::ops::Deref for MyVec<T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl CoherenceAndOrphanRules {
    /// What is coherence.
    pub fn what_is_coherence() -> &'static str {
        r#"Coherence is the property that ensures there is at most one
implementation of a trait for any given type.

Rust enforces coherence so that:
1. The compiler always knows which `impl` to dispatch to
2. Adding a new crate to your dependency graph cannot break existing code
   by introducing conflicting impls

This is fundamental to Rust's trait system reliability."#
    }

    /// Orphan rules explained.
    pub fn orphan_rules_explained() -> &'static str {
        r#"Orphan rules determine who is allowed to implement a trait for a type.

The basic rule: at least one of the trait or the type must be defined
in the current crate.

**Allowed:**
```rust
// Local trait, foreign type
trait MyTrait {}
impl MyTrait for String {}

// Foreign trait, local type
impl Display for MyLocalType {}
```

**Forbidden:**
```rust
// Foreign trait, foreign type
impl Display for String {} // ERROR!
```

This prevents two different crates from implementing `Display for String`
in conflicting ways."#
    }

    /// `#[fundamental]` types.
    pub fn fundamental_types() -> &'static str {
        r#"`#[fundamental]` types relax orphan rules.

The following types are `#[fundamental]`:
- `Box<T>`
- `Pin<T>`
- `&T`
- `&mut T`

For fundamental types, you can implement a foreign trait for
`Box<YourLocalType>` because the outer type is considered "local"
when the inner type is local.

Example:
```rust
trait ForeignTrait {}
struct LocalType;

// Allowed because Box is #[fundamental] and contains a local type
impl ForeignTrait for Box<LocalType> {}
```"#
    }

    /// Newtype workaround (working code).
    pub fn newtype_workaround() -> String {
        let my = MyString("hello".to_string());
        my.as_ref().to_string()
    }

    /// Trait delegation pattern.
    pub fn trait_delegation_pattern() -> &'static str {
        r#"Trait delegation pattern (alternative to newtype):

When the newtype wrapper is too tedious, some crates use macros to
automatically delegate trait methods to the inner type:

```rust
macro_rules! delegate_display {
    ($wrapper:ty) => {
        impl std::fmt::Display for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
    };
}

delegate_display!(MyString);
```

Or use the `derive_more` / `delegate` crates from crates.io."#
    }

    /// Why coherence matters.
    pub fn why_coherence_matters() -> &'static str {
        r#"Why coherence matters for ecosystem compatibility:

1. **Composability**: You can use any two crates together without fear
   that they both defined conflicting impls for the same type.

2. **API Evolution**: Crate authors can add new impls without breaking
   downstream consumers (as long as orphan rules are respected).

3. **Binary Size**: Coherence enables monomorphization — the compiler
   knows exactly which function to inline for each concrete type.

Without coherence, Rust would face the 'impl collision' problem that
makes C++ template specialization so fragile."#
    }
}

// ============================================================================
// 6. Type Family Demo — 类型族在 Rust 中的实际应用
// ============================================================================

/// 类型族（Type Families）概念演示
///
/// 类型族允许根据一个类型参数选择另一个相关类型。
/// Rust 中通过关联类型（associated types）实现。
pub struct TypeFamilyDemo;

/// 容器类型族 trait
pub trait ContainerFamily {
    type Container<T>: Container<T>;
}

/// 容器 trait
pub trait Container<T> {
    fn new(items: Vec<T>) -> Self;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

/// 列表容器族
pub struct ListFamily;

impl ContainerFamily for ListFamily {
    type Container<T> = Vec<T>;
}

impl<T> Container<T> for Vec<T> {
    fn new(items: Vec<T>) -> Self {
        items
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
}

/// 树形容器族（简化版）
pub struct TreeFamily;

pub struct SimpleTree<T> {
    root: Option<T>,
    children: Vec<SimpleTree<T>>,
}

impl ContainerFamily for TreeFamily {
    type Container<T> = SimpleTree<T>;
}

impl<T> Container<T> for SimpleTree<T> {
    fn new(items: Vec<T>) -> Self {
        let mut iter = items.into_iter();
        Self {
            root: iter.next(),
            children: iter.map(|item| SimpleTree { root: Some(item), children: vec![] }).collect(),
        }
    }
    fn len(&self) -> usize {
        1 + self.children.iter().map(|c| c.len()).sum::<usize>()
    }
    fn is_empty(&self) -> bool {
        self.root.is_none()
    }
}

impl TypeFamilyDemo {
    /// 使用类型族创建容器
    pub fn create_container<F, T>(items: Vec<T>) -> F::Container<T>
    where
        F: ContainerFamily,
    {
        F::Container::new(items)
    }

    /// 展示同一份代码对不同类型族工作
    pub fn add_i32(a: i32, b: i32) -> i32 {
        a + b
    }

    /// 展示同一份代码对不同类型族工作
    pub fn add_f64(a: f64, b: f64) -> f64 {
        a + b
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------------
    // NeverTypeExplained tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_what_is_never_type() {
        assert!(!NeverTypeExplained::what_is_never_type().is_empty());
    }

    #[test]
    fn test_never_in_practice() {
        assert!(!NeverTypeExplained::never_in_practice().is_empty());
    }

    #[test]
    fn test_never_coercion_example() {
        assert!(!NeverTypeExplained::never_coercion_example().is_empty());
    }

    #[test]
    fn test_never_in_result() {
        assert!(!NeverTypeExplained::never_in_result().is_empty());
    }

    #[test]
    fn test_never_in_control_flow() {
        assert!(!NeverTypeExplained::never_in_control_flow().is_empty());
    }

    #[test]
    fn test_current_stability_never() {
        assert!(!NeverTypeExplained::current_stability().is_empty());
    }

    #[test]
    fn test_infallible_result_demo() {
        let res = NeverTypeExplained::infallible_result_demo();
        assert_eq!(res.unwrap(), 42);
    }

    // ------------------------------------------------------------------------
    // TypeAliasImplTrait tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_what_is_tait() {
        assert!(!TypeAliasImplTrait::what_is_tait().is_empty());
    }

    #[test]
    fn test_difference_from_rpit() {
        assert!(!TypeAliasImplTrait::difference_from_rpit().is_empty());
    }

    #[test]
    fn test_use_case_named_opaque() {
        assert!(!TypeAliasImplTrait::use_case_named_opaque().is_empty());
    }

    #[test]
    fn test_tait_current_status() {
        assert!(!TypeAliasImplTrait::current_status().is_empty());
    }

    #[test]
    fn test_stable_workaround() {
        let result = TypeAliasImplTrait::stable_workaround();
        assert_eq!(result, vec!["a", "b"]);
    }

    // ------------------------------------------------------------------------
    // ImplTraitInAssocType tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_what_is_rpitit() {
        assert!(!ImplTraitInAssocType::what_is_rpitit().is_empty());
    }

    #[test]
    fn test_rpitit_example() {
        assert_eq!(ImplTraitInAssocType::rpitit_example(), "Widget");
    }

    #[test]
    fn test_associated_type_comparison() {
        assert!(!ImplTraitInAssocType::associated_type_comparison().is_empty());
    }

    #[test]
    fn test_what_is_afit() {
        assert!(!ImplTraitInAssocType::what_is_afit().is_empty());
    }

    #[test]
    fn test_afit_example() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        let result = rt.block_on(ImplTraitInAssocType::afit_example());
        assert_eq!(result, 42);
    }

    // ------------------------------------------------------------------------
    // AutoTraitsDeepDive tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_what_are_auto_traits() {
        assert!(!AutoTraitsDeepDive::what_are_auto_traits().is_empty());
    }

    #[test]
    fn test_how_auto_impl_works() {
        assert!(!AutoTraitsDeepDive::how_auto_impl_works().is_empty());
    }

    #[test]
    fn test_negative_impls_concept() {
        assert!(!AutoTraitsDeepDive::negative_impls_concept().is_empty());
    }

    #[test]
    fn test_marker_traits_with_phantom() {
        let result = AutoTraitsDeepDive::marker_traits_with_phantom();
        assert!(result.contains("PhantomData"));
    }

    #[test]
    fn test_when_custom_auto_trait() {
        assert!(!AutoTraitsDeepDive::when_custom_auto_trait().is_empty());
    }

    // ------------------------------------------------------------------------
    // CoherenceAndOrphanRules tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_what_is_coherence() {
        assert!(!CoherenceAndOrphanRules::what_is_coherence().is_empty());
    }

    #[test]
    fn test_orphan_rules_explained() {
        assert!(!CoherenceAndOrphanRules::orphan_rules_explained().is_empty());
    }

    #[test]
    fn test_fundamental_types() {
        assert!(!CoherenceAndOrphanRules::fundamental_types().is_empty());
    }

    #[test]
    fn test_newtype_workaround() {
        assert_eq!(CoherenceAndOrphanRules::newtype_workaround(), "hello");
    }

    #[test]
    fn test_trait_delegation_pattern() {
        assert!(!CoherenceAndOrphanRules::trait_delegation_pattern().is_empty());
    }

    #[test]
    fn test_why_coherence_matters() {
        assert!(!CoherenceAndOrphanRules::why_coherence_matters().is_empty());
    }

    // ------------------------------------------------------------------------
    // TypeFamilyDemo tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_type_family_add() {
        assert_eq!(TypeFamilyDemo::add_i32(3, 4), 7);
        assert_eq!(TypeFamilyDemo::add_f64(3.0, 4.0), 7.0);
    }

    #[test]
    fn test_type_family_container() {
        let list = TypeFamilyDemo::create_container::<ListFamily, _>(vec![1, 2, 3]);
        assert_eq!(list.len(), 3);

        let tree = TypeFamilyDemo::create_container::<TreeFamily, _>(vec![1, 2, 3]);
        assert_eq!(tree.len(), 3);
    }
}
