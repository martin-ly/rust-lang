# Chapter 11: Rust Design Patterns - Deep Dive with Formal Semantics

## Executive Summary

This chapter provides a comprehensive, formal treatment of design patterns in Rust, bridging classical GoF patterns with Rust's ownership-centric paradigm.
We establish rigorous semantic foundations for pattern formalization, prove key theorems about pattern correctness, and provide extensive counter-examples demonstrating common pitfalls.

**Key Contributions:**

- Formal semantics for pattern structure in ownership-aware contexts
- Complete adaptation of all 23 GoF patterns for Rust
- 15+ detailed counter-examples with explanations
- 5+ formal theorems with proofs
- Performance analysis and anti-pattern identification

---

## 1. Design Pattern Formalization

### 1.1 Pattern Structure

We formalize design patterns as quintuples:

```
Pattern = (Name, Problem, Solution, Consequences, Examples)
```

Where:

- **Name**: Unique identifier for the pattern
- **Problem**: Context and forces requiring the pattern
- **Solution**: Structural and behavioral elements
- **Consequences**: Trade-offs and implications
- **Examples**: Concrete Rust implementations

#### 1.1.1 Formal Definition

```rust
/// Pattern descriptor trait for documentation purposes
trait Pattern {
    /// Pattern name
    const NAME: &'static str;

    /// Problem description
    const PROBLEM: &'static str;

    /// Consequences analysis
    const CONSEQUENCES: &'static str;
}
```

#### 1.1.2 Ownership-Aware Pattern Classification

Patterns in Rust must respect ownership rules. We classify patterns by their ownership interaction:

```
OwnershipClassification =
    | Transfer       // Takes ownership
    | Borrow         // Takes reference
    | InteriorMut    // Uses interior mutability
    | CopySemantics  // Relies on Copy trait
```

```rust
/// Marker trait for ownership classification
mod classification {
    pub struct Transfer;
    pub struct Borrow;
    pub struct InteriorMut;
    pub struct CopySemantics;
}
```

### 1.2 Pattern Correctness Criteria

**Definition 1.1 (Pattern Soundness)**: A pattern P is *sound* if for all valid inputs, its implementation does not violate Rust's ownership rules or trigger undefined behavior.

**Definition 1.2 (Pattern Completeness)**: A pattern P is *complete* if it handles all specified use cases within its problem domain.

**Definition 1.3 (Pattern Compositionality)**: Patterns P₁ and P₂ are *composable* if their combined usage maintains soundness and completeness.

---

## 2. Creational Patterns

### 2.1 Builder Pattern

The Builder pattern separates construction of complex objects from their representation.

#### 2.1.1 Problem

```
PROBLEM BUILDER:
    Given: Complex object with many optional fields
    Constraint: Step-by-step construction needed
    Constraint: Different configurations require same construction code
    Constraint: Must ensure all required fields are set
```

#### 2.1.2 Solution Structure

```rust
/// Target complex type
#[derive(Debug, Clone)]
pub struct HttpRequest {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
    timeout: Duration,
    retries: u32,
}

/// Builder for HttpRequest
pub struct HttpRequestBuilder {
    method: Option<String>,
    url: Option<String>,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
    timeout: Option<Duration>,
    retries: Option<u32>,
}

impl HttpRequestBuilder {
    /// Create new builder instance
    pub fn new() -> Self {
        Self {
            method: None,
            url: None,
            headers: Vec::new(),
            body: None,
            timeout: None,
            retries: None,
        }
    }

    /// Set HTTP method (required)
    pub fn method(mut self, method: impl Into<String>) -> Self {
        self.method = Some(method.into());
        self
    }

    /// Set URL (required)
    pub fn url(mut self, url: impl Into<String>) -> Self {
        self.url = Some(url.into());
        self
    }

    /// Add header (optional, repeatable)
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.push((key.into(), value.into()));
        self
    }

    /// Set body (optional)
    pub fn body(mut self, body: impl Into<Vec<u8>>) -> Self {
        self.body = Some(body.into());
        self
    }

    /// Set timeout (optional with default)
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Set retry count (optional with default)
    pub fn retries(mut self, retries: u32) -> Self {
        self.retries = Some(retries);
        self
    }

    /// Build the request (consumes self)
    ///
    /// # Panics
    /// Panics if required fields are not set (runtime check)
    pub fn build(self) -> HttpRequest {
        HttpRequest {
            method: self.method.expect("Method is required"),
            url: self.url.expect("URL is required"),
            headers: self.headers,
            body: self.body,
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
            retries: self.retries.unwrap_or(3),
        }
    }
}

impl Default for HttpRequestBuilder {
    fn default() -> Self {
        Self::new()
    }
}
```

#### 2.1.3 Theorem BUILDER-COMPLETENESS

**Theorem**: Given a builder B with required fields R and optional fields O, if B.build() is called after all fields in R have been set, the resulting object is complete.

**Proof**:

1. Let R = {r₁, r₂, ..., rₙ} be the set of required fields
2. Let S ⊆ R be the set of fields that have been set
3. By construction, B.build() checks S = R via Option::expect()
4. If S = R, all required fields are Some(_), build succeeds
5. If S ⊂ R, at least one field is None, panic occurs
6. Therefore, successful build implies S = R, guaranteeing completeness ∎

**Runtime Guarantee**: The current implementation uses runtime checks. For compile-time guarantees, see Type-State Builder.

#### 2.1.4 Ownership Semantics

```rust
/// Demonstrating ownership transfer in builder
fn builder_ownership_demo() {
    let data = vec![1, 2, 3];

    // Ownership transferred to builder, then to request
    let request = HttpRequestBuilder::new()
        .method("POST")
        .url("https://api.example.com")
        .body(data)  // data moved here
        .build();

    // data is no longer accessible - ownership transferred
    // println!("{:?}", data); // ERROR: use of moved value
}
```

**Ownership Flow**:

```
Caller → Builder::body() → Builder field → HttpRequest::body
   │           │                │              │
   │           │                │              └── Owns Vec<u8>
   │           │                └── Owns Vec<u8>
   │           └── Takes ownership
   └── Original owner
```

#### 2.1.5 Performance Characteristics

| Aspect | Cost | Notes |
|--------|------|-------|
| Builder creation | O(1) | Stack allocation |
| Each setter | O(1) | Moves value, no copy |
| build() | O(1) | Unwraps Options |
| Memory overhead | 1x | No double allocation |

---

### 2.2 Type-State Builder

The Type-State Builder uses the type system to enforce correct construction at compile time.

#### 2.2.1 Problem

```
PROBLEM TYPE-STATE-BUILDER:
    Given: Builder with required fields
    Constraint: Runtime errors for missing fields unacceptable
    Constraint: Must enforce correct order of operations
    Constraint: Invalid states must be unrepresentable
```

#### 2.2.2 Solution Structure

```rust
use std::marker::PhantomData;

/// State markers (zero-sized types)
pub struct NoMethod;
pub struct MethodSet;
pub struct NoUrl;
pub struct UrlSet;

/// Type-state builder for HttpRequest
pub struct TypedHttpRequestBuilder<MethodState, UrlState> {
    method: Option<String>,
    url: Option<String>,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
    timeout: Option<Duration>,
    retries: Option<u32>,
    _method_state: PhantomData<MethodState>,
    _url_state: PhantomData<UrlState>,
}

/// Only allow build when both method and URL are set
impl TypedHttpRequestBuilder<MethodSet, UrlSet> {
    pub fn build(self) -> HttpRequest {
        HttpRequest {
            method: self.method.unwrap(),  // Safe: type guarantees Some
            url: self.url.unwrap(),        // Safe: type guarantees Some
            headers: self.headers,
            body: self.body,
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
            retries: self.retries.unwrap_or(3),
        }
    }
}

impl TypedHttpRequestBuilder<NoMethod, NoUrl> {
    pub fn new() -> Self {
        Self {
            method: None,
            url: None,
            headers: Vec::new(),
            body: None,
            timeout: None,
            retries: None,
            _method_state: PhantomData,
            _url_state: PhantomData,
        }
    }

    pub fn method(self, method: impl Into<String>) -> TypedHttpRequestBuilder<MethodSet, NoUrl> {
        TypedHttpRequestBuilder {
            method: Some(method.into()),
            url: self.url,
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
            retries: self.retries,
            _method_state: PhantomData,
            _url_state: PhantomData,
        }
    }
}

impl TypedHttpRequestBuilder<MethodSet, NoUrl> {
    pub fn url(self, url: impl Into<String>) -> TypedHttpRequestBuilder<MethodSet, UrlSet> {
        TypedHttpRequestBuilder {
            method: self.method,
            url: Some(url.into()),
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
            retries: self.retries,
            _method_state: PhantomData,
            _url_state: PhantomData,
        }
    }
}

impl TypedHttpRequestBuilder<NoMethod, UrlSet> {
    pub fn method(self, method: impl Into<String>) -> TypedHttpRequestBuilder<MethodSet, UrlSet> {
        TypedHttpRequestBuilder {
            method: Some(method.into()),
            url: self.url,
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
            retries: self.retries,
            _method_state: PhantomData,
            _url_state: PhantomData,
        }
    }
}

/// Optional field setters (available in all states)
impl<MethodState, UrlState> TypedHttpRequestBuilder<MethodState, UrlState> {
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.push((key.into(), value.into()));
        self
    }

    pub fn body(mut self, body: impl Into<Vec<u8>>) -> Self {
        self.body = Some(body.into());
        self
    }

    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    pub fn retries(mut self, retries: u32) -> Self {
        self.retries = Some(retries);
        self
    }
}
```

#### 2.2.3 Type State Transitions

```
                    ┌─────────────────────────────────────┐
                    │                                     │
                    ▼                                     │
┌─────────┐    ┌───────────┐    ┌───────────┐    ┌───────┴──────┐
│ NoMethod│───▶│ MethodSet │───▶│ MethodSet │───▶│   HttpRequest │
│   NoUrl │    │    NoUrl  │    │   UrlSet  │    │   (build)     │
└─────────┘    └───────────┘    └───────────┘    └──────────────┘
      │                                              ▲
      │         ┌───────────┐    ┌───────────┐       │
      └────────▶│    NoUrl  │───▶│   UrlSet  │───────┘
                │   UrlSet  │    │  MethodSet│
                └───────────┘    └───────────┘
```

#### 2.2.4 Theorem TYPE-STATE-SAFETY

**Theorem**: For any type-state builder B with states S₁ → S₂ → ... → Sₙ, if B.build() requires state Sₙ, then calling build() without reaching Sₙ is a compile-time error.

**Proof**:

1. Builder states are represented as type parameters
2. Transition methods consume self and return builder with new state type
3. build() is only implemented for B<Sₙ>
4. Attempting build() on B<Sᵢ> where i < n results in "method not found" at compile time
5. Therefore, invalid states are unrepresentable in the type system ∎

#### 2.2.5 Usage Example

```rust
fn type_state_usage() {
    // This works - all required fields set
    let request = TypedHttpRequestBuilder::new()
        .method("GET")
        .url("https://api.example.com")
        .header("Accept", "application/json")
        .timeout(Duration::from_secs(10))
        .build();

    // Order can vary
    let request2 = TypedHttpRequestBuilder::new()
        .url("https://api.example.com")
        .method("POST")
        .body(vec![1, 2, 3])
        .build();

    // This does NOT compile - method not set
    // let invalid = TypedHttpRequestBuilder::new()
    //     .url("https://example.com")
    //     .build();  // ERROR: no method `build` found
}
```

#### 2.2.6 Comparison: Runtime vs Type-State Builder

| Aspect | Runtime Builder | Type-State Builder |
|--------|-----------------|-------------------|
| Error detection | Runtime | Compile time |
| Binary size | Smaller | Larger (monomorphization) |
| Compilation time | Faster | Slower |
| API complexity | Lower | Higher |
| Zero-cost | Yes | Yes |
| Flexibility | Higher | Lower |

---

### 2.3 Factory Pattern

#### 2.3.1 Simple Factory

```rust
/// Trait for creatable objects
pub trait Connection: Send + Sync {
    fn connect(&mut self) -> Result<(), ConnectionError>;
    fn disconnect(&mut self);
    fn is_connected(&self) -> bool;
}

#[derive(Debug)]
pub struct ConnectionError;

/// Factory for creating connections
pub struct ConnectionFactory;

impl ConnectionFactory {
    pub fn create(protocol: &str) -> Box<dyn Connection> {
        match protocol {
            "tcp" => Box::new(TcpConnection::new()),
            "udp" => Box::new(UdpConnection::new()),
            "http" => Box::new(HttpConnection::new()),
            _ => panic!("Unknown protocol: {}", protocol),
        }
    }
}

pub struct TcpConnection { connected: bool }
impl TcpConnection { fn new() -> Self { Self { connected: false } } }
impl Connection for TcpConnection {
    fn connect(&mut self) -> Result<(), ConnectionError> { self.connected = true; Ok(()) }
    fn disconnect(&mut self) { self.connected = false; }
    fn is_connected(&self) -> bool { self.connected }
}

pub struct UdpConnection { connected: bool }
impl UdpConnection { fn new() -> Self { Self { connected: false } } }
impl Connection for UdpConnection {
    fn connect(&mut self) -> Result<(), ConnectionError> { self.connected = true; Ok(()) }
    fn disconnect(&mut self) { self.connected = false; }
    fn is_connected(&self) -> bool { self.connected }
}

pub struct HttpConnection { connected: bool }
impl HttpConnection { fn new() -> Self { Self { connected: false } } }
impl Connection for HttpConnection {
    fn connect(&mut self) -> Result<(), ConnectionError> { self.connected = true; Ok(()) }
    fn disconnect(&mut self) { self.connected = false; }
    fn is_connected(&self) -> bool { self.connected }
}
```

#### 2.3.2 Generic Factory

```rust
/// Generic factory with registration
pub struct GenericFactory<T> {
    creators: HashMap<String, Box<dyn Fn() -> T + Send + Sync>>,
}

impl<T> GenericFactory<T> {
    pub fn new() -> Self {
        Self {
            creators: HashMap::new(),
        }
    }

    pub fn register<F>(&mut self, name: &str, creator: F)
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        self.creators.insert(name.to_string(), Box::new(creator));
    }

    pub fn create(&self, name: &str) -> Option<T> {
        self.creators.get(name).map(|creator| creator())
    }
}
```

---

## 3. Structural Patterns

### 3.1 Newtype Pattern

The Newtype pattern creates a distinct type with the same runtime representation.

#### 3.1.1 Problem

```
PROBLEM NEWTYPE:
    Given: Primitive type (e.g., u32)
    Constraint: Must distinguish between different uses
    Constraint: Must add type-specific behavior
    Constraint: Zero runtime overhead required
```

#### 3.1.2 Solution Structure

```rust
/// Base unit type
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Meters(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Kilometers(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Millimeters(u64);

impl Meters {
    pub fn new(value: u32) -> Self {
        Self(value)
    }

    pub fn value(&self) -> u32 {
        self.0
    }

    pub fn to_kilometers(&self) -> Kilometers {
        Kilometers(self.0 / 1000)
    }

    pub fn to_millimeters(&self) -> Millimeters {
        Millimeters(self.0 as u64 * 1000)
    }
}

impl Kilometers {
    pub fn new(value: u32) -> Self {
        Self(value)
    }

    pub fn value(&self) -> u32 {
        self.0
    }

    pub fn to_meters(&self) -> Meters {
        Meters(self.0 * 1000)
    }
}

impl Millimeters {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(&self) -> u64 {
        self.0
    }

    pub fn to_meters(&self) -> Meters {
        Meters((self.0 / 1000) as u32)
    }
}

// Type-safe operations prevent mixing units
fn calculate_distance() {
    let distance1 = Meters::new(500);
    let distance2 = Kilometers::new(2);

    // This would be a type error:
    // let sum = distance1 + distance2; // ERROR: expected Meters, found Kilometers

    // Correct approach:
    let total_meters = Meters::new(distance1.value() + distance2.to_meters().value());
}
```

#### 3.1.3 Theorem NEWTYPE-ZERO-COST

**Theorem**: For a newtype NT wrapping type T, sizeof(NT) = sizeof(T) and operations on NT have identical performance to operations on T.

**Proof**:

1. Rust represents single-field structs identically to the field type (ABI guarantee)
2. Methods on newtype are monomorphized to direct operations on the inner value
3. No vtable or indirection is introduced
4. Therefore, sizeof(NT) = sizeof(T) and performance is identical ∎

#### 3.1.4 Newtype for Validation

```rust
/// Validated email type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Email(String);

impl Email {
    /// Validates and creates Email, returns None if invalid
    pub fn new(address: impl Into<String>) -> Option<Self> {
        let address = address.into();
        if Self::is_valid(&address) {
            Some(Self(address))
        } else {
            None
        }
    }

    /// Unchecked creation - use only when certain of validity
    ///
    /// # Safety
    /// Caller must ensure address is valid
    pub unsafe fn new_unchecked(address: impl Into<String>) -> Self {
        Self(address.into())
    }

    fn is_valid(address: &str) -> bool {
        address.contains('@') && !address.is_empty()
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}
```

---

### 3.2 RAII Guard Pattern

RAII (Resource Acquisition Is Initialization) ensures resources are released when guards go out of scope.

#### 3.2.1 Problem

```
PROBLEM RAII-GUARD:
    Given: Resource that must be released after use
    Constraint: Release must happen even on panic/early return
    Constraint: No manual cleanup calls
    Constraint: Resource has scope-bound lifetime
```

#### 3.2.2 Solution Structure

```rust
use std::ops::{Deref, DerefMut};

/// Managed resource
pub struct DatabaseConnection {
    id: u64,
    active: bool,
}

impl DatabaseConnection {
    fn new(id: u64) -> Self {
        println!("Opening connection {}", id);
        Self { id, active: true }
    }

    fn close(&mut self) {
        if self.active {
            println!("Closing connection {}", self.id);
            self.active = false;
        }
    }

    fn query(&self, sql: &str) -> Vec<String> {
        vec![format!("Result for: {}", sql)]
    }
}

/// RAII guard for database connection
pub struct ConnectionGuard {
    conn: DatabaseConnection,
}

impl ConnectionGuard {
    pub fn new(id: u64) -> Self {
        Self {
            conn: DatabaseConnection::new(id),
        }
    }

    /// Explicit close (optional)
    pub fn close(mut self) {
        self.conn.close();
    }
}

impl Deref for ConnectionGuard {
    type Target = DatabaseConnection;

    fn deref(&self) -> &Self::Target {
        &self.conn
    }
}

impl DerefMut for ConnectionGuard {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.conn
    }
}

impl Drop for ConnectionGuard {
    fn drop(&mut self) {
        self.conn.close();
    }
}

/// Usage demonstrates automatic cleanup
fn raii_usage() {
    {
        let conn = ConnectionGuard::new(1);
        let _results = conn.query("SELECT * FROM users");
        // Connection automatically closed here
    }

    // Early return - still cleaned up
    {
        let conn = ConnectionGuard::new(2);
        if true {
            return;  // Drop called before return
        }
        let _ = conn;  // Never reached
    }
}
```

#### 3.2.3 Scope Guards

```rust
/// Execute code on scope exit
pub struct ScopeGuard<F: FnOnce()> {
    callback: Option<F>,
}

impl<F: FnOnce()> ScopeGuard<F> {
    pub fn new(callback: F) -> Self {
        Self {
            callback: Some(callback),
        }
    }

    /// Cancel the guard (skip callback)
    pub fn dismiss(mut self) {
        self.callback = None;
    }
}

impl<F: FnOnce()> Drop for ScopeGuard<F> {
    fn drop(&mut self) {
        if let Some(callback) = self.callback.take() {
            callback();
        }
    }
}

/// Usage
fn scope_guard_usage() {
    let mut value = 0;

    {
        let _guard = ScopeGuard::new(|| {
            println!("Cleanup: value = {}", value);
        });

        value = 42;
        // Guard triggers here
    }

    // Conditional cleanup
    let mut should_cleanup = true;
    {
        let guard = ScopeGuard::new(|| {
            println!("Conditional cleanup");
        });

        if !should_cleanup {
            guard.dismiss();  // Prevent cleanup
        }
    }
}
```

#### 3.2.4 Theorem RAII-SAFETY

**Theorem**: For any RAII guard G managing resource R, R is released exactly once when G is dropped, regardless of control flow.

**Proof**:

1. Rust guarantees Drop::drop is called when value goes out of scope
2. For panics, stack unwinding calls drop for all values on stack
3. Early returns still go through scope exit, triggering drop
4. Manually implemented Drop ensures resource release logic
5. Therefore, R is released exactly once ∎

---

### 3.3 View Types Pattern

View types provide zero-cost abstractions over data with different access patterns.

#### 3.3.1 Problem

```
PROBLEM VIEW-TYPES:
    Given: Large data structure
    Constraint: Different consumers need different "views"
    Constraint: Views must have zero runtime cost
    Constraint: Views must respect borrowing rules
```

#### 3.3.2 Solution Structure

```rust
/// Source data structure
pub struct DataFrame {
    columns: Vec<String>,
    data: Vec<Vec<f64>>,
}

impl DataFrame {
    pub fn new(columns: Vec<String>, data: Vec<Vec<f64>>) -> Self {
        Self { columns, data }
    }

    /// Create a row view
    pub fn row(&self, index: usize) -> Option<RowView> {
        self.data.get(index).map(|row| RowView {
            columns: &self.columns,
            data: row,
        })
    }

    /// Create a column view
    pub fn column(&self, name: &str) -> Option<ColumnView> {
        self.columns.iter()
            .position(|c| c == name)
            .map(|idx| ColumnView {
                name,
                data: self.data.iter().map(|row| &row[idx]).collect(),
            })
    }

    /// Create a slice view (rows [start, end))
    pub fn slice(&self, start: usize, end: usize) -> DataFrameView {
        DataFrameView {
            columns: &self.columns,
            data: &self.data[start..end.min(self.data.len())],
        }
    }
}

/// View of a single row
pub struct RowView<'a> {
    columns: &'a [String],
    data: &'a [f64],
}

impl<'a> RowView<'a> {
    pub fn get(&self, column: &str) -> Option<&f64> {
        self.columns.iter()
            .position(|c| c == column)
            .and_then(|idx| self.data.get(idx))
    }

    pub fn iter(&self) -> impl Iterator<Item = (&'a str, &f64)> {
        self.columns.iter()
            .map(|s| s.as_str())
            .zip(self.data.iter())
    }
}

/// View of a single column
pub struct ColumnView<'a> {
    name: &'a str,
    data: Vec<&'a f64>,
}

impl<'a> ColumnView<'a> {
    pub fn name(&self) -> &str {
        self.name
    }

    pub fn iter(&self) -> impl Iterator<Item = &f64> {
        self.data.iter().copied()
    }

    pub fn mean(&self) -> f64 {
        let sum: f64 = self.data.iter().copied().sum();
        sum / self.data.len() as f64
    }
}

/// View of a range of rows
pub struct DataFrameView<'a> {
    columns: &'a [String],
    data: &'a [Vec<f64>],
}

impl<'a> DataFrameView<'a> {
    pub fn row_count(&self) -> usize {
        self.data.len()
    }

    pub fn column_count(&self) -> usize {
        self.columns.len()
    }

    pub fn rows(&self) -> impl Iterator<Item = RowView> {
        self.data.iter().map(move |row| RowView {
            columns: self.columns,
            data: row,
        })
    }
}
```

#### 3.3.3 Theorem VIEW-ZERO-COST

**Theorem**: For view type V over data D, sizeof(V) ≤ sizeof(D) and V operations have no overhead compared to direct D access.

**Proof**:

1. Views contain only references (&T) or indices into D
2. References are pointer-sized regardless of data size
3. View methods inline to direct array/slice operations
4. No heap allocation or copying occurs
5. Therefore, views have zero runtime cost ∎

---

### 3.4 Adapter Pattern

```rust
/// Target interface
pub trait Target {
    fn request(&self) -> String;
}

/// Adaptee (incompatible interface)
pub struct Adaptee {
    value: String,
}

impl Adaptee {
    pub fn new(value: impl Into<String>) -> Self {
        Self { value: value.into() }
    }

    pub fn specific_request(&self) -> String {
        format!("Specific: {}", self.value)
    }
}

/// Adapter makes Adaptee compatible with Target
pub struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    pub fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}
```

---

### 3.5 Decorator Pattern

```rust
/// Component trait
pub trait TextNode {
    fn render(&self) -> String;
}

/// Concrete component
pub struct PlainText {
    text: String,
}

impl PlainText {
    pub fn new(text: impl Into<String>) -> Self {
        Self { text: text.into() }
    }
}

impl TextNode for PlainText {
    fn render(&self) -> String {
        self.text.clone()
    }
}

/// Base decorator
pub struct TextDecorator<T: TextNode> {
    inner: T,
}

impl<T: TextNode> TextDecorator<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }
}

impl<T: TextNode> TextNode for TextDecorator<T> {
    fn render(&self) -> String {
        self.inner.render()
    }
}

/// Bold decorator
pub struct Bold<T: TextNode>(TextDecorator<T>);

impl<T: TextNode> Bold<T> {
    pub fn new(inner: T) -> Self {
        Self(TextDecorator::new(inner))
    }
}

impl<T: TextNode> TextNode for Bold<T> {
    fn render(&self) -> String {
        format!("<b>{}</b>", self.0.render())
    }
}

/// Italic decorator
pub struct Italic<T: TextNode>(TextDecorator<T>);

impl<T: TextNode> Italic<T> {
    pub fn new(inner: T) -> Self {
        Self(TextDecorator::new(inner))
    }
}

impl<T: TextNode> TextNode for Italic<T> {
    fn render(&self) -> String {
        format!("<i>{}</i>", self.0.render())
    }
}

/// Usage: Bold<Italic<PlainText>>
fn decorator_usage() {
    let text = Bold::new(Italic::new(PlainText::new("Hello")));
    assert_eq!(text.render(), "<b><i>Hello</i></b>");
}
```

---

## 4. Behavioral Patterns

### 4.1 State Machine Pattern with Enums

#### 4.1.1 Problem

```
PROBLEM STATE-MACHINE:
    Given: Object with distinct behavioral states
    Constraint: Transitions must be valid
    Constraint: Invalid transitions must be prevented
    Constraint: State-specific data must be encapsulated
```

#### 4.1.2 Solution Structure

```rust
/// Events that trigger state transitions
#[derive(Debug, Clone)]
pub enum Event {
    Start,
    Pause,
    Resume,
    Stop,
    Reset,
}

/// States with encapsulated data
#[derive(Debug, Clone)]
pub enum State {
    Idle,
    Running { start_time: std::time::Instant },
    Paused { elapsed: Duration },
    Stopped { total_time: Duration },
}

impl State {
    /// Valid state transitions
    pub fn transition(self, event: Event) -> Result<Self, InvalidTransition> {
        match (self, event) {
            // Idle can transition to Running
            (State::Idle, Event::Start) => {
                Ok(State::Running { start_time: std::time::Instant::now() })
            }

            // Running can transition to Paused or Stopped
            (State::Running { start_time }, Event::Pause) => {
                let elapsed = start_time.elapsed();
                Ok(State::Paused { elapsed })
            }
            (State::Running { start_time }, Event::Stop) => {
                let total_time = start_time.elapsed();
                Ok(State::Stopped { total_time })
            }

            // Paused can transition to Running or Stopped
            (State::Paused { elapsed }, Event::Resume) => {
                Ok(State::Running {
                    start_time: std::time::Instant::now() - elapsed
                })
            }
            (State::Paused { elapsed }, Event::Stop) => {
                Ok(State::Stopped { total_time: elapsed })
            }

            // Stopped can transition to Idle (reset)
            (State::Stopped { .. }, Event::Reset) => {
                Ok(State::Idle)
            }

            // All other combinations are invalid
            (state, event) => Err(InvalidTransition {
                from: format!("{:?}", state),
                event: format!("{:?}", event)
            }),
        }
    }

    /// Get current state name
    pub fn name(&self) -> &'static str {
        match self {
            State::Idle => "Idle",
            State::Running { .. } => "Running",
            State::Paused { .. } => "Paused",
            State::Stopped { .. } => "Stopped",
        }
    }
}

#[derive(Debug)]
pub struct InvalidTransition {
    from: String,
    event: String,
}

impl std::fmt::Display for InvalidTransition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid transition from {} on {:?}", self.from, self.event)
    }
}

impl std::error::Error for InvalidTransition {}

/// State machine with context
pub struct StateMachine {
    state: State,
    history: Vec<State>,
}

impl StateMachine {
    pub fn new() -> Self {
        Self {
            state: State::Idle,
            history: vec![State::Idle],
        }
    }

    pub fn handle(&mut self, event: Event) -> Result<(), InvalidTransition> {
        let new_state = self.state.clone().transition(event)?;
        self.state = new_state.clone();
        self.history.push(new_state);
        Ok(())
    }

    pub fn current_state(&self) -> &State {
        &self.state
    }

    pub fn history(&self) -> &[State] {
        &self.history
    }
}
```

#### 4.1.3 State Transition Diagram

```
                    ┌─────────────┐
         ┌─────────│    Idle     │◀────────┐
         │         └─────────────┘         │
         │                │                │
         │           Start│                │
         │                ▼                │ Reset
         │         ┌─────────────┐         │
    Pause│    Stop │   Running   │─────────┤
         │◀────────│             │         │
         │         └─────────────┘         │
         │                │                │
         │           Pause│                │
         │                ▼                │
         │         ┌─────────────┐   Stop  │
         └────────▶│   Paused    │─────────┘
                   └─────────────┘
                          │
                     Resume│
                          ▼
                   ┌─────────────┐
              Stop │   Stopped   │
                   └─────────────┘
```

#### 4.1.4 Theorem STATE-MACHINE-SAFETY

**Theorem**: For a state machine with states S and transitions T ⊆ S × Event × S, attempting an undefined transition (s, e) ∉ T results in a compile-time or runtime error.

**Proof**:

1. Enum-based state machine defines all valid (state, event) pairs
2. match expression with exhaustive checking ensures all cases handled
3. Invalid combinations result in Err(InvalidTransition)
4. Alternatively, type-state pattern makes invalid transitions compile errors
5. Therefore, undefined transitions are caught ∎

---

### 4.2 Strategy Pattern

#### 4.2.1 Problem

```
PROBLEM STRATEGY:
    Given: Algorithm with interchangeable variants
    Constraint: Must select algorithm at runtime
    Constraint: Algorithm must be testable in isolation
    Constraint: Adding new algorithms must not modify existing code
```

#### 4.2.2 Solution Structure

```rust
/// Strategy trait
pub trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
    fn name(&self) -> &'static str;
}

/// Concrete strategy: QuickSort
pub struct QuickSort;

impl SortStrategy for QuickSort {
    fn sort(&self, data: &mut [i32]) {
        if data.len() <= 1 {
            return;
        }
        let pivot = partition(data);
        let (left, right) = data.split_at_mut(pivot);
        self.sort(left);
        self.sort(&mut right[1..]);
    }

    fn name(&self) -> &'static str {
        "QuickSort"
    }
}

fn partition(data: &mut [i32]) -> usize {
    let len = data.len();
    let pivot_index = len / 2;
    data.swap(pivot_index, len - 1);
    let mut i = 0;
    for j in 0..len - 1 {
        if data[j] <= data[len - 1] {
            data.swap(i, j);
            i += 1;
        }
    }
    data.swap(i, len - 1);
    i
}

/// Concrete strategy: MergeSort
pub struct MergeSort;

impl SortStrategy for MergeSort {
    fn sort(&self, data: &mut [i32]) {
        if data.len() <= 1 {
            return;
        }
        let mid = data.len() / 2;
        let mut left = data[..mid].to_vec();
        let mut right = data[mid..].to_vec();
        self.sort(&mut left);
        self.sort(&mut right);
        merge(&left, &right, data);
    }

    fn name(&self) -> &'static str {
        "MergeSort"
    }
}

fn merge(left: &[i32], right: &[i32], result: &mut [i32]) {
    let (mut i, mut j, mut k) = (0, 0, 0);
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result[k] = left[i];
            i += 1;
        } else {
            result[k] = right[j];
            j += 1;
        }
        k += 1;
    }
    while i < left.len() {
        result[k] = left[i];
        i += 1;
        k += 1;
    }
    while j < right.len() {
        result[k] = right[j];
        j += 1;
        k += 1;
    }
}

/// Concrete strategy: HeapSort
pub struct HeapSort;

impl SortStrategy for HeapSort {
    fn sort(&self, data: &mut [i32]) {
        let len = data.len();
        for i in (0..len / 2).rev() {
            heapify(data, len, i);
        }
        for i in (1..len).rev() {
            data.swap(0, i);
            heapify(data, i, 0);
        }
    }

    fn name(&self) -> &'static str {
        "HeapSort"
    }
}

fn heapify(data: &mut [i32], heap_size: usize, root: usize) {
    let mut largest = root;
    let left = 2 * root + 1;
    let right = 2 * root + 2;

    if left < heap_size && data[left] > data[largest] {
        largest = left;
    }
    if right < heap_size && data[right] > data[largest] {
        largest = right;
    }
    if largest != root {
        data.swap(root, largest);
        heapify(data, heap_size, largest);
    }
}

/// Context using a strategy
pub struct Sorter<'a> {
    strategy: &'a dyn SortStrategy,
}

impl<'a> Sorter<'a> {
    pub fn new(strategy: &'a dyn SortStrategy) -> Self {
        Self { strategy }
    }

    pub fn set_strategy(&mut self, strategy: &'a dyn SortStrategy) {
        self.strategy = strategy;
    }

    pub fn sort(&self, data: &mut [i32]) {
        println!("Sorting with {}", self.strategy.name());
        self.strategy.sort(data);
    }
}

/// Generic context (zero-cost abstraction)
pub struct GenericSorter<S: SortStrategy> {
    strategy: S,
}

impl<S: SortStrategy> GenericSorter<S> {
    pub fn new(strategy: S) -> Self {
        Self { strategy }
    }

    pub fn sort(&self, data: &mut [i32]) {
        self.strategy.sort(data);
    }
}
```

#### 4.2.3 Theorem STRATEGY-EXTENSIBILITY

**Theorem**: For a context C using strategy trait S, adding a new strategy implementation N requires no modifications to C or existing implementations.

**Proof**:

1. Strategy pattern uses trait-based polymorphism
2. Context depends only on trait interface, not implementations
3. New implementations only need to satisfy trait bounds
4. No recompilation of context needed (with dynamic dispatch)
5. Therefore, strategies are extensible without modification ∎

---

### 4.3 Command Pattern

```rust
use std::collections::VecDeque;

/// Command trait
pub trait Command {
    fn execute(&mut self);
    fn undo(&mut self);
    fn description(&self) -> &'static str;
}

/// Receiver
pub struct TextEditor {
    content: String,
    clipboard: String,
}

impl TextEditor {
    pub fn new() -> Self {
        Self {
            content: String::new(),
            clipboard: String::new(),
        }
    }

    pub fn insert(&mut self, text: &str, position: usize) {
        if position <= self.content.len() {
            self.content.insert_str(position, text);
        }
    }

    pub fn delete(&mut self, start: usize, end: usize) -> String {
        let deleted = self.content[start..end].to_string();
        self.content.replace_range(start..end, "");
        deleted
    }

    pub fn set_clipboard(&mut self, text: String) {
        self.clipboard = text;
    }

    pub fn clipboard(&self) -> &str {
        &self.clipboard
    }

    pub fn content(&self) -> &str {
        &self.content
    }
}

/// Concrete command: Insert
pub struct InsertCommand<'a> {
    editor: &'a mut TextEditor,
    text: String,
    position: usize,
}

impl<'a> InsertCommand<'a> {
    pub fn new(editor: &'a mut TextEditor, text: impl Into<String>, position: usize) -> Self {
        Self {
            editor,
            text: text.into(),
            position,
        }
    }
}

impl<'a> Command for InsertCommand<'a> {
    fn execute(&mut self) {
        self.editor.insert(&self.text, self.position);
    }

    fn undo(&mut self) {
        let len = self.text.len();
        self.editor.delete(self.position, self.position + len);
    }

    fn description(&self) -> &'static str {
        "Insert"
    }
}

/// Concrete command: Delete
pub struct DeleteCommand<'a> {
    editor: &'a mut TextEditor,
    start: usize,
    end: usize,
    deleted: Option<String>,
}

impl<'a> DeleteCommand<'a> {
    pub fn new(editor: &'a mut TextEditor, start: usize, end: usize) -> Self {
        Self {
            editor,
            start,
            end,
            deleted: None,
        }
    }
}

impl<'a> Command for DeleteCommand<'a> {
    fn execute(&mut self) {
        self.deleted = Some(self.editor.delete(self.start, self.end));
    }

    fn undo(&mut self) {
        if let Some(ref text) = self.deleted {
            self.editor.insert(text, self.start);
        }
    }

    fn description(&self) -> &'static str {
        "Delete"
    }
}

/// Command invoker with history
pub struct CommandHistory<'a> {
    history: VecDeque<Box<dyn Command + 'a>>,
    current: usize,
}

impl<'a> CommandHistory<'a> {
    pub fn new() -> Self {
        Self {
            history: VecDeque::new(),
            current: 0,
        }
    }

    pub fn execute(&mut self, mut command: Box<dyn Command + 'a>) {
        command.execute();

        // Remove any redo commands
        self.history.truncate(self.current);

        self.history.push_back(command);
        self.current += 1;
    }

    pub fn undo(&mut self) -> bool {
        if self.current > 0 {
            self.current -= 1;
            if let Some(cmd) = self.history.get_mut(self.current) {
                cmd.undo();
                return true;
            }
        }
        false
    }

    pub fn redo(&mut self) -> bool {
        if self.current < self.history.len() {
            if let Some(cmd) = self.history.get_mut(self.current) {
                cmd.execute();
                self.current += 1;
                return true;
            }
        }
        false
    }
}
```

---

### 4.4 Observer Pattern

```rust
use std::sync::{Arc, Weak};
use std::collections::HashMap;

/// Observer trait
pub trait Observer {
    fn update(&mut self, event: &str, data: &str);
}

/// Subject trait
pub trait Subject {
    fn attach(&mut self, id: &str, observer: Arc<std::sync::Mutex<dyn Observer + Send>>);
    fn detach(&mut self, id: &str);
    fn notify(&mut self, event: &str, data: &str);
}

/// Concrete subject
pub struct NewsAgency {
    observers: HashMap<String, Weak<std::sync::Mutex<dyn Observer + Send>>>,
}

impl NewsAgency {
    pub fn new() -> Self {
        Self {
            observers: HashMap::new(),
        }
    }

    pub fn publish(&mut self, headline: &str) {
        self.notify("news", headline);
    }
}

impl Subject for NewsAgency {
    fn attach(&mut self, id: &str, observer: Arc<std::sync::Mutex<dyn Observer + Send>>) {
        self.observers.insert(id.to_string(), Arc::downgrade(&observer));
    }

    fn detach(&mut self, id: &str) {
        self.observers.remove(id);
    }

    fn notify(&mut self, event: &str, data: &str) {
        let mut to_remove = Vec::new();

        for (id, weak) in &self.observers {
            if let Some(observer) = weak.upgrade() {
                if let Ok(mut obs) = observer.lock() {
                    obs.update(event, data);
                }
            } else {
                to_remove.push(id.clone());
            }
        }

        for id in to_remove {
            self.observers.remove(&id);
        }
    }
}

/// Concrete observer
pub struct NewsChannel {
    name: String,
    headlines: Vec<String>,
}

impl NewsChannel {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            headlines: Vec::new(),
        }
    }

    pub fn headlines(&self) -> &[String] {
        &self.headlines
    }
}

impl Observer for NewsChannel {
    fn update(&mut self, _event: &str, data: &str) {
        println!("{} received: {}", self.name, data);
        self.headlines.push(data.to_string());
    }
}
```

---

### 4.5 Visitor Pattern

```rust
/// Element trait
pub trait Element {
    fn accept(&self, visitor: &mut dyn Visitor);
}

/// Visitor trait
pub trait Visitor {
    fn visit_document(&mut self, doc: &Document);
    fn visit_paragraph(&mut self, para: &Paragraph);
    fn visit_text(&mut self, text: &Text);
}

/// Concrete elements
pub struct Document {
    pub children: Vec<Box<dyn Element>>,
}

impl Element for Document {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_document(self);
        for child in &self.children {
            child.accept(visitor);
        }
    }
}

pub struct Paragraph {
    pub children: Vec<Box<dyn Element>>,
}

impl Element for Paragraph {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_paragraph(self);
        for child in &self.children {
            child.accept(visitor);
        }
    }
}

pub struct Text {
    pub content: String,
}

impl Element for Text {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_text(self);
    }
}

/// Concrete visitor: HTML renderer
pub struct HtmlRenderer {
    output: String,
}

impl HtmlRenderer {
    pub fn new() -> Self {
        Self { output: String::new() }
    }

    pub fn result(self) -> String {
        self.output
    }
}

impl Visitor for HtmlRenderer {
    fn visit_document(&mut self, _doc: &Document) {
        self.output.push_str("<!DOCTYPE html><html><body>");
    }

    fn visit_paragraph(&mut self, _para: &Paragraph) {
        self.output.push_str("<p>");
    }

    fn visit_text(&mut self, text: &Text) {
        self.output.push_str(&html_escape(&text.content));
        self.output.push_str("</p>");
    }
}

fn html_escape(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// Concrete visitor: Word counter
pub struct WordCounter {
    count: usize,
}

impl WordCounter {
    pub fn new() -> Self {
        Self { count: 0 }
    }

    pub fn count(&self) -> usize {
        self.count
    }
}

impl Visitor for WordCounter {
    fn visit_document(&mut self, _doc: &Document) {}
    fn visit_paragraph(&mut self, _para: &Paragraph) {}

    fn visit_text(&mut self, text: &Text) {
        self.count += text.content.split_whitespace().count();
    }
}
```

---

## 5. Rust-Specific Patterns

### 5.1 Borrowed vs Owned

#### 5.1.1 Decision Framework

```
┌─────────────────────────────────────────────────────────────┐
│               Borrowed vs Owned Decision Tree               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Does the data need to outlive the current scope?           │
│         │                                                   │
│    Yes ─┴─▶ Use Owned (T, Box<T>, Arc<T>, Vec<T>)           │
│         │                                                   │
│    No ──┬─▶ Can you guarantee unique access?                │
│              │                                              │
│         Yes ─┴─▶ Use &mut T (mutable borrow)                │
│              │                                              │
│         No ────▶ Use &T (shared borrow)                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 5.1.2 Pattern Implementation

```rust
/// Owned data - caller provides data, function takes ownership
pub fn process_owned(data: Vec<u8>) -> Vec<u8> {
    // Owns data, can modify freely
    data.into_iter().map(|b| b.wrapping_add(1)).collect()
}

/// Borrowed data - caller retains ownership, function borrows
pub fn process_borrowed(data: &[u8]) -> Vec<u8> {
    // Borrows data, creates new owned result
    data.iter().map(|b| b.wrapping_add(1)).collect()
}

/// Mutable borrow - caller retains ownership, function can modify
pub fn process_mut_borrowed(data: &mut [u8]) {
    // Mutably borrows, modifies in place
    for byte in data.iter_mut() {
        *byte = byte.wrapping_add(1);
    }
}

/// Generic approach accepting any form
pub fn process_generic<D: AsRef<[u8]>>(data: D) -> Vec<u8> {
    data.as_ref().iter().map(|b| b.wrapping_add(1)).collect()
}

/// Cow approach - owned or borrowed
use std::borrow::Cow;

pub fn process_cow(data: Cow<[u8]>) -> Cow<[u8]> {
    match data {
        Cow::Borrowed(slice) => {
            if slice.iter().all(|&b| b != 0xFF) {
                // No modification needed
                Cow::Borrowed(slice)
            } else {
                // Need to modify
                Cow::Owned(slice.iter().map(|b| b.wrapping_add(1)).collect())
            }
        }
        Cow::Owned(mut vec) => {
            for byte in &mut vec {
                *byte = byte.wrapping_add(1);
            }
            Cow::Owned(vec)
        }
    }
}
```

#### 5.1.3 Performance Comparison

```rust
/// Benchmark comparison (conceptual)
///
/// Scenario: Process 1MB of data
///
/// | Pattern        | Stack | Heap  | Copies | Time   |
/// |----------------|-------|-------|--------|--------|
/// | Owned          | 24B   | 1MB   | 1      | 1.0x   |
/// | Borrowed       | 16B   | 0     | 1      | 1.0x   |
/// | Mut Borrowed   | 16B   | 0     | 0      | 0.9x   |
/// | Cow (no mod)   | 32B   | 0     | 0      | 0.95x  |
/// | Cow (modified) | 32B   | 1MB   | 1      | 1.1x   |
```

---

### 5.2 Clone-on-Write (Cow<T>)

#### 5.2.1 Problem

```
PROBLEM COW:
    Given: Data that may or may not need modification
    Constraint: Avoid copy if not modified
    Constraint: Provide uniform interface
    Constraint: Zero-cost when not cloning
```

#### 5.2.2 Solution Structure

```rust
use std::borrow::Cow;

/// Configuration with defaults
#[derive(Clone)]
pub struct Config<'a> {
    /// Name - always required, borrow if possible
    name: Cow<'a, str>,

    /// Timeout - has default, store owned
    timeout: Duration,

    /// Headers - optional, use Cow for flexibility
    headers: Cow<'a, [(&'a str, &'a str)]>,
}

impl<'a> Config<'a> {
    /// Create with borrowed data (zero allocation)
    pub fn borrowed(name: &'a str) -> Self {
        Self {
            name: Cow::Borrowed(name),
            timeout: Duration::from_secs(30),
            headers: Cow::Borrowed(&[]),
        }
    }

    /// Create with owned data
    pub fn owned(name: impl Into<String>) -> Self {
        Self {
            name: Cow::Owned(name.into()),
            timeout: Duration::from_secs(30),
            headers: Cow::Owned(vec![]),
        }
    }

    /// Set name - triggers clone if borrowed
    pub fn set_name(&mut self, name: impl Into<String>) {
        self.name = Cow::Owned(name.into());
    }

    /// Get name - works for both cases
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Ensure ownership (for passing to other threads)
    pub fn into_owned(self) -> Config<'static> {
        Config {
            name: Cow::Owned(self.name.into_owned()),
            timeout: self.timeout,
            headers: Cow::Owned(self.headers.iter()
                .map(|&(k, v)| (k, v))
                .collect()),
        }
    }
}
```

#### 5.2.3 Theorem COW-LAZINESS

**Theorem**: For Cow<T> value c, cloning occurs if and only if c is Borrowed and mutation is requested.

**Proof**:

1. Cow::Borrowed holds reference, no heap allocation
2. to_mut() checks variant: if Borrowed, clones to Owned
3. If already Owned, returns mutable reference directly
4. No other operations trigger cloning
5. Therefore, cloning is lazy and conditional ∎

---

### 5.3 Phantom Types

#### 5.3.1 Problem

```
PROBLEM PHANTOM-TYPES:
    Given: Type that needs compile-time state tracking
    Constraint: State must not affect runtime representation
    Constraint: Invalid state transitions must be compile errors
```

#### 5.3.2 Solution Structure

```rust
use std::marker::PhantomData;

/// State markers
pub struct Unverified;
pub struct Verified;
pub struct Active;
pub struct Inactive;

/// Token with phantom type state
pub struct Token<State> {
    value: String,
    expires_at: u64,
    _state: PhantomData<State>,
}

/// Token can only be created in Unverified state
impl Token<Unverified> {
    pub fn new(value: impl Into<String>, expires_at: u64) -> Self {
        Self {
            value: value.into(),
            expires_at,
            _state: PhantomData,
        }
    }

    /// Verify the token - state transition
    pub fn verify(self, current_time: u64) -> Result<Token<Verified>, TokenError> {
        if self.expires_at > current_time {
            Ok(Token {
                value: self.value,
                expires_at: self.expires_at,
                _state: PhantomData,
            })
        } else {
            Err(TokenError::Expired)
        }
    }
}

/// Verified token can be activated
impl Token<Verified> {
    pub fn activate(self) -> Token<Active> {
        Token {
            value: self.value,
            expires_at: self.expires_at,
            _state: PhantomData,
        }
    }

    pub fn value(&self) -> &str {
        &self.value
    }
}

/// Active token can be used for operations
impl Token<Active> {
    pub fn authorize(&self, resource: &str) -> Authorization {
        Authorization {
            token: &self.value,
            resource: resource.to_string(),
        }
    }

    pub fn deactivate(self) -> Token<Inactive> {
        Token {
            value: self.value,
            expires_at: self.expires_at,
            _state: PhantomData,
        }
    }
}

/// Inactive token can be reactivated or dropped
impl Token<Inactive> {
    pub fn reactivate(self) -> Token<Active> {
        Token {
            value: self.value,
            expires_at: self.expires_at,
            _state: PhantomData,
        }
    }
}

#[derive(Debug)]
pub enum TokenError {
    Expired,
    Invalid,
}

pub struct Authorization<'a> {
    token: &'a str,
    resource: String,
}

/// Usage demonstrates compile-time state safety
fn phantom_usage() {
    // Create unverified token
    let token = Token::new("abc123", 1000);

    // Cannot use unverified token
    // token.authorize("resource"); // ERROR: no method found

    // Verify to transition state
    let verified = token.verify(500).unwrap();

    // Cannot use verified token directly
    // verified.authorize("resource"); // ERROR: no method found

    // Activate to use
    let active = verified.activate();
    let _auth = active.authorize("resource");

    // Can deactivate and reactivate
    let inactive = active.deactivate();
    let _active_again = inactive.reactivate();
}
```

#### 5.3.3 Theorem PHANTOM-ZERO-SIZE

**Theorem**: For type T<S> containing PhantomData<S>, sizeof(T<S>) is independent of sizeof(S).

**Proof**:

1. PhantomData<S> is a zero-sized type (ZST)
2. ZSTs contribute 0 bytes to struct size
3. S is never instantiated, only used as type parameter
4. Therefore, sizeof(T<S>) = sizeof(fields excluding PhantomData) ∎

---

### 5.4 Deref/DerefMut for Smart Pointers

```rust
use std::ops::{Deref, DerefMut};

/// Custom smart pointer with reference counting
pub struct MyRc<T> {
    ptr: *mut T,
    ref_count: *mut usize,
}

impl<T> MyRc<T> {
    pub fn new(value: T) -> Self {
        let ptr = Box::into_raw(Box::new(value));
        let ref_count = Box::into_raw(Box::new(1usize));
        Self { ptr, ref_count }
    }

    fn ref_count(&self) -> usize {
        unsafe { *self.ref_count }
    }
}

impl<T> Deref for MyRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

impl<T> Clone for MyRc<T> {
    fn clone(&self) -> Self {
        unsafe {
            *self.ref_count += 1;
        }
        Self {
            ptr: self.ptr,
            ref_count: self.ref_count,
        }
    }
}

impl<T> Drop for MyRc<T> {
    fn drop(&mut self) {
        unsafe {
            *self.ref_count -= 1;
            if *self.ref_count == 0 {
                let _ = Box::from_raw(self.ptr);
                let _ = Box::from_raw(self.ref_count);
            }
        }
    }
}
```

---

## 6. Counter-Examples (Anti-Pattern Demonstrations)

### 6.1 Builder Missing Field

```rust
/// ❌ INCORRECT: Builder allows incomplete construction
pub struct BadBuilder {
    required_field: Option<String>,
    optional_field: Option<i32>,
}

impl BadBuilder {
    pub fn new() -> Self {
        Self {
            required_field: None,
            optional_field: None,
        }
    }

    // Missing setter for required_field

    pub fn optional_field(mut self, value: i32) -> Self {
        self.optional_field = Some(value);
        self
    }

    /// Returns Result but doesn't check required fields
    pub fn build(self) -> Result<BadProduct, String> {
        // ❌ No validation of required_field
        Ok(BadProduct {
            required_field: self.required_field.unwrap_or_default(), // Silent default!
            optional_field: self.optional_field,
        })
    }
}

pub struct BadProduct {
    required_field: String,
    optional_field: Option<i32>,
}

/// ✅ CORRECT: Builder with mandatory field enforcement
pub struct GoodBuilder {
    required_field: Option<String>,
    optional_field: Option<i32>,
}

impl GoodBuilder {
    pub fn new() -> Self {
        Self {
            required_field: None,
            optional_field: None,
        }
    }

    pub fn required_field(mut self, value: impl Into<String>) -> Self {
        self.required_field = Some(value.into());
        self
    }

    pub fn build(self) -> Result<GoodProduct, BuildError> {
        let required_field = self.required_field
            .ok_or(BuildError::MissingField("required_field"))?;

        Ok(GoodProduct {
            required_field,
            optional_field: self.optional_field,
        })
    }
}

#[derive(Debug)]
pub enum BuildError {
    MissingField(&'static str),
}
```

**Issue**: BadBuilder silently uses default value for missing required field, leading to subtle bugs.

---

### 6.2 Type State Bypass

```rust
/// ❌ INCORRECT: Type state can be bypassed via unsafe
pub struct BadTypeState<State> {
    data: String,
    _marker: PhantomData<State>,
}

pub struct Uninitialized;
pub struct Initialized;

impl BadTypeState<Uninitialized> {
    pub fn new() -> Self {
        Self {
            data: String::new(),
            _marker: PhantomData,
        }
    }
}

impl BadTypeState<Initialized> {
    /// Assume this should only be called on initialized data
    pub fn dangerous_operation(&self) {
        println!("Operating on: {}", self.data);
    }
}

/// ❌ UNSAFE: Can bypass type state
fn bypass_type_state() {
    let uninitialized: BadTypeState<Uninitialized> = BadTypeState::new();

    // Transmute to bypass state checking
    let fake_initialized: BadTypeState<Initialized> = unsafe {
        std::mem::transmute(uninitialized)
    };

    // Calls dangerous_operation on uninitialized data
    fake_initialized.dangerous_operation(); // Undefined behavior risk!
}

/// ✅ CORRECT: Type state with proper encapsulation
pub struct GoodTypeState<State> {
    data: String,
    _marker: PhantomData<State>,
}

impl GoodTypeState<Uninitialized> {
    pub fn new() -> Self {
        Self {
            data: String::new(),
            _marker: PhantomData,
        }
    }

    pub fn initialize(self, data: impl Into<String>) -> GoodTypeState<Initialized> {
        GoodTypeState {
            data: data.into(),
            _marker: PhantomData,
        }
    }
}

impl GoodTypeState<Initialized> {
    pub fn dangerous_operation(&self) {
        println!("Operating on: {}", self.data);
    }
}
```

**Issue**: Type state can be bypassed using unsafe transmute, breaking safety guarantees.

---

### 6.3 RAII Guard Misuse

```rust
use std::sync::Mutex;

/// ❌ INCORRECT: RAII guard stored and used after scope
fn raii_guard_misuse() {
    let data = Mutex::new(vec![1, 2, 3]);

    let guard; // ❌ Declared outside scope

    {
        guard = data.lock().unwrap(); // Lock acquired
        guard.push(4);
    } // Lock should be released here

    // ❌ ERROR: guard used after scope would be a compile error
    // But storing it incorrectly can lead to deadlocks

    // Actually in Rust this is prevented, but pattern shows intent
}

/// ❌ INCORRECT: MutexGuard held across await point
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

async fn bad_async_mutex() {
    let data = Mutex::new(0);

    let guard = data.lock().unwrap(); // ❌ Held across await

    some_async_op().await; // ❌ Deadlock risk! Guard not Send

    // guard dropped here
}

async fn some_async_op() {}

/// ✅ CORRECT: Scoped mutex usage
fn good_raii_usage() {
    let data = Mutex::new(vec![1, 2, 3]);

    {
        let mut guard = data.lock().unwrap();
        guard.push(4);
    } // Guard dropped, lock released

    // Can acquire lock again
    let guard = data.lock().unwrap();
    println!("{:?}", *guard);
}

/// ✅ CORRECT: Async-aware locking
use std::sync::Arc;
use tokio::sync::Mutex as AsyncMutex; // For async contexts

async fn good_async_mutex() {
    let data = Arc::new(AsyncMutex::new(0));

    {
        let mut guard = data.lock().await;
        *guard += 1;
    } // Guard dropped

    some_async_op().await; // No deadlock risk
}
```

**Issue**: Holding guards across scope boundaries or await points can cause deadlocks.

---

### 6.4 Mutable Singleton

```rust
use std::sync::Mutex;
use once_cell::sync::Lazy;

/// ❌ INCORRECT: Global mutable state without synchronization
static mut BAD_GLOBAL: Vec<i32> = vec![];

fn bad_global_access() {
    unsafe {
        BAD_GLOBAL.push(1); // ❌ Data race in multi-threaded context
    }
}

/// ❌ INCORRECT: Deadlock-prone nested locking
static GLOBAL_MUTEX: Lazy<Mutex<Vec<i32>>> = Lazy::new(|| {
    Mutex::new(vec![])
});

fn nested_locking_deadlock() {
    let guard1 = GLOBAL_MUTEX.lock().unwrap();

    // ❌ If this function is called recursively, DEADLOCK
    another_function_that_locks();

    drop(guard1);
}

fn another_function_that_locks() {
    let _guard2 = GLOBAL_MUTEX.lock().unwrap(); // DEADLOCK!
}

/// ✅ CORRECT: Thread-safe global with proper encapsulation
static GOOD_GLOBAL: Lazy<Mutex<Vec<i32>>> = Lazy::new(|| {
    Mutex::new(vec![])
});

pub fn global_push(value: i32) {
    let mut guard = GOOD_GLOBAL.lock().unwrap();
    guard.push(value);
} // Guard dropped here

/// ✅ CORRECT: Avoid nested locking
pub fn safe_global_operation() {
    // Perform all work in single lock scope
    let result = {
        let guard = GOOD_GLOBAL.lock().unwrap();
        guard.len()
    }; // Lock released

    // Do work outside lock
    println!("Length: {}", result);

    // Can acquire lock again if needed
    global_push(42);
}
```

**Issue**: Global mutable state creates data races and deadlock risks.

---

### 6.5 Strategy with State

```rust
/// ❌ INCORRECT: Strategy with internal mutable state
pub trait BadStrategy {
    fn execute(&mut self, data: &mut [i32]);
}

pub struct StatefulStrategy {
    call_count: usize, // Mutable state
}

impl BadStrategy for StatefulStrategy {
    fn execute(&mut self, data: &mut [i32]) {
        self.call_count += 1; // ❌ Mutation requires &mut self
        data.sort();
    }
}

/// ❌ Problem: Can't use with multiple contexts
pub struct BadContext<'a> {
    strategy: &'a mut dyn BadStrategy,
}

impl<'a> BadContext<'a> {
    pub fn new(strategy: &'a mut dyn BadStrategy) -> Self {
        Self { strategy }
    }

    pub fn process(&mut self, data: &mut [i32]) {
        self.strategy.execute(data);
    }
}

fn strategy_usage_problem() {
    let mut strategy = StatefulStrategy { call_count: 0 };

    let mut ctx1 = BadContext::new(&mut strategy);
    // ❌ Can't create ctx2 because strategy already borrowed
    // let mut ctx2 = BadContext::new(&mut strategy);
}

/// ✅ CORRECT: Stateless strategy with external state
pub trait GoodStrategy {
    fn execute(&self, data: &mut [i32], state: &mut StrategyState);
}

pub struct StrategyState {
    call_count: usize,
}

pub struct StatelessStrategy;

impl GoodStrategy for StatelessStrategy {
    fn execute(&self, data: &mut [i32], state: &mut StrategyState) {
        state.call_count += 1;
        data.sort();
    }
}

/// ✅ CORRECT: Strategy with interior mutability for shared state
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct ThreadSafeStrategy {
    call_count: AtomicUsize,
}

impl ThreadSafeStrategy {
    pub fn new() -> Self {
        Self {
            call_count: AtomicUsize::new(0),
        }
    }

    pub fn call_count(&self) -> usize {
        self.call_count.load(Ordering::Relaxed)
    }
}

impl GoodStrategy for ThreadSafeStrategy {
    fn execute(&self, data: &mut [i32], _state: &mut StrategyState) {
        self.call_count.fetch_add(1, Ordering::Relaxed);
        data.sort();
    }
}
```

**Issue**: Mutable state in strategies limits composability and sharing.

---

### 6.6 Observer Memory Leak

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

/// ❌ INCORRECT: Strong references in observer pattern
pub struct BadSubject {
    observers: Vec<Arc<Mutex<dyn Observer + Send>>>, // Strong refs
}

impl BadSubject {
    pub fn new() -> Self {
        Self { observers: vec![] }
    }

    pub fn attach(&mut self, observer: Arc<Mutex<dyn Observer + Send>>) {
        self.observers.push(observer);
    }

    pub fn notify(&self) {
        for observer in &self.observers {
            if let Ok(mut obs) = observer.lock() {
                obs.update("event");
            }
        }
    }
}

/// ❌ MEMORY LEAK: Circular reference
pub struct BadObserver {
    subject: Option<Arc<Mutex<BadSubject>>>, // Reference to subject
    data: String,
}

impl Observer for BadObserver {
    fn update(&mut self, event: &str) {
        // May reference subject, creating cycle
        println!("{} received {}", self.data, event);
    }
}

fn circular_reference_leak() {
    let subject = Arc::new(Mutex::new(BadSubject::new()));
    let observer = Arc::new(Mutex::new(BadObserver {
        subject: Some(Arc::clone(&subject)),
        data: "Observer".to_string(),
    }));

    subject.lock().unwrap().attach(Arc::clone(&observer));

    // ❌ Both Arcs have count 2, never dropped
    // subject -> observer -> subject cycle
}

/// ✅ CORRECT: Use Weak references
use std::sync::Weak;

pub struct GoodSubject {
    observers: Vec<Weak<Mutex<dyn Observer + Send>>>,
}

impl GoodSubject {
    pub fn new() -> Self {
        Self { observers: vec![] }
    }

    pub fn attach(&mut self, observer: Arc<Mutex<dyn Observer + Send>>) {
        self.observers.push(Arc::downgrade(&observer));
    }

    pub fn notify(&mut self) {
        self.observers.retain(|weak| {
            if let Some(observer) = weak.upgrade() {
                if let Ok(mut obs) = observer.lock() {
                    obs.update("event");
                }
                true
            } else {
                false // Remove dead references
            }
        });
    }
}
```

**Issue**: Strong references between subject and observer create circular references and memory leaks.

---

### 6.7 Command Pattern Ownership

```rust
/// ❌ INCORRECT: Command takes ownership of receiver
pub struct BadCommand {
    receiver: DatabaseConnection, // Owned
    operation: String,
}

impl BadCommand {
    pub fn new(receiver: DatabaseConnection, operation: impl Into<String>) -> Self {
        Self {
            receiver,
            operation: operation.into(),
        }
    }

    pub fn execute(&mut self) {
        // Uses receiver
        println!("Executing {} on connection {:?}", self.operation, self.receiver);
    }
}

fn command_ownership_problem() {
    let conn = DatabaseConnection::new(1);

    let cmd = BadCommand::new(conn, "SELECT");
    // conn is moved, can't use again

    // ❌ Can't create another command with same connection
    // let cmd2 = BadCommand::new(conn, "INSERT"); // ERROR: conn moved
}

/// ✅ CORRECT: Command borrows receiver or uses reference counting
pub struct GoodCommand<'a> {
    receiver: &'a mut DatabaseConnection,
    operation: String,
}

impl<'a> GoodCommand<'a> {
    pub fn new(receiver: &'a mut DatabaseConnection, operation: impl Into<String>) -> Self {
        Self {
            receiver,
            operation: operation.into(),
        }
    }

    pub fn execute(&mut self) {
        println!("Executing {}", self.operation);
    }
}

/// ✅ CORRECT: Command with shared ownership
use std::sync::Arc;
use std::sync::Mutex;

pub struct SharedCommand {
    receiver: Arc<Mutex<DatabaseConnection>>,
    operation: String,
}

impl SharedCommand {
    pub fn new(receiver: Arc<Mutex<DatabaseConnection>>, operation: impl Into<String>) -> Self {
        Self {
            receiver,
            operation: operation.into(),
        }
    }

    pub fn execute(&self) {
        let mut conn = self.receiver.lock().unwrap();
        println!("Executing {}", self.operation);
    }
}
```

**Issue**: Commands taking ownership prevent reuse of shared resources.

---

### 6.8 Factory Returning References

```rust
/// ❌ INCORRECT: Factory returns reference to local variable
pub struct Factory;

impl Factory {
    /// ❌ DANGEROUS: Returns reference to stack data
    pub fn create_bad<'a>(&self) -> &'a Product {
        let product = Product::new(); // Local variable
        &product // ❌ Returns reference to data that will be dropped
    }
}

pub struct Product {
    value: i32,
}

impl Product {
    pub fn new() -> Self {
        Self { value: 42 }
    }
}

/// ✅ CORRECT: Factory returns owned value
impl Factory {
    pub fn create_good(&self) -> Product {
        Product::new() // Returns owned value
    }
}

/// ✅ CORRECT: Factory with object pool for references
use std::collections::HashMap;
use std::sync::Mutex;

pub struct PooledFactory {
    pool: Mutex<HashMap<u64, Box<Product>>>,
    next_id: Mutex<u64>,
}

impl PooledFactory {
    pub fn new() -> Self {
        Self {
            pool: Mutex::new(HashMap::new()),
            next_id: Mutex::new(0),
        }
    }

    pub fn create_pooled(&self) -> ProductHandle {
        let id = {
            let mut next = self.next_id.lock().unwrap();
            let id = *next;
            *next += 1;
            id
        };

        let mut pool = self.pool.lock().unwrap();
        pool.insert(id, Box::new(Product::new()));

        ProductHandle {
            factory: self,
            id,
        }
    }
}

pub struct ProductHandle<'a> {
    factory: &'a PooledFactory,
    id: u64,
}

impl<'a> ProductHandle<'a> {
    pub fn get(&self) -> Option<&Product> {
        // Returns reference from pool
        let pool = self.factory.pool.lock().unwrap();
        // Note: In practice need unsafe or better abstraction
        None
    }
}
```

**Issue**: Returning references to local data creates dangling references.

---

### 6.9 Adapter Lifetime Issue

```rust
/// ❌ INCORRECT: Adapter stores reference without lifetime
pub struct BadAdapter {
    adaptee: &Adaptee, // ❌ Missing lifetime
}

/// ❌ INCORRECT: Adapter lifetime shorter than adaptee
pub struct ShortLivedAdapter<'a> {
    adaptee: &'a Adaptee,
}

pub struct LongLivedContext {
    adapter: ShortLivedAdapter<'static>, // ❌ Can't satisfy
}

/// ✅ CORRECT: Proper lifetime annotation
pub struct GoodAdapter<'a> {
    adaptee: &'a Adaptee,
}

impl<'a> GoodAdapter<'a> {
    pub fn new(adaptee: &'a Adaptee) -> Self {
        Self { adaptee }
    }
}

impl<'a> Target for GoodAdapter<'a> {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}

/// ✅ CORRECT: Owned adapter for independent lifetimes
pub struct OwnedAdapter {
    adaptee: Adaptee,
}

impl OwnedAdapter {
    pub fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

impl Target for OwnedAdapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}
```

**Issue**: Incorrect lifetime annotations lead to borrow checker errors or use-after-free.

---

### 6.10 Decorator Recursion

```rust
/// ❌ INCORRECT: Decorator with potential infinite recursion
pub trait Component {
    fn operation(&self) -> String;
}

pub struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "Concrete".to_string()
    }
}

pub struct BadDecorator<T: Component> {
    inner: T,
}

impl<T: Component> Component for BadDecorator<T> {
    fn operation(&self) -> String {
        // ❌ Potential infinite recursion if inner is also BadDecorator
        format!("Decorator({})", self.inner.operation())
    }
}

/// ❌ STACK OVERFLOW: Recursive composition
fn decorator_stack_overflow() {
    let component = ConcreteComponent;
    let d1 = BadDecorator { inner: component };
    let d2 = BadDecorator { inner: d1 };
    let d3 = BadDecorator { inner: d2 };
    // ... many more layers
    // operation() recurses through each layer
}

/// ✅ CORRECT: Limit decorator depth or use iterative approach
pub struct SafeDecorator<T: Component> {
    inner: T,
    depth: usize,
}

impl<T: Component> SafeDecorator<T> {
    const MAX_DEPTH: usize = 100;

    pub fn new(inner: T) -> Self {
        Self { inner, depth: 0 }
    }

    fn with_depth(inner: T, depth: usize) -> Self {
        Self { inner, depth }
    }
}

impl<T: Component> Component for SafeDecorator<T> {
    fn operation(&self) -> String {
        if self.depth >= Self::MAX_DEPTH {
            return "[Max depth reached]".to_string();
        }
        format!("Decorator({})", self.inner.operation())
    }
}
```

**Issue**: Deep decorator chains can cause stack overflow.

---

### 6.11 Iterator Invalidation

```rust
/// ❌ INCORRECT: Modifying collection while iterating
fn iterator_invalidation() {
    let mut data = vec![1, 2, 3, 4, 5];

    // ❌ In languages without borrow checker, this causes issues
    // In Rust, this is prevented at compile time

    // But we can demonstrate the conceptual problem:
    for i in 0..data.len() {
        if data[i] % 2 == 0 {
            // In C++: data.erase(data.begin() + i); // INVALIDATES ITERATORS
            data.remove(i); // ❌ Shifts elements, skips next element
        }
    }
}

/// ✅ CORRECT: Retain for filtered removal
fn correct_removal_retain() {
    let mut data = vec![1, 2, 3, 4, 5];
    data.retain(|&x| x % 2 != 0);
    // Result: [1, 3, 5]
}

/// ✅ CORRECT: Iterate and collect indices, then remove
fn correct_removal_indices() {
    let mut data = vec![1, 2, 3, 4, 5];

    let to_remove: Vec<usize> = data.iter()
        .enumerate()
        .filter(|(_, &x)| x % 2 == 0)
        .map(|(i, _)| i)
        .collect();

    // Remove from end to avoid index shifting
    for &i in to_remove.iter().rev() {
        data.remove(i);
    }
}

/// ✅ CORRECT: Use drain_filter (unstable) or partition
fn correct_partition() {
    let data = vec![1, 2, 3, 4, 5];
    let (evens, odds): (Vec<_>, Vec<_>) = data.into_iter()
        .partition(|&x| x % 2 == 0);
    // odds: [1, 3, 5]
}
```

**Issue**: Modifying collections during iteration leads to skipped elements or crashes.

---

### 6.12 Visitor with Mutability

```rust
/// ❌ INCORRECT: Visitor tries to mutate during traversal
pub trait BadVisitor {
    fn visit_element(&mut self, element: &mut dyn Element);
}

pub trait Element {
    fn accept(&self, visitor: &mut dyn BadVisitor);
    fn children(&self) -> &[Box<dyn Element>];
}

/// ❌ PROBLEM: Can't borrow mutably multiple times
struct MutatingVisitor;

impl BadVisitor for MutatingVisitor {
    fn visit_element(&mut self, element: &mut dyn Element) {
        // Modify element
        // Then try to visit children
        for child in element.children() {
            // ❌ Can't get mutable reference to child
            // while element is borrowed
            // child.accept(self);
        }
    }
}

/// ✅ CORRECT: Two-phase visit (immutable scan, mutable update)
pub trait Visitor {
    fn visit(&self, element: &dyn Element) -> ElementDelta;
}

pub struct ElementDelta {
    changes: Vec<Change>,
}

pub enum Change {
    SetProperty(String, String),
    RemoveChild(usize),
}

/// Apply changes after traversal
fn apply_changes(element: &mut dyn Element, delta: ElementDelta) {
    for change in delta.changes {
        match change {
            Change::SetProperty(k, v) => element.set_property(&k, &v),
            Change::RemoveChild(i) => element.remove_child(i),
        }
    }
}
```

**Issue**: Mutable visitor pattern conflicts with Rust's aliasing rules.

---

### 6.13 Chain of Responsibility Leak

```rust
/// ❌ INCORRECT: Handlers form linked list without cleanup
pub struct Handler {
    next: Option<Box<Handler>>, // Recursive type
    handler: Box<dyn Fn(&Request) -> Response>,
}

impl Handler {
    pub fn new(handler: impl Fn(&Request) -> Response + 'static) -> Self {
        Self {
            next: None,
            handler: Box::new(handler),
        }
    }

    pub fn set_next(&mut self, next: Handler) {
        self.next = Some(Box::new(next));
    }

    pub fn handle(&self, request: &Request) -> Response {
        let response = (self.handler)(request);
        if !response.success && self.next.is_some() {
            return self.next.as_ref().unwrap().handle(request);
        }
        response
    }
}

/// ❌ MEMORY LEAK: Circular chain
fn circular_chain_leak() {
    let mut h1 = Handler::new(|_| Response { success: false });
    let mut h2 = Handler::new(|_| Response { success: false });

    h1.set_next(h2);
    // h2.set_next(h1); // ❌ Can't do this with owned Box

    // But with Rc/RefCell, cycles are possible:
}

use std::rc::Rc;
use std::cell::RefCell;

pub struct RcHandler {
    next: RefCell<Option<Rc<RcHandler>>>,
    handler: Box<dyn Fn(&Request) -> Response>,
}

impl RcHandler {
    pub fn set_next(&self, next: Rc<RcHandler>) {
        *self.next.borrow_mut() = Some(next);
    }
}

fn rc_circular_chain() {
    let h1 = Rc::new(RcHandler {
        next: RefCell::new(None),
        handler: Box::new(|_| Response { success: false }),
    });

    let h2 = Rc::new(RcHandler {
        next: RefCell::new(None),
        handler: Box::new(|_| Response { success: false }),
    });

    h1.set_next(Rc::clone(&h2));
    h2.set_next(Rc::clone(&h1)); // ❌ CYCLE! Memory leak
}

/// ✅ CORRECT: Use Weak references
use std::rc::Weak;

pub struct SafeHandler {
    next: RefCell<Option<Weak<SafeHandler>>>,
    handler: Box<dyn Fn(&Request) -> Response>,
}

impl SafeHandler {
    pub fn set_next(&self, next: Rc<SafeHandler>) {
        *self.next.borrow_mut() = Some(Rc::downgrade(&next));
    }

    pub fn handle(&self, request: &Request) -> Response {
        let response = (self.handler)(request);
        if !response.success {
            if let Some(next) = self.next.borrow().as_ref() {
                if let Some(handler) = next.upgrade() {
                    return handler.handle(request);
                }
            }
        }
        response
    }
}

pub struct Request;
pub struct Response {
    success: bool,
}
```

**Issue**: Chain of responsibility with strong references creates circular dependencies.

---

### 6.14 Mediator Circular Reference

```rust
use std::sync::{Arc, Mutex};

/// ❌ INCORRECT: Mediator and colleagues hold strong references
pub struct BadMediator {
    colleagues: Vec<Arc<Mutex<dyn Colleague>>>,
}

impl BadMediator {
    pub fn new() -> Self {
        Self { colleagues: vec![] }
    }

    pub fn register(&mut self, colleague: Arc<Mutex<dyn Colleague>>) {
        self.colleagues.push(colleague);
    }
}

pub trait Colleague {
    fn set_mediator(&mut self, mediator: Arc<Mutex<BadMediator>>);
    fn notify(&mut self, event: &str);
}

pub struct ConcreteColleague {
    mediator: Option<Arc<Mutex<BadMediator>>>,
    name: String,
}

impl Colleague for ConcreteColleague {
    fn set_mediator(&mut self, mediator: Arc<Mutex<BadMediator>>) {
        self.mediator = Some(mediator);
    }

    fn notify(&mut self, event: &str) {
        println!("{} received: {}", self.name, event);
    }
}

fn mediator_cycle() {
    let mediator = Arc::new(Mutex::new(BadMediator::new()));

    let colleague = Arc::new(Mutex::new(ConcreteColleague {
        mediator: None,
        name: "C1".to_string(),
    }));

    // ❌ CYCLE: mediator -> colleague -> mediator
    mediator.lock().unwrap().register(Arc::clone(&colleague));
    colleague.lock().unwrap().set_mediator(Arc::clone(&mediator));
}

/// ✅ CORRECT: Mediator uses Weak references
use std::sync::Weak;

pub struct GoodMediator {
    colleagues: Vec<Weak<Mutex<dyn Colleague + Send>>>,
}

impl GoodMediator {
    pub fn new() -> Self {
        Self { colleagues: vec![] }
    }

    pub fn register(&mut self, colleague: &Arc<Mutex<dyn Colleague + Send>>) {
        self.colleagues.push(Arc::downgrade(colleague));
    }

    pub fn notify_all(&self, event: &str) {
        self.colleagues.retain(|weak| {
            if let Some(colleague) = weak.upgrade() {
                if let Ok(mut c) = colleague.lock() {
                    c.notify(event);
                }
                true
            } else {
                false
            }
        });
    }
}

pub trait GoodColleague {
    fn notify(&mut self, event: &str);
}
```

**Issue**: Bidirectional strong references between mediator and colleagues create memory leaks.

---

### 6.15 Memento Deep Copy Cost

```rust
/// ❌ INCORRECT: Memento copies entire state
pub struct BadMemento {
    state: Vec<u8>, // Could be megabytes
    timestamp: u64,
}

pub struct BadOriginator {
    state: Vec<u8>,
}

impl BadOriginator {
    pub fn save(&self) -> BadMemento {
        BadMemento {
            state: self.state.clone(), // ❌ O(n) copy every save
            timestamp: 0,
        }
    }

    pub fn restore(&mut self, memento: BadMemento) {
        self.state = memento.state; // Another O(n) copy
    }

    pub fn modify(&mut self) {
        self.state.push(1);
    }
}

fn expensive_mementos() {
    let mut originator = BadOriginator { state: vec![0; 1_000_000] };
    let mut history = vec![];

    for i in 0..100 {
        originator.modify();
        history.push(originator.save()); // ❌ 100MB allocated!
    }
}

/// ✅ CORRECT: Use persistent data structures or COW
use std::sync::Arc;

pub struct GoodMemento {
    state: Arc<Vec<u8>>, // Shared ownership
    timestamp: u64,
}

pub struct GoodOriginator {
    state: Vec<u8>,
}

impl GoodOriginator {
    pub fn save(&self) -> GoodMemento {
        GoodMemento {
            state: Arc::new(self.state.clone()), // Clone only if needed
            timestamp: 0,
        }
    }

    pub fn restore(&mut self, memento: GoodMemento) {
        self.state = (*memento.state).clone();
    }
}

/// ✅ CORRECT: Incremental/differential memento
pub struct IncrementalMemento {
    changes: Vec<Change>,
    base: Option<Arc<Vec<u8>>>,
}

pub enum Change {
    Append(u8),
    Remove(usize),
    Modify(usize, u8),
}

pub struct IncrementalOriginator {
    state: Vec<u8>,
    base: Arc<Vec<u8>>,
}

impl IncrementalOriginator {
    pub fn save(&self) -> IncrementalMemento {
        // Store only changes from base
        IncrementalMemento {
            changes: self.compute_changes(),
            base: Some(Arc::clone(&self.base)),
        }
    }

    fn compute_changes(&self) -> Vec<Change> {
        // Compute diff between base and current state
        vec![] // Implementation details omitted
    }
}
```

**Issue**: Memento pattern with large states creates excessive memory usage.

---

## 7. Anti-Patterns

### 7.1 Clone Everywhere

```rust
/// ❌ ANTI-PATTERN: Excessive cloning
fn clone_everywhere_bad() {
    let data = vec![1, 2, 3, 4, 5];

    process1(data.clone());
    process2(data.clone());
    process3(data.clone());
    // ❌ 3x memory usage, 3x copy time
}

fn process1(data: Vec<i32>) { /* ... */ }
fn process2(data: Vec<i32>) { /* ... */ }
fn process3(data: Vec<i32>) { /* ... */ }

/// ✅ CORRECT: Borrow instead of clone
fn borrow_instead_good() {
    let data = vec![1, 2, 3, 4, 5];

    process1_ref(&data);
    process2_ref(&data);
    process3_ref(&data);
    // ✅ Zero copying, shared read access
}

fn process1_ref(data: &[i32]) { /* ... */ }
fn process2_ref(data: &[i32]) { /* ... */ }
fn process3_ref(data: &[i32]) { /* ... */ }

/// ✅ CORRECT: Arc for shared ownership
use std::sync::Arc;

fn shared_ownership_good() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);

    process1_arc(Arc::clone(&data));
    process2_arc(Arc::clone(&data));
    process3_arc(Arc::clone(&data));
    // ✅ Reference counting, no data copy
}

fn process1_arc(data: Arc<Vec<i32>>) { /* ... */ }
fn process2_arc(data: Arc<Vec<i32>>) { /* ... */ }
fn process3_arc(data: Arc<Vec<i32>>) { /* ... */ }
```

**Impact**: Unnecessary cloning increases memory usage and decreases performance.

---

### 7.2 RefCell Abuse

```rust
use std::cell::RefCell;

/// ❌ ANTI-PATTERN: RefCell where borrowing would work
pub struct RefCellAbuse {
    data: RefCell<Vec<i32>>, // Interior mutability not needed
}

impl RefCellAbuse {
    pub fn new() -> Self {
        Self {
            data: RefCell::new(vec![]),
        }
    }

    /// ❌ Runtime borrow checking overhead
    pub fn add(&self, value: i32) {
        self.data.borrow_mut().push(value);
    }

    /// ❌ Potential panic at runtime
    pub fn get(&self, index: usize) -> i32 {
        self.data.borrow()[index]
    }
}

/// ❌ PANIC: Double borrow mut
fn refcell_panic() {
    let abuse = RefCellAbuse::new();
    let mut borrow1 = abuse.data.borrow_mut();
    // let borrow2 = abuse.data.borrow_mut(); // ❌ Would panic!
    borrow1.push(1);
}

/// ✅ CORRECT: Use regular borrowing
pub struct ProperBorrowing {
    data: Vec<i32>,
}

impl ProperBorrowing {
    pub fn new() -> Self {
        Self { data: vec![] }
    }

    /// Compile-time borrow checking
    pub fn add(&mut self, value: i32) {
        self.data.push(value);
    }

    /// Compile-time borrow checking
    pub fn get(&self, index: usize) -> Option<&i32> {
        self.data.get(index)
    }
}
```

**Impact**: RefCell moves borrow checking to runtime, hiding errors and adding overhead.

---

### 7.3 Unnecessary Rc<RefCell<T>>

```rust
use std::rc::Rc;
use std::cell::RefCell;

/// ❌ ANTI-PATTERN: Rc<RefCell<T>> for single ownership
fn unnecessary_rc_refcell() {
    let data: Rc<RefCell<Vec<i32>>> = Rc::new(RefCell::new(vec![]));

    // Only one owner, no need for Rc
    data.borrow_mut().push(1);
    data.borrow_mut().push(2);

    // ❌ Runtime overhead, no benefit
}

/// ❌ ANTI-PATTERN: Rc<RefCell<T>> when Cell would work
fn refcell_where_cell_works() {
    let counter: Rc<RefCell<i32>> = Rc::new(RefCell::new(0));

    *counter.borrow_mut() += 1; // ❌ RefCell for Copy type
}

/// ✅ CORRECT: Simple ownership
fn simple_ownership() {
    let mut data: Vec<i32> = vec![];
    data.push(1);
    data.push(2);
}

/// ✅ CORRECT: Cell for Copy types
use std::cell::Cell;

fn cell_for_copy() {
    let counter: Cell<i32> = Cell::new(0);
    counter.set(counter.get() + 1); // Zero-cost for Copy types
}

/// ✅ CORRECT: Proper use case for Rc<RefCell<T>>
fn legitimate_use_case() {
    // Shared ownership AND mutation needed
    let shared: Rc<RefCell<Vec<i32>>> = Rc::new(RefCell::new(vec![]));

    let shared2 = Rc::clone(&shared);

    // Different parts of code need to modify same data
    shared.borrow_mut().push(1);
    shared2.borrow_mut().push(2);

    println!("{:?}", shared.borrow()); // [1, 2]
}
```

**Impact**: Rc<RefCell<T>> adds reference counting and runtime borrow checking overhead unnecessarily.

---

## 8. Case Study: HTTP Client Design

### 8.1 Requirements Analysis

```
REQUIREMENTS HTTP-CLIENT:
    Functional:
    - Support GET, POST, PUT, DELETE methods
    - Configurable timeouts and retries
    - Request/response body handling
    - Header management

    Non-functional:
    - Async/await support
    - Connection pooling
    - Middleware support
    - Type-safe request building
```

### 8.2 Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                     HttpClient                              │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │   Builder   │  │  Connection │  │   MiddlewareStack   │  │
│  │   Pattern   │  │    Pool     │  │                     │  │
│  └─────────────┘  └─────────────┘  └─────────────────────┘  │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │   Request   │  │  Response   │  │   RetryStrategy     │  │
│  │   (Typed)   │  │  (Typed)    │  │   (Strategy)        │  │
│  └─────────────┘  └─────────────┘  └─────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### 8.3 Implementation

```rust
use std::collections::HashMap;
use std::time::Duration;
use std::sync::Arc;
use std::pin::Pin;
use std::future::Future;

/// HTTP method enum (Type-safe state machine)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Method {
    Get,
    Post,
    Put,
    Delete,
    Patch,
    Head,
    Options,
}

impl Method {
    pub fn as_str(&self) -> &'static str {
        match self {
            Method::Get => "GET",
            Method::Post => "POST",
            Method::Put => "PUT",
            Method::Delete => "DELETE",
            Method::Patch => "PATCH",
            Method::Head => "HEAD",
            Method::Options => "OPTIONS",
        }
    }
}

/// Headers newtype for type safety
#[derive(Debug, Clone, Default)]
pub struct Headers(HashMap<String, String>);

impl Headers {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn insert(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.0.insert(key.into(), value.into());
    }

    pub fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).map(|s| s.as_str())
    }
}

/// Request body (COW pattern)
#[derive(Debug, Clone)]
pub enum Body {
    Empty,
    Text(String),
    Bytes(Vec<u8>),
    Json(serde_json::Value),
}

impl Body {
    pub fn content_type(&self) -> Option<&'static str> {
        match self {
            Body::Empty => None,
            Body::Text(_) => Some("text/plain"),
            Body::Bytes(_) => Some("application/octet-stream"),
            Body::Json(_) => Some("application/json"),
        }
    }

    pub fn as_bytes(&self) -> Option<&[u8]> {
        match self {
            Body::Empty => Some(&[]),
            Body::Text(s) => Some(s.as_bytes()),
            Body::Bytes(b) => Some(b),
            Body::Json(v) => {
                // In real implementation, cache serialized form
                None
            }
        }
    }
}

/// Request with type-state builder
pub struct Request {
    method: Method,
    url: String,
    headers: Headers,
    body: Body,
    timeout: Duration,
}

/// Request builder (Type-state pattern)
pub struct RequestBuilder<MethodState, UrlState> {
    method: Option<Method>,
    url: Option<String>,
    headers: Headers,
    body: Body,
    timeout: Option<Duration>,
    _method: PhantomData<MethodState>,
    _url: PhantomData<UrlState>,
}

pub struct NoMethod;
pub struct MethodSet;
pub struct NoUrl;
pub struct UrlSet;

impl RequestBuilder<NoMethod, NoUrl> {
    pub fn new() -> Self {
        Self {
            method: None,
            url: None,
            headers: Headers::new(),
            body: Body::Empty,
            timeout: None,
            _method: PhantomData,
            _url: PhantomData,
        }
    }
}

impl<UrlState> RequestBuilder<NoMethod, UrlState> {
    pub fn get(self) -> RequestBuilder<MethodSet, UrlState> {
        self.with_method(Method::Get)
    }

    pub fn post(self) -> RequestBuilder<MethodSet, UrlState> {
        self.with_method(Method::Post)
    }

    pub fn put(self) -> RequestBuilder<MethodSet, UrlState> {
        self.with_method(Method::Put)
    }

    pub fn delete(self) -> RequestBuilder<MethodSet, UrlState> {
        self.with_method(Method::Delete)
    }

    fn with_method(self, method: Method) -> RequestBuilder<MethodSet, UrlState> {
        RequestBuilder {
            method: Some(method),
            url: self.url,
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
            _method: PhantomData,
            _url: PhantomData,
        }
    }
}

impl<MethodState> RequestBuilder<MethodState, NoUrl> {
    pub fn url(self, url: impl Into<String>) -> RequestBuilder<MethodState, UrlSet> {
        RequestBuilder {
            method: self.method,
            url: Some(url.into()),
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
            _method: PhantomData,
            _url: PhantomData,
        }
    }
}

impl<MethodState, UrlState> RequestBuilder<MethodState, UrlState> {
    pub fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key, value);
        self
    }

    pub fn body(mut self, body: Body) -> Self {
        self.body = body;
        self
    }

    pub fn json(self, value: serde_json::Value) -> Self {
        self.body(Body::Json(value))
            .header("Content-Type", "application/json")
    }

    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
}

impl RequestBuilder<MethodSet, UrlSet> {
    pub fn build(self) -> Request {
        Request {
            method: self.method.unwrap(),
            url: self.url.unwrap(),
            headers: self.headers,
            body: self.body,
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
        }
    }
}

/// Response type
#[derive(Debug)]
pub struct Response {
    status: u16,
    headers: Headers,
    body: Body,
}

impl Response {
    pub fn status(&self) -> u16 {
        self.status
    }

    pub fn is_success(&self) -> bool {
        self.status >= 200 && self.status < 300
    }

    pub fn json<T: serde::de::DeserializeOwned>(&self) -> Result<T, Error> {
        match &self.body {
            Body::Json(v) => serde_json::from_value(v.clone())
                .map_err(|e| Error::Deserialize(e.to_string())),
            Body::Text(s) => serde_json::from_str(s)
                .map_err(|e| Error::Deserialize(e.to_string())),
            _ => Err(Error::Deserialize("Invalid body type".to_string())),
        }
    }
}

/// Retry strategy (Strategy pattern)
pub trait RetryStrategy: Send + Sync {
    fn should_retry(&self, attempt: u32, error: &Error) -> bool;
    fn delay(&self, attempt: u32) -> Duration;
}

/// Exponential backoff retry
pub struct ExponentialBackoff {
    max_attempts: u32,
    base_delay: Duration,
    max_delay: Duration,
}

impl ExponentialBackoff {
    pub fn new(max_attempts: u32) -> Self {
        Self {
            max_attempts,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(10),
        }
    }
}

impl RetryStrategy for ExponentialBackoff {
    fn should_retry(&self, attempt: u32, error: &Error) -> bool {
        if attempt >= self.max_attempts {
            return false;
        }
        matches!(error, Error::Network(_) | Error::Timeout)
    }

    fn delay(&self, attempt: u32) -> Duration {
        let exp = 2u32.pow(attempt);
        let delay = self.base_delay * exp;
        delay.min(self.max_delay)
    }
}

/// Middleware trait
#[async_trait::async_trait]
pub trait Middleware: Send + Sync {
    async fn handle(
        &self,
        request: Request,
        next: Next<'_>,
    ) -> Result<Response, Error>;
}

pub type Next<'a> = Box<
    dyn FnOnce(Request) -> Pin<Box<dyn Future<Output = Result<Response, Error>> + Send>> + Send + 'a,
>;

/// HTTP Client
pub struct HttpClient {
    retry_strategy: Arc<dyn RetryStrategy>,
    middleware: Vec<Arc<dyn Middleware>>,
    default_headers: Headers,
    timeout: Duration,
}

impl HttpClient {
    pub fn new() -> Self {
        Self {
            retry_strategy: Arc::new(ExponentialBackoff::new(3)),
            middleware: vec![],
            default_headers: Headers::new(),
            timeout: Duration::from_secs(30),
        }
    }

    pub fn with_retry_strategy(mut self, strategy: impl RetryStrategy + 'static) -> Self {
        self.retry_strategy = Arc::new(strategy);
        self
    }

    pub fn with_middleware(mut self, middleware: impl Middleware + 'static) -> Self {
        self.middleware.push(Arc::new(middleware));
        self
    }

    pub fn with_default_header(
        mut self,
        key: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        self.default_headers.insert(key, value);
        self
    }

    /// Execute request with retries
    pub async fn execute(&self, request: Request) -> Result<Response, Error> {
        let mut attempt = 0;

        loop {
            match self.execute_once(&request).await {
                Ok(response) => return Ok(response),
                Err(error) => {
                    if self.retry_strategy.should_retry(attempt, &error) {
                        let delay = self.retry_strategy.delay(attempt);
                        tokio::time::sleep(delay).await;
                        attempt += 1;
                    } else {
                        return Err(error);
                    }
                }
            }
        }
    }

    async fn execute_once(&self, request: &Request) -> Result<Response, Error> {
        // In real implementation, make actual HTTP request
        // For now, return mock response
        Ok(Response {
            status: 200,
            headers: Headers::new(),
            body: Body::Empty,
        })
    }

    /// Convenience methods
    pub fn get(&self, url: impl Into<String>) -> RequestBuilder<NoMethod, UrlSet> {
        RequestBuilder::new().get().url(url)
    }

    pub fn post(&self, url: impl Into<String>) -> RequestBuilder<NoMethod, UrlSet> {
        RequestBuilder::new().post().url(url)
    }
}

/// Error type
#[derive(Debug, Clone)]
pub enum Error {
    Network(String),
    Timeout,
    Deserialize(String),
    InvalidRequest(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}
```

### 8.4 Usage Examples

```rust
/// Basic GET request
async fn basic_get() -> Result<(), Error> {
    let client = HttpClient::new();

    let request = client
        .get("https://api.example.com/users")
        .header("Accept", "application/json")
        .build();

    let response = client.execute(request).await?;

    if response.is_success() {
        println!("Success!");
    }

    Ok(())
}

/// POST with JSON body
async fn post_json() -> Result<(), Error> {
    let client = HttpClient::new()
        .with_default_header("X-API-Key", "secret123");

    let request = RequestBuilder::new()
        .post()
        .url("https://api.example.com/users")
        .json(serde_json::json!({
            "name": "Alice",
            "email": "alice@example.com"
        }))
        .build();

    let response = client.execute(request).await?;
    let user: serde_json::Value = response.json()?;

    println!("Created user: {:?}", user);
    Ok(())
}

/// Custom retry strategy
struct CustomRetry;

impl RetryStrategy for CustomRetry {
    fn should_retry(&self, attempt: u32, error: &Error) -> bool {
        attempt < 5 && matches!(error, Error::Network(_))
    }

    fn delay(&self, attempt: u32) -> Duration {
        Duration::from_secs(attempt as u64)
    }
}

async fn custom_retry_client() -> Result<(), Error> {
    let client = HttpClient::new()
        .with_retry_strategy(CustomRetry);

    let request = client
        .get("https://unreliable-api.example.com")
        .build();

    let response = client.execute(request).await?;
    println!("Status: {}", response.status());

    Ok(())
}
```

### 8.5 Patterns Applied Summary

| Pattern | Application | Benefit |
|---------|-------------|---------|
| Type-State Builder | RequestBuilder | Compile-time correctness |
| Strategy | RetryStrategy | Pluggable retry logic |
| Newtype | Headers, Method | Type safety |
| COW | Body | Efficient data handling |
| RAII | Connection pool | Automatic cleanup |
| Phantom Types | Builder states | Zero-cost state tracking |

---

## 9. Theorem Summary

### Theorem 9.1: BUILDER-COMPLETENESS

Builder ensures all required fields are set before construction completes.

### Theorem 9.2: TYPE-STATE-SAFETY

Invalid state transitions are compile-time errors in type-state builders.

### Theorem 9.3: NEWTYPE-ZERO-COST

Newtypes have identical memory layout and performance to their wrapped types.

### Theorem 9.4: RAII-SAFETY

Resources are released exactly once when RAII guards are dropped.

### Theorem 9.5: VIEW-ZERO-COST

Views provide zero-overhead abstractions over underlying data.

### Theorem 9.6: STRATEGY-EXTENSIBILITY

New strategies can be added without modifying existing code.

### Theorem 9.7: STATE-MACHINE-SAFETY

Invalid state transitions are caught at compile or runtime.

### Theorem 9.8: COW-LAZINESS

Cloning in Cow only occurs when mutation is actually requested.

### Theorem 9.9: PHANTOM-ZERO-SIZE

Phantom types add no runtime overhead.

---

## 10. Performance Considerations

### 10.1 Pattern Overhead Comparison

```
┌─────────────────────────┬───────────┬───────────┬─────────────┐
│ Pattern                 │ Stack     │ Heap      │ Runtime     │
├─────────────────────────┼───────────┼───────────┼─────────────┤
│ Newtype                 │ Same      │ None      │ Zero        │
│ RAII Guard              │ Ptr size  │ Resource  │ Drop call   │
│ Builder                 │ Fields    │ None      │ O(1)        │
│ Type-State Builder      │ Same      │ None      │ Zero*       │
│ Strategy (static)       │ None      │ None      │ Inlined     │
│ Strategy (dynamic)      │ VTable    │ Trait obj │ Indirect    │
│ Cow (no clone)          │ Ptr+Len   │ None      │ Zero        │
│ Cow (clone)             │ Ptr+Len   │ Copy      │ Clone cost  │
│ Phantom Types           │ Zero      │ None      │ Zero        │
│ View Types              │ Ptr+Len   │ None      │ Zero        │
└─────────────────────────┴───────────┴───────────┴─────────────┘

* Type-State may increase binary size due to monomorphization
```

### 10.2 Optimization Guidelines

1. **Prefer static dispatch** for hot paths
2. **Use Cow** for data that rarely needs modification
3. **Minimize RefCell** usage - prefer compile-time checked borrowing
4. **Avoid Rc<RefCell<T>>** unless truly necessary
5. **Use PhantomData** for compile-time state tracking
6. **Profile before optimizing** - patterns have different trade-offs

---

## 11. Conclusion

This chapter provided a comprehensive formal treatment of design patterns in Rust. Key takeaways:

1. **Rust's ownership system** fundamentally changes pattern implementation
2. **Type system** can encode many invariants at compile time
3. **Zero-cost abstractions** allow patterns without runtime overhead
4. **Counter-examples** demonstrate common pitfalls and their solutions

The formal semantics and theorems presented provide a foundation for reasoning about pattern correctness in Rust's unique context.

---

## References

1. Gamma, E., et al. "Design Patterns: Elements of Reusable Object-Oriented Software" (GoF)
2. Rust Programming Language Reference - Ownership
3. Rust API Guidelines
4. Rust Design Patterns (Rust Lang Nursery)
