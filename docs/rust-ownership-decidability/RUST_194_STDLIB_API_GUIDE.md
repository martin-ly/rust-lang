# Rust 1.94 Standard Library API Guide

**Release Date:** March 5, 2026
**Edition:** 2021 (compatible with 2024)
**MSRV Impact:** Some Cargo.toml features require Rust 1.94+

---

## Table of Contents

- [Rust 1.94 Standard Library API Guide](#rust-194-standard-library-api-guide)
  - [Table of Contents](#table-of-contents)
  - [Introduction](#introduction)
  - [Core Library APIs](#core-library-apis)
    - [Slice Methods](#slice-methods)
      - [`[T]::array_windows`](#tarray_windows)
      - [`[T]::element_offset`](#telement_offset)
    - [LazyCell and LazyLock](#lazycell-and-lazylock)
      - [`LazyCell::get`, `get_mut`, `force_mut`](#lazycellget-get_mut-force_mut)
      - [`LazyLock::get`, `get_mut`, `force_mut`](#lazylockget-get_mut-force_mut)
    - [Peekable Iterator](#peekable-iterator)
      - [`Peekable::next_if_map` and `next_if_map_mut`](#peekablenext_if_map-and-next_if_map_mut)
    - [Type Conversions](#type-conversions)
      - [`impl TryFrom<char> for usize`](#impl-tryfromchar-for-usize)
    - [Mathematical Constants](#mathematical-constants)
      - [`f32::consts::EULER_GAMMA` and `f64::consts::EULER_GAMMA`](#f32constseuler_gamma-and-f64constseuler_gamma)
      - [`f32::consts::GOLDEN_RATIO` and `f64::consts::GOLDEN_RATIO`](#f32constsgolden_ratio-and-f64constsgolden_ratio)
  - [Platform Intrinsics](#platform-intrinsics)
    - [x86 AVX512-FP16 Intrinsics](#x86-avx512-fp16-intrinsics)
    - [AArch64 NEON FP16 Intrinsics](#aarch64-neon-fp16-intrinsics)
  - [BinaryHeap Improvements](#binaryheap-improvements)
    - [Ord Bound Relaxation](#ord-bound-relaxation)
  - [Cargo Features](#cargo-features)
    - [Config Include Key](#config-include-key)
    - [Registry Pubtime Field](#registry-pubtime-field)
    - [TOML v1.1 Support](#toml-v11-support)
    - [CARGO\_BIN\_EXE\_ at Runtime](#cargo_bin_exe_-at-runtime)
  - [Const Stabilization](#const-stabilization)
    - [`f32::mul_add` and `f64::mul_add` in Const Contexts](#f32mul_add-and-f64mul_add-in-const-contexts)
  - [Summary Table](#summary-table)
  - [Migration Guide](#migration-guide)
    - [From `once_cell` to `std::sync::LazyLock`](#from-once_cell-to-stdsynclazylock)
    - [Using `array_windows` vs `windows`](#using-array_windows-vs-windows)
  - [References](#references)

---

## Introduction

Rust 1.94.0 brings significant enhancements to the standard library, focusing on:

- **Iterator ergonomics** with fixed-size array windows
- **Lazy initialization** with improved API surface
- **Platform intrinsics** for half-precision floating point
- **Cargo tooling** improvements for configuration management

This guide covers each new API with descriptions, code examples, ownership implications, and usage recommendations.

---

## Core Library APIs

### Slice Methods

#### `[T]::array_windows`

Returns an iterator over all contiguous windows of a fixed size `N`.

**Description:**
Unlike the dynamic `windows()` method, `array_windows()` returns `&[T; N]` (fixed-size arrays) instead of `&[T]` (slices). This enables:

- Compile-time size guarantees
- Pattern matching on array elements
- Elimination of runtime bounds checking

**Code Example:**

```rust
fn has_abba(s: &str) -> bool {
    s.as_bytes()
        .array_windows()
        .any(|[a1, b1, b2, a2]| (a1 != b1) && (a1 == a2) && (b1 == b2))
}

fn main() {
    let data = [1, 2, 3, 4, 5];

    // Type is inferred from pattern matching
    for [a, b] in data.array_windows() {
        println!("Pair: ({}, {})", a, b);
    }

    // Explicit type annotation also works
    let sums: Vec<i32> = data.array_windows::<3>()
        .map(|[a, b, c]| a + b + c)
        .collect();
    println!("{:?}", sums); // [6, 9, 12]
}
```

**Ownership/Safety Implications:**

- The iterator borrows from the slice immutably (`&self`)
- Returns `&[T; N]`, not owned values - no cloning or moving
- Lifetime tied to original slice
- No unsafe code required - fully memory-safe

**When to Use:**

- Sliding window algorithms (pattern matching in strings)
- Signal processing (convolution, filtering)
- Data analysis (rolling averages with compile-time window sizes)
- When you need array destructuring patterns on windows

---

#### `[T]::element_offset`

Calculates the offset of an element relative to the start of a slice.

**Description:**
Returns the offset (in elements, not bytes) of a pointer from the start of the slice. This is a convenience wrapper around pointer arithmetic that handles the calculations safely.

**Code Example:**

```rust
fn main() {
    let data = [10, 20, 30, 40, 50];
    let slice = &data[..];

    // Get a reference to an element
    let ptr = &slice[3];

    // Calculate offset from slice start
    if let Some(offset) = slice.element_offset(ptr) {
        println!("Element {} is at offset {}", ptr, offset); // offset = 3
    }

    // Useful for working with sub-slices
    let sub = &slice[2..];
    let element = &sub[1]; // Points to 40
    if let Some(offset) = slice.element_offset(element) {
        println!("Element in sub-slice has offset {} in original", offset);
    }
}
```

**Ownership/Safety Implications:**

- Returns `Option<usize>` - `None` if pointer doesn't belong to slice
- Performs bounds checking internally
- Does not dereference the pointer - only compares addresses
- Safe alternative to `offset_from` with proper validation

**When to Use:**

- Debugging pointer relationships
- Implementing custom slice algorithms
- Converting between indices and pointers safely
- When you need to verify a pointer belongs to a slice

---

### LazyCell and LazyLock

Rust 1.94 adds three new methods to both `LazyCell` (single-threaded) and `LazyLock` (thread-safe):

- `get()` - Get reference to initialized value
- `get_mut()` - Get mutable reference to initialized value
- `force_mut()` - Force initialization with mutable access

#### `LazyCell::get`, `get_mut`, `force_mut`

**Description:**
`LazyCell` provides lazy initialization for single-threaded contexts. The new methods allow:

- Checking initialization status without triggering initialization
- Mutable access to the contained value
- Forced initialization with custom logic

**Code Example:**

```rust
use std::cell::LazyCell;

fn main() {
    let mut lazy: LazyCell<String> = LazyCell::new(|| {
        println!("Initializing...");
        "Hello, Lazy!".to_string()
    });

    // Check if initialized without triggering initialization
    assert!(lazy.get().is_none());

    // Trigger initialization via Deref
    let _ = &*lazy;

    // Now get() returns Some
    assert_eq!(lazy.get(), Some("Hello, Lazy!"));

    // Get mutable reference
    if let Some(s) = lazy.get_mut() {
        s.push_str(" (modified)");
    }

    println!("{}", lazy.get().unwrap()); // "Hello, Lazy! (modified)"
}
```

**Ownership/Safety Implications:**

- `LazyCell<T>` owns the value of type `T`
- Uses interior mutability via `UnsafeCell` - safe because `!Sync`
- `get_mut()` requires `&mut self` - no aliasing violations
- `force_mut()` allows initialization with custom function
- Cannot cause data races (not `Sync`)

**When to Use:**

- Single-threaded lazy initialization
- Configuration loading on first access
- Memoization in sequential code
- When you need mutable access after initialization

---

#### `LazyLock::get`, `get_mut`, `force_mut`

**Description:**
`LazyLock` is the thread-safe equivalent of `LazyCell`. The new methods provide:

- Safe concurrent access to lazily-initialized data
- Mutable access when you have exclusive ownership
- Force initialization for complex startup sequences

**Code Example:**

```rust
use std::sync::LazyLock;
use std::collections::HashMap;
use std::sync::Mutex;

// Static lazy initialization - common pattern
static GLOBAL_CACHE: LazyLock<Mutex<HashMap<String, i32>>> =
    LazyLock::new(|| {
        println!("Initializing global cache...");
        Mutex::new(HashMap::new())
    });

fn main() {
    // Check if initialized (rarely needed for statics)
    // Note: for statics, get() always returns Some after first access

    // Thread-safe access
    {
        let cache = GLOBAL_CACHE.lock().unwrap();
        println!("Cache size: {}", cache.len());
    }

    // Insert data
    {
        let mut cache = GLOBAL_CACHE.lock().unwrap();
        cache.insert("key".to_string(), 42);
    }

    // Example with owned LazyLock
    let mut lazy: LazyLock<Vec<i32>> = LazyLock::new(|| vec![1, 2, 3]);

    // Get mutable access
    if let Some(v) = lazy.get_mut() {
        v.push(4);
    }

    println!("{:?}", &*lazy); // [1, 2, 3, 4]
}
```

**Ownership/Safety Implications:**

- Thread-safe via internal synchronization (similar to `OnceLock`)
- `Sync` when `T: Send + Sync` - safe for static variables
- `get_mut()` requires `&mut self` - ensures exclusive access
- No deadlocks possible with `get()` - uses `Once` internally
- Poisoning not applicable (unlike `Mutex`)

**When to Use:**

- Global/static lazy initialization
- Expensive computation that should happen once
- Configuration singletons
- Thread-safe memoization

---

### Peekable Iterator

#### `Peekable::next_if_map` and `next_if_map_mut`

**Description:**
These methods combine conditional consumption with mapping. They peek at the next element, apply a mapping function, and:

- If the function returns `Some`, consume the element and return the mapped value
- If the function returns `None`, keep the element for future iteration

`next_if_map_mut` provides mutable access without consuming ownership.

**Code Example:**

```rust
fn main() {
    let data = vec!["1", "two", "3", "four", "5"];
    let mut iter = data.into_iter().peekable();

    let mut numbers = Vec::new();

    // Consume and parse numeric strings only
    while let Some(n) = iter.next_if_map(|s| s.parse::<i32>().ok()) {
        numbers.push(n);
    }

    println!("Numbers: {:?}", numbers); // [1, 3, 5]
    println!("Remaining: {:?}", iter.collect::<Vec<_>>());
    // ["two", "four"]
}
```

**Ownership/Safety Implications:**

- `next_if_map` takes `FnOnce(T) -> Option<U>` - consumes the item
- `next_if_map_mut` takes `FnMut(&mut T) -> Option<U>` - mutates in place
- If the function panics, the item is consumed (dropped)
- No memory leaks - ownership is always transferred or retained

**When to Use:**

- Tokenizing/parsing with lookahead
- Filtering while transforming
- State machines consuming input conditionally
- When you need both peeking and mapping in one operation

---

### Type Conversions

#### `impl TryFrom<char> for usize`

**Description:**
Allows converting a `char` to `usize` representing its Unicode scalar value. This complements the existing `u32` conversion.

**Code Example:**

```rust
fn main() {
    // Convert char to usize (Unicode scalar value)
    let c = 'A';
    let code: usize = c.try_into().unwrap();
    assert_eq!(code, 65);

    let emoji = '🦀';
    let code: usize = emoji.try_into().unwrap();
    assert_eq!(code, 0x1F980); // 129408

    // Works with any Unicode scalar value
    let ch = '中';
    let code: usize = ch.try_into().unwrap();
    assert_eq!(code, 20013);
}
```

**Ownership/Safety Implications:**

- `char` is `Copy` - no ownership transfer
- Conversion always succeeds (Unicode scalar values fit in `usize`)
- No unsafe code
- Use `as usize` for infallible conversion (when `char` is known valid)

**When to Use:**

- Indexing by character code
- Character arithmetic
- Converting between text representations
- Building character tables/lookup arrays

---

### Mathematical Constants

#### `f32::consts::EULER_GAMMA` and `f64::consts::EULER_GAMMA`

**Description:**
The Euler-Mascheroni constant (γ ≈ 0.57721566...), appearing in number theory, analysis, and asymptotic expansions.

**Code Example:**

```rust
fn main() {
    use std::f64::consts::EULER_GAMMA;

    // Euler's constant appears in the asymptotic expansion of harmonic numbers
    // H_n ≈ ln(n) + γ + 1/(2n) - ...
    fn harmonic_approx(n: u64) -> f64 {
        (n as f64).ln() + EULER_GAMMA + 1.0 / (2.0 * n as f64)
    }

    // Also appears in the digamma function (derivative of log gamma)
    // ψ(1) = -γ
    println!("Euler's constant: {:.10}", EULER_GAMMA);

    // f32 version also available
    use std::f32::consts::EULER_GAMMA as GAMMA_F32;
    println!("f32 version: {}", GAMMA_F32);
}
```

**Ownership/Safety Implications:**

- Constants are `const` items - no runtime overhead
- `Copy` type - no ownership concerns
- IEEE 754 double-precision value

**When to Use:**

- Number theory algorithms
- Asymptotic analysis
- Special function implementations
- Numerical analysis

---

#### `f32::consts::GOLDEN_RATIO` and `f64::consts::GOLDEN_RATIO`

**Description:**
The golden ratio (φ ≈ 1.61803399...), appearing in mathematics, art, and algorithms like Fibonacci heap analysis.

**Code Example:**

```rust
fn main() {
    use std::f64::consts::GOLDEN_RATIO;

    // φ satisfies φ² = φ + 1
    assert!((GOLDEN_RATIO * GOLDEN_RATIO - (GOLDEN_RATIO + 1.0)).abs() < 1e-15);

    // Used in Fibonacci numbers closed form (Binet's formula)
    // F_n = round(φⁿ / √5)
    fn fibonacci_approx(n: u32) -> f64 {
        let phi = GOLDEN_RATIO;
        let sqrt5 = 5.0f64.sqrt();
        (phi.powi(n as i32) / sqrt5).round()
    }

    println!("Fibonacci(10) ≈ {}", fibonacci_approx(10)); // 55

    // Golden ratio conjugate
    let phi_conj = 1.0 - GOLDEN_RATIO; // or -1.0 / GOLDEN_RATIO
    println!("φ conjugate: {}", phi_conj);
}
```

**Ownership/Safety Implications:**

- Compile-time constants - no runtime cost
- Exact IEEE 754 representation (best possible approximation)
- Available in both `f32` and `f64` precisions

**When to Use:**

- Fibonacci algorithms
- Golden section search
- Aesthetic proportions
- Algorithm analysis

---

## Platform Intrinsics

### x86 AVX512-FP16 Intrinsics

**Description:**
Rust 1.94 stabilizes AVX512-FP16 intrinsics for x86_64 platforms with AVX512-FP16 support. These provide hardware acceleration for half-precision (16-bit) floating point operations.

**Note:** Intrinsics depending on the unstable `f16` type remain unstable.

**Code Example:**

```rust
#[cfg(target_arch = "x86_64")]
fn main() {
    #[cfg(target_feature = "avx512fp16")]
    {
        use std::arch::x86_64::*;

        // Create a vector of 16-bit floats (stored as u16)
        // These represent half-precision floats
        let a = _mm_set1_epi16(0x3C00); // 1.0 in f16
        let b = _mm_set1_epi16(0x4000); // 2.0 in f16

        // Perform addition using AVX512-FP16
        let result = unsafe { _mm_add_ph(a, b) };

        // Extract and interpret result
        let result_arr: [i16; 8] = unsafe { std::mem::transmute(result) };
        println!("Result (as u16): {:04X?}", result_arr);
    }

    #[cfg(not(target_feature = "avx512fp16"))]
    {
        println!("AVX512-FP16 not available on this target");
    }
}

#[cfg(not(target_arch = "x86_64"))]
fn main() {
    println!("x86 intrinsics not available on this architecture");
}
```

**Ownership/Safety Implications:**

- Requires `unsafe` blocks - hardware intrinsics bypass type safety
- Platform-specific - use `cfg` for portability
- No automatic fallback - runtime feature detection required
- Data is manipulated as raw bits (i16/u16) until operations

**When to Use:**

- Machine learning inference (f16 is common in ML)
- Graphics processing
- Numerical computing with reduced precision
- Bandwidth-constrained data transfers

---

### AArch64 NEON FP16 Intrinsics

**Description:**
ARM NEON FP16 intrinsics provide hardware acceleration for half-precision floating point on ARM64 platforms (ARMv8.2-A+).

**Code Example:**

```rust
#[cfg(target_arch = "aarch64")]
fn main() {
    #[cfg(target_feature = "fp16")]
    {
        use std::arch::aarch64::*;

        // Create vectors with f16 values (stored as u16)
        let a: float16x8_t = unsafe { vdupq_n_f16(1.0f16) };
        let b: float16x8_t = unsafe { vdupq_n_f16(2.0f16) };

        // Perform vector addition
        let result: float16x8_t = unsafe { vaddq_f16(a, b) };

        // Store results
        let mut output = [0f16; 8];
        unsafe { vst1q_f16(output.as_mut_ptr(), result) };

        println!("Results: {:?}", output); // [3.0, 3.0, ...]
    }

    #[cfg(not(target_feature = "fp16"))]
    {
        println!("FP16 not available on this target");
    }
}

#[cfg(not(target_arch = "aarch64"))]
fn main() {
    println!("AArch64 intrinsics not available on this architecture");
}
```

**Ownership/Safety Implications:**

- `unsafe` required for all intrinsics
- Feature detection at runtime recommended
- NEON types are SIMD types - special alignment requirements
- Results may vary between ARM implementations

**When to Use:**

- Mobile/embedded ML inference
- Signal processing on ARM
- Power-efficient computation
- Cross-platform f16 support with x86

---

## BinaryHeap Improvements

### Ord Bound Relaxation

**Description:**
Rust 1.94 relaxes the `T: Ord` bound on several `BinaryHeap<T>` methods, allowing heap operations on types that only implement basic traits.

**Methods with relaxed bounds:**

- `new()` - No longer requires `T: Ord`
- `with_capacity()` - No longer requires `T: Ord`
- `len()` - Only requires `T` (no trait bounds)
- `is_empty()` - Only requires `T` (no trait bounds)
- `iter()` - Only requires `T` (no trait bounds)
- `capacity()` - Only requires `T` (no trait bounds)

**Code Example:**

```rust
use std::collections::BinaryHeap;

// A type that doesn't implement Ord
#[derive(Debug, Clone)]
struct UnorderedData {
    id: u32,
    payload: String,
}

fn main() {
    // Can now create a BinaryHeap without Ord bound
    let mut heap: BinaryHeap<UnorderedData> = BinaryHeap::new();

    // Can check properties without Ord
    assert!(heap.is_empty());
    assert_eq!(heap.len(), 0);

    // These still require T: Ord:
    // heap.push(UnorderedData { id: 1, payload: "test".into() }); // ERROR!
    // heap.pop(); // ERROR!

    // But we can use the heap as storage and convert later
    let items = vec![
        UnorderedData { id: 3, payload: "c".into() },
        UnorderedData { id: 1, payload: "a".into() },
        UnorderedData { id: 2, payload: "b".into() },
    ];

    // Create heap with Ord-implementing wrapper
    let ordered_heap: BinaryHeap<_> = items
        .into_iter()
        .map(|d| (d.id, d)) // (u32, UnorderedData) implements Ord
        .collect();

    println!("Heap size: {}", ordered_heap.len());
}
```

**Ownership/Safety Implications:**

- No change to heap invariant safety
- Methods requiring heap property still need `Ord`
- Type safety preserved - cannot accidentally use unordered type where order matters

**When to Use:**

- Delayed initialization patterns
- Generic code where heap might not be fully used
- Building generic data structures that may include BinaryHeap
- Wrapper patterns for complex ordering

---

## Cargo Features

### Config Include Key

**Description:**
The `include` key in `.cargo/config.toml` allows modular configuration by including other TOML files.

**Code Example:**

`.cargo/config.toml`:

```toml
# Include paths as strings (required by default)
include = [
    "configs/defaults.toml",
    "configs/local.toml",
]

# Or with inline tables for more control
include = [
    { path = "configs/required.toml" },
    { path = "configs/optional.toml", optional = true },
]

# Your other config settings
[build]
target = "x86_64-unknown-linux-gnu"

[profile.release]
opt-level = 3
```

`configs/defaults.toml`:

```toml
[env]
DATABASE_URL = "postgres://localhost/mydb"
```

`configs/local.toml`:

```toml
[env]
DATABASE_URL = "postgres://localhost/mydb_dev"
RUST_LOG = "debug"
```

**Ownership/Safety Implications:**

- Configuration is merged - later includes override earlier ones
- `optional = true` prevents errors for missing files
- Paths are relative to the config file location
- No sandboxing - included files execute with full Cargo privileges

**When to Use:**

- Sharing configuration across team members
- Separating environment-specific settings
- Monorepo with shared build settings
- CI/CD with different configurations per pipeline

---

### Registry Pubtime Field

**Description:**
The registry index now includes a `pubtime` field recording when each crate version was published. This enables time-based dependency resolution in future tooling.

**Code Example:**

```toml
# This is in the registry index, not your Cargo.toml
# Crates.io backfills pubtime gradually

# Your Cargo.toml doesn't change, but tools can use pubtime:
# - cargo update --newer-than 2025-01-01
# - cargo tree --published-after 2024-06-01
```

**Usage in tooling:**

```rust
// Example: Checking publication time (conceptual)
use std::time::{SystemTime, Duration};

fn is_recently_published(pubtime: SystemTime) -> bool {
    let one_month = Duration::from_secs(30 * 24 * 3600);
    SystemTime::now().duration_since(pubtime)
        .map(|d| d < one_month)
        .unwrap_or(false)
}
```

**Ownership/Safety Implications:**

- Metadata only - doesn't affect compilation
- Not all crates have pubtime yet (backfilling in progress)
- Timestamps are UTC

**When to Use:**

- Audit dependencies by age
- Time-based update policies
- Supply chain security analysis
- Compliance reporting

---

### TOML v1.1 Support

**Description:**
Cargo now parses TOML v1.1, which includes several quality-of-life improvements:

**New features:**

- Multi-line inline tables with trailing commas
- `\xHH` and `\e` string escape sequences
- Optional seconds in time values (default to 0)

**Code Example:**

```toml
# Before (TOML v1.0) - single line required
dependencies = { serde = { version = "1.0", features = ["derive"] }, tokio = { version = "1", features = ["full"] } }

# After (TOML v1.1) - multi-line inline tables
dependencies = {
    serde = {
        version = "1.0",
        features = ["derive"],
    },
    tokio = {
        version = "1",
        features = ["full"],
    },
}

# Escape sequences
[package]
metadata = { escape = "\x1B[31mRed\x1B[0m" }  # ANSI escape

# Times without seconds
[metadata.build]
timestamp = 2025-03-05T12:30  # seconds default to 00
```

**MSRV Considerations:**

- Using TOML v1.1 features raises your development MSRV
- `cargo publish` rewrites manifests to remain compatible with older parsers
- Third-party tools may need updates to parse new syntax

**When to Use:**

- Large dependency tables needing formatting
- Configuration with ANSI escape sequences
- Precise control over TOML formatting

---

### CARGO_BIN_EXE_<crate> at Runtime

**Description:**
The `CARGO_BIN_EXE_<name>` environment variable is now available at runtime (not just compile time), making it easier for binaries to locate other binaries in the same package.

**Code Example:**

`Cargo.toml`:

```toml
[package]
name = "my-toolchain"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "my-toolchain"

[[bin]]
name = "worker"
```

`src/main.rs`:

```rust
use std::process::Command;

fn main() {
    // Now available at runtime via std::env::var
    // Previously only available at compile time via env!()

    let worker_path = std::env::var("CARGO_BIN_EXE_worker")
        .expect("Worker binary path not found");

    // Spawn worker process
    let output = Command::new(&worker_path)
        .arg("--help")
        .output()
        .expect("Failed to execute worker");

    println!("Worker output: {}", String::from_utf8_lossy(&output.stdout));

    // Can also use compile-time version for static paths
    let worker_static = env!("CARGO_BIN_EXE_worker");
    println!("Compile-time path: {}", worker_static);
}
```

**Ownership/Safety Implications:**

- Runtime lookup allows dynamic binary discovery
- Path may differ from compile-time if binary moved
- No path escaping - verify paths if from untrusted sources

**When to Use:**

- Multi-binary packages
- Toolchains with subcommands
- Integration testing
- Plugin architectures

---

## Const Stabilization

### `f32::mul_add` and `f64::mul_add` in Const Contexts

**Description:**
Fused multiply-add (`a * b + c`) is now available in `const fn`, `const` blocks, and `static` initializers. This operation performs multiplication and addition with a single rounding, improving precision and performance.

**Code Example:**

```rust
// Compile-time computation with mul_add
const fn polynomial(x: f64) -> f64 {
    // Compute: 2x² + 3x + 1
    // More precise than: 2.0 * x * x + 3.0 * x + 1.0
    let a = 2.0f64.mul_add(x, 3.0).mul_add(x, 1.0)
    a
}

const RESULT: f64 = polynomial(2.5);

fn main() {
    println!("Polynomial(2.5) = {}", RESULT); // 21.0

    // Also usable in static
    static SCALE_FACTOR: f64 = 1.5f64.mul_add(2.0, 0.5);
    println!("Scale factor: {}", SCALE_FACTOR); // 3.5
}
```

**Ownership/Safety Implications:**

- `Copy` type - no ownership semantics
- Single rounding (fused) improves numerical precision
- No unsafe code
- Hardware acceleration on most modern CPUs

**When to Use:**

- High-precision numerical constants
- Polynomial evaluation
- Linear algebra in const contexts
- DSP filter coefficients
- Any `a * b + c` pattern where precision matters

---

## Summary Table

| API | Category | Ownership Pattern | Thread-Safe |
|-----|----------|------------------|-------------|
| `[T]::array_windows` | Iterator | Borrows slice | N/A |
| `[T]::element_offset` | Utility | Borrows slice | N/A |
| `LazyCell::get/get_mut` | Lazy init | Owns value | No |
| `LazyLock::get/get_mut` | Lazy init | Owns value | Yes |
| `Peekable::next_if_map` | Iterator | Consumes/keeps item | N/A |
| `TryFrom<char> for usize` | Conversion | Copy type | N/A |
| `EULER_GAMMA` | Constants | Copy type | N/A |
| `GOLDEN_RATIO` | Constants | Copy type | N/A |
| AVX512-FP16 | Intrinsics | Unsafe/raw bits | Platform |
| NEON FP16 | Intrinsics | Unsafe/raw bits | Platform |
| BinaryHeap relaxation | Collections | Generic | No change |
| `mul_add` (const) | Numerics | Copy type | N/A |

---

## Migration Guide

### From `once_cell` to `std::sync::LazyLock`

```rust
// Before (once_cell)
use once_cell::sync::Lazy;
static DATA: Lazy<Vec<i32>> = Lazy::new(|| vec![1, 2, 3]);

// After (std)
use std::sync::LazyLock;
static DATA: LazyLock<Vec<i32>> = LazyLock::new(|| vec![1, 2, 3]);
```

### Using `array_windows` vs `windows`

```rust
// Before: Dynamic windows with runtime bounds
for window in slice.windows(4) {
    let a = window[0]; // Runtime bounds check
    let b = window[1];
    // ...
}

// After: Fixed-size windows, compile-time guarantees
for [a, b, c, d] in slice.array_windows() {
    // Pattern matching works directly
    // No runtime bounds checks
}
```

---

## References

- [Rust 1.94.0 Release Notes](https://blog.rust-lang.org/2026/03/05/Rust-1.94.0/)
- [Cargo 1.94 Changelog](https://doc.rust-lang.org/cargo/CHANGELOG.html)
- [TOML v1.1 Specification](https://toml.io/en/v1.1.0)
- [AVX512-FP16 Intrinsics Guide](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html)
- [ARM NEON Reference](https://developer.arm.com/architectures/instruction-sets/intrinsics/)

---

*Document generated for Rust 1.94.0 - March 2026*
