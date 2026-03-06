# 08-03. Rust FFI Patterns Deep Dive

> "Foreign Function Interface is where memory safety meets the real world—and the real world always wins."

This chapter provides a comprehensive exploration of Rust's Foreign Function Interface (FFI) patterns, focusing on memory safety, ownership semantics, and practical implementation strategies when interfacing with C, C++, Python, Ruby, Node.js, and other languages.

## Table of Contents

- [08-03. Rust FFI Patterns Deep Dive](#08-03-rust-ffi-patterns-deep-dive)
  - [Table of Contents](#table-of-contents)
  - [1. FFI Safety Model](#1-ffi-safety-model)
    - [1.1 The Unsafe Boundary](#11-the-unsafe-boundary)
    - [1.2 Core Invariants](#12-core-invariants)
    - [1.3 Safety Contract Documentation](#13-safety-contract-documentation)
  - [2. Memory Management Patterns](#2-memory-management-patterns)
    - [2.1 Pattern 1: Rust Allocates, Rust Frees](#21-pattern-1-rust-allocates-rust-frees)
    - [2.2 Pattern 2: C Allocates, C Frees](#22-pattern-2-c-allocates-c-frees)
    - [2.3 Pattern 3: Shared Ownership](#23-pattern-3-shared-ownership)
    - [2.4 Pattern 4: Custom Allocator Bridge](#24-pattern-4-custom-allocator-bridge)
  - [3. Type Safety](#3-type-safety)
    - [3.1 Type Mapping Reference](#31-type-mapping-reference)
    - [3.2 Transparent Types](#32-transparent-types)
    - [3.3 Opaque Types](#33-opaque-types)
    - [3.4 String Handling](#34-string-handling)
    - [3.5 Slice Types](#35-slice-types)
  - [4. Panic Safety](#4-panic-safety)
    - [4.1 The Panic Problem](#41-the-panic-problem)
    - [4.2 The Solution: catch\_unwind](#42-the-solution-catch_unwind)
    - [4.3 Abort-on-Panic Strategy](#43-abort-on-panic-strategy)
    - [4.4 Panic-Safe Data Structures](#44-panic-safe-data-structures)
  - [5. Counter-Examples and Anti-Patterns](#5-counter-examples-and-anti-patterns)
    - [5.1 Counter-Example 1: Use After Free](#51-counter-example-1-use-after-free)
    - [5.2 Counter-Example 2: Dangling Pointer Return](#52-counter-example-2-dangling-pointer-return)
    - [5.3 Counter-Example 3: Null Pointer Dereference](#53-counter-example-3-null-pointer-dereference)
    - [5.4 Counter-Example 4: Uninitialized Memory](#54-counter-example-4-uninitialized-memory)
    - [5.5 Counter-Example 5: Invalid Enum Value](#55-counter-example-5-invalid-enum-value)
    - [5.6 Counter-Example 6: String Without Null Terminator](#56-counter-example-6-string-without-null-terminator)
    - [5.7 Counter-Example 7: Slice Length Mismatch](#57-counter-example-7-slice-length-mismatch)
    - [5.8 Counter-Example 8: Panic Across Boundary](#58-counter-example-8-panic-across-boundary)
    - [5.9 Counter-Example 9: Thread-Unsafe Data Sharing](#59-counter-example-9-thread-unsafe-data-sharing)
    - [5.10 Counter-Example 10: Mutable Aliasing](#510-counter-example-10-mutable-aliasing)
    - [5.11 Counter-Example 11: Incorrect ABI](#511-counter-example-11-incorrect-abi)
    - [5.12 Counter-Example 12: Struct Layout Mismatch](#512-counter-example-12-struct-layout-mismatch)
    - [5.13 Counter-Example 13: Bitfield Handling](#513-counter-example-13-bitfield-handling)
    - [5.14 Counter-Example 14: Callback Lifetime](#514-counter-example-14-callback-lifetime)
    - [5.15 Counter-Example 15: Resource Leak](#515-counter-example-15-resource-leak)
    - [5.16 Counter-Example 16: Integer Overflow in FFI](#516-counter-example-16-integer-overflow-in-ffi)
    - [5.17 Counter-Example 17: Data Race in Global State](#517-counter-example-17-data-race-in-global-state)
    - [5.18 Counter-Example 18: Double Free](#518-counter-example-18-double-free)
    - [5.19 Counter-Example 19: Mismatched Drop Order](#519-counter-example-19-mismatched-drop-order)
    - [5.20 Counter-Example 20: FFI Type Confusion](#520-counter-example-20-ffi-type-confusion)
  - [6. Bindgen and Cbindgen](#6-bindgen-and-cbindgen)
    - [6.1 Bindgen: C to Rust](#61-bindgen-c-to-rust)
    - [6.2 Cbindgen: Rust to C](#62-cbindgen-rust-to-c)
  - [7. CXX Crate for Safe C++ Interop](#7-cxx-crate-for-safe-c-interop)
    - [7.1 Basic Setup](#71-basic-setup)
    - [7.2 CXX Bridge](#72-cxx-bridge)
    - [7.3 Safe String Handling](#73-safe-string-handling)
    - [7.4 Safe Vectors](#74-safe-vectors)
    - [7.5 Safe Exceptions](#75-safe-exceptions)
    - [7.6 Shared Types](#76-shared-types)
  - [8. Case Study: Embedding Python](#8-case-study-embedding-python)
    - [8.1 Project Setup](#81-project-setup)
    - [8.2 Basic Module Structure](#82-basic-module-structure)
    - [8.3 Python Usage](#83-python-usage)
    - [8.4 Memory Management in PyO3](#84-memory-management-in-pyo3)
  - [9. Case Study: Ruby Extensions](#9-case-study-ruby-extensions)
    - [9.1 Setup](#91-setup)
    - [9.2 Basic Extension](#92-basic-extension)
    - [9.3 Ruby Usage](#93-ruby-usage)
    - [9.4 Error Handling](#94-error-handling)
  - [10. Case Study: Node.js Native Modules](#10-case-study-nodejs-native-modules)
    - [10.1 Setup](#101-setup)
    - [10.2 Basic Module](#102-basic-module)
    - [10.3 TypeScript Definitions](#103-typescript-definitions)
    - [10.4 JavaScript Usage](#104-javascript-usage)
  - [11. Advanced Patterns](#11-advanced-patterns)
    - [11.1 Object Pools](#111-object-pools)
    - [11.2 Zero-Copy Serialization](#112-zero-copy-serialization)
    - [11.3 Async FFI with Futures](#113-async-ffi-with-futures)
    - [11.4 Memory-Mapped I/O](#114-memory-mapped-io)
  - [12. Best Practices Summary](#12-best-practices-summary)
    - [12.1 Safety Checklist](#121-safety-checklist)
    - [12.2 Theorems Summary](#122-theorems-summary)
    - [12.3 Pattern Selection Guide](#123-pattern-selection-guide)
    - [12.4 Common Pitfalls to Avoid](#124-common-pitfalls-to-avoid)
  - [Conclusion](#conclusion)

---

## 1. FFI Safety Model

### 1.1 The Unsafe Boundary

When Rust interacts with foreign code, it crosses an **unsafe boundary** where the compiler's guarantees no longer apply. Understanding this boundary is fundamental to writing correct FFI code.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           FFI SAFETY BOUNDARY                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│    ┌─────────────┐        ┌─────────────┐        ┌─────────────────────┐   │
│    │  Safe Rust  │ ←────→ │ Unsafe Rust │ ←────→ │    Foreign Code     │   │
│    │             │        │             │        │                     │   │
│    │ • Ownership │        │ • Raw ptrs  │        │ • C                 │   │
│    │ • Borrowck  │        │ • FFI calls │        │ • C++               │   │
│    │ • No UB     │        │ • unsafe{}  │        │ • Python (C API)    │   │
│    │             │        │             │        │ • Ruby (C API)      │   │
│    │  GUARANTEED │        │  MANUAL     │        │  UNSAFE             │   │
│    │             │        │  VERIFY     │        │                     │   │
│    └─────────────┘        └─────────────┘        └─────────────────────┘   │
│           ↑                                               ↑                 │
│           │                                               │                 │
│           └───────────────────────────────────────────────┘                 │
│                    Trust Boundary (Programmer Responsibility)               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**The Three-Layer Model:**

| Layer | Guarantees | Responsibility |
|-------|-----------|----------------|
| Safe Rust | Full ownership, borrow check, no UB | Compiler enforced |
| Unsafe Rust | Raw pointers, FFI calls, manual memory | Programmer verified |
| Foreign Code | No guarantees, manual everything | Programmer verified |

### 1.2 Core Invariants

When working across the FFI boundary, the following invariants must be maintained:

**Invariant 1: Safe Rust Guarantees Are Void in FFI**

```rust
// In Safe Rust, this is impossible
fn safe_rust() {
    let x = vec![1, 2, 3];
    // Compiler prevents use-after-free, double-free, etc.
}

// In FFI, all bets are off
pub unsafe extern "C" fn unsafe_ffi(ptr: *mut Vec<i32>) {
    // We must manually verify:
    // 1. ptr is not null
    // 2. ptr is properly aligned
    // 3. ptr points to valid memory
    // 4. No other thread is accessing this memory
    // 5. The data is in a valid state
}
```

**Invariant 2: Programmer Responsible for Pre/Post Conditions**

```rust
/// # Safety
///
/// - `ptr` must be a valid, non-null pointer to a `Data` structure
///   allocated by `create_data`
/// - `ptr` must not have been previously freed
/// - `ptr` must be properly aligned
/// - After this call, `ptr` is invalid and must not be used
#[no_mangle]
pub unsafe extern "C" fn free_data(ptr: *mut Data) {
    if ptr.is_null() {
        return;
    }
    // SAFETY: Caller guarantees ptr is valid per documentation
    unsafe {
        drop(Box::from_raw(ptr));
    }
}
```

**Invariant 3: ABI Compatibility Must Match Exactly**

```rust
// Rust side
#[repr(C)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

#[no_mangle]
pub extern "C" fn compute_distance(p1: Point, p2: Point) -> f64 {
    ((p2.x - p1.x).powi(2) + (p2.y - p1.y).powi(2)).sqrt()
}
```

```c
// C side - MUST match exactly
typedef struct {
    double x;
    double y;
} Point;

double compute_distance(Point p1, Point p2);
```

**Theorem FFI-BOUNDARY-SAFETY**:
> For any FFI boundary crossing, at least one side must be marked `unsafe`, and the safe side bears the burden of proof for all safety invariants.

### 1.3 Safety Contract Documentation

Every FFI function should document its safety contract:

```rust
/// Creates a new data structure and returns an opaque pointer.
///
/// # Returns
///
/// A valid pointer to a newly allocated `Data` structure, or null on OOM.
///
/// # Safety Contract
///
/// The caller must:
/// 1. Check for null return value
/// 2. Eventually call `data_free` with the returned pointer
/// 3. Not use the pointer after calling `data_free`
/// 4. Not free the pointer with any other function
///
/// # Thread Safety
///
/// The returned pointer is not thread-safe unless otherwise specified.
#[no_mangle]
pub extern "C" fn data_new() -> *mut Data {
    match Box::try_new(Data::default()) {
        Ok(data) => Box::into_raw(data),
        Err(_) => std::ptr::null_mut(),
    }
}
```

---

## 2. Memory Management Patterns

Memory management across FFI boundaries is one of the most challenging aspects of interoperability. There are three primary patterns, each with distinct trade-offs.

### 2.1 Pattern 1: Rust Allocates, Rust Frees

In this pattern, Rust maintains full ownership and control over memory. Foreign code receives only opaque pointers.

```rust
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int};

/// Opaque handle type
pub struct DataStore {
    items: Vec<String>,
    counter: usize,
}

/// Creates a new data store.
///
/// # Returns
///
/// A pointer to a new `DataStore`, or null if allocation fails.
///
/// # Safety
///
/// The caller must eventually call `datastore_free` to prevent leaks.
#[no_mangle]
pub extern "C" fn datastore_new() -> *mut DataStore {
    let store = Box::new(DataStore {
        items: Vec::new(),
        counter: 0,
    });
    Box::into_raw(store)
}

/// Adds a string to the data store.
///
/// # Safety
///
/// - `store` must be a valid pointer returned by `datastore_new`
/// - `store` must not have been freed
/// - `value` must be a valid null-terminated C string
#[no_mangle]
pub unsafe extern "C" fn datastore_add(
    store: *mut DataStore,
    value: *const c_char,
) -> c_int {
    if store.is_null() || value.is_null() {
        return -1;
    }

    // SAFETY: Caller guarantees valid pointers
    let store = unsafe { &mut *store };
    let c_str = unsafe { CStr::from_ptr(value) };

    match c_str.to_str() {
        Ok(s) => {
            store.items.push(s.to_string());
            store.counter += 1;
            0 // Success
        }
        Err(_) => -2, // Invalid UTF-8
    }
}

/// Gets the count of items in the store.
///
/// # Safety
///
/// - `store` must be a valid pointer returned by `datastore_new`
/// - `store` must not have been freed
#[no_mangle]
pub unsafe extern "C" fn datastore_count(store: *const DataStore) -> c_int {
    if store.is_null() {
        return -1;
    }
    // SAFETY: Caller guarantees valid pointer
    let store = unsafe { &*store };
    store.counter as c_int
}

/// Frees the data store.
///
/// # Safety
///
/// - `store` must be a valid pointer returned by `datastore_new`
/// - `store` must not have been previously freed
/// - After this call, `store` is invalid
#[no_mangle]
pub unsafe extern "C" fn datastore_free(store: *mut DataStore) {
    if !store.is_null() {
        // SAFETY: Caller guarantees valid pointer
        unsafe {
            drop(Box::from_raw(store));
        }
    }
}
```

**C Usage Example:**

```c
#include <stdio.h>
#include "rust_ffi.h"

int main() {
    DataStore* store = datastore_new();
    if (!store) {
        fprintf(stderr, "Failed to create store\n");
        return 1;
    }

    datastore_add(store, "Hello");
    datastore_add(store, "World");

    int count = datastore_count(store);
    printf("Items: %d\n", count);

    datastore_free(store);
    // store is now dangling - must not be used
    return 0;
}
```

**Advantages:**

- Full control over memory layout
- Can use Rust's allocator optimizations
- Safe to use with Rust's ownership system

**Disadvantages:**

- Requires explicit free function
- Potential for memory leaks if free is forgotten
- Cannot use C's allocator for debugging

### 2.2 Pattern 2: C Allocates, C Frees

When C needs to manage the lifetime of data, or when integrating with existing C codebases:

```rust
use std::alloc::{self, Layout};
use std::ffi::c_void;
use std::mem;
use std::os::raw::c_char;
use std::slice;

/// Allocator that uses C's malloc/free
pub struct CAllocator;

impl CAllocator {
    /// Allocates memory using C's malloc
    ///
    /// # Safety
    ///
    /// The returned pointer must be freed with C's free, not Rust's deallocator
    pub unsafe fn malloc(size: usize) -> *mut c_void {
        libc::malloc(size)
    }

    /// Frees memory allocated with C's malloc
    ///
    /// # Safety
    ///
    /// `ptr` must have been allocated by C's malloc and not yet freed
    pub unsafe fn free(ptr: *mut c_void) {
        libc::free(ptr);
    }
}

/// Data structure that C owns
#[repr(C)]
pub struct COwnedBuffer {
    pub data: *mut c_char,
    pub len: usize,
    pub capacity: usize,
}

/// Fills a pre-allocated buffer with data.
///
/// # Safety
///
/// - `buffer` must point to valid, writable memory of at least `buffer_len` bytes
/// - `buffer_len` must be the actual size of the buffer
/// - Returns number of bytes written, or -1 on error
#[no_mangle]
pub unsafe extern "C" fn fill_buffer(
    buffer: *mut c_char,
    buffer_len: usize,
) -> isize {
    if buffer.is_null() || buffer_len == 0 {
        return -1;
    }

    let data = b"Hello from Rust!";
    let to_write = data.len().min(buffer_len - 1); // Reserve space for null

    // SAFETY: Caller guarantees buffer is valid and writable
    let slice = unsafe { slice::from_raw_parts_mut(buffer as *mut u8, buffer_len) };
    slice[..to_write].copy_from_slice(&data[..to_write]);
    slice[to_write] = 0; // Null terminate

    to_write as isize
}

/// Creates a buffer that must be freed by C.
///
/// # Safety
///
/// The returned buffer's `data` field must be freed using C's free().
#[no_mangle]
pub extern "C" fn create_c_buffer() -> COwnedBuffer {
    let data = b"Rust-generated data\0";
    let len = data.len();

    // SAFETY: We're allocating with C's malloc
    let ptr = unsafe { libc::malloc(len) as *mut c_char };
    if ptr.is_null() {
        return COwnedBuffer {
            data: std::ptr::null_mut(),
            len: 0,
            capacity: 0,
        };
    }

    // SAFETY: We just allocated this memory
    unsafe {
        std::ptr::copy_nonoverlapping(data.as_ptr(), ptr as *mut u8, len);
    }

    COwnedBuffer {
        data: ptr,
        len: len - 1, // Exclude null terminator from length
        capacity: len,
    }
}

/// Frees a buffer allocated by Rust using C's allocator.
///
/// # Safety
///
/// - `buffer.data` must have been allocated by Rust's FFI functions
/// - `buffer.data` must not have been previously freed
#[no_mangle]
pub unsafe extern "C" fn free_c_buffer(buffer: COwnedBuffer) {
    if !buffer.data.is_null() {
        // SAFETY: Caller guarantees valid pointer from our allocation
        unsafe {
            libc::free(buffer.data as *mut c_void);
        }
    }
}
```

**Advantages:**

- Integrates naturally with C code
- Allows C to control allocation strategy
- Compatible with existing C memory debugging tools

**Disadvantages:**

- Cannot use Rust's ownership system
- More prone to use-after-free errors
- Requires careful documentation of ownership

### 2.3 Pattern 3: Shared Ownership

For complex scenarios where both sides need access:

```rust
use std::ffi::c_void;
use std::os::raw::c_int;
use std::sync::{Arc, Mutex, RwLock, Weak};
use std::sync::atomic::{AtomicUsize, Ordering};

/// Thread-safe shared data structure
pub struct SharedData {
    value: Mutex<i32>,
    reference_count: AtomicUsize,
}

/// Opaque handle for shared data
pub struct SharedDataHandle {
    arc: Arc<SharedData>,
}

/// Creates thread-safe shared data.
#[no_mangle]
pub extern "C" fn shared_data_new(initial_value: c_int) -> *mut SharedDataHandle {
    let data = Arc::new(SharedData {
        value: Mutex::new(initial_value),
        reference_count: AtomicUsize::new(1),
    });

    let handle = Box::new(SharedDataHandle { arc: data });
    Box::into_raw(handle)
}

/// Clones a reference to shared data (increments reference count).
///
/// # Safety
///
/// - `handle` must be a valid pointer from `shared_data_new`
/// - `handle` must not have been freed
#[no_mangle]
pub unsafe extern "C" fn shared_data_clone(
    handle: *const SharedDataHandle
) -> *mut SharedDataHandle {
    if handle.is_null() {
        return std::ptr::null_mut();
    }

    // SAFETY: Caller guarantees valid handle
    let handle = unsafe { &*handle };
    handle.arc.reference_count.fetch_add(1, Ordering::Relaxed);

    let new_handle = Box::new(SharedDataHandle {
        arc: Arc::clone(&handle.arc),
    });
    Box::into_raw(new_handle)
}

/// Gets the value from shared data.
///
/// # Safety
///
/// - `handle` must be a valid pointer
#[no_mangle]
pub unsafe extern "C" fn shared_data_get(handle: *const SharedDataHandle) -> c_int {
    if handle.is_null() {
        return 0;
    }

    let handle = unsafe { &*handle };
    match handle.arc.value.lock() {
        Ok(guard) => *guard,
        Err(_) => 0, // Poisoned mutex
    }
}

/// Sets the value in shared data.
///
/// # Safety
///
/// - `handle` must be a valid pointer
#[no_mangle]
pub unsafe extern "C" fn shared_data_set(
    handle: *const SharedDataHandle,
    value: c_int,
) -> c_int {
    if handle.is_null() {
        return -1;
    }

    let handle = unsafe { &*handle };
    match handle.arc.value.lock() {
        Ok(mut guard) => {
            *guard = value;
            0
        }
        Err(_) => -1,
    }
}

/// Releases a reference to shared data.
///
/// # Safety
///
/// - `handle` must be a valid pointer from `shared_data_new` or `shared_data_clone`
/// - `handle` must not have been previously freed
/// - After this call, `handle` is invalid
#[no_mangle]
pub unsafe extern "C" fn shared_data_release(handle: *mut SharedDataHandle) {
    if handle.is_null() {
        return;
    }

    // SAFETY: Caller guarantees valid handle
    let handle = unsafe { Box::from_raw(handle) };
    let prev_count = handle.arc.reference_count.fetch_sub(1, Ordering::Release);

    // If we were the last reference, the Arc will be dropped
    // when handle goes out of scope
    drop(handle);

    if prev_count == 1 {
        std::sync::atomic::fence(Ordering::Acquire);
        // Last reference dropped, data is freed
    }
}

/// Returns the current reference count (for debugging).
///
/// # Safety
///
/// - `handle` must be a valid pointer
#[no_mangle]
pub unsafe extern "C" fn shared_data_ref_count(handle: *const SharedDataHandle) -> usize {
    if handle.is_null() {
        return 0;
    }
    let handle = unsafe { &*handle };
    handle.arc.reference_count.load(Ordering::Relaxed)
}
```

**Advantages:**

- Multiple owners can safely access data
- Automatic cleanup when last reference is dropped
- Thread-safe by design

**Disadvantages:**

- Runtime overhead of reference counting
- Potential for reference cycles
- More complex mental model

### 2.4 Pattern 4: Custom Allocator Bridge

For integrating with custom C allocators:

```rust
use std::alloc::{GlobalAlloc, Layout, System};
use std::ffi::c_void;
use std::os::raw::{c_char, c_int};

/// Function pointers for custom C allocator
type CAllocFn = unsafe extern "C" fn(size: usize) -> *mut c_void;
type CFreeFn = unsafe extern "C" fn(ptr: *mut c_void);
type CReallocFn = unsafe extern "C" fn(ptr: *mut c_void, new_size: usize) -> *mut c_void;

static mut C_ALLOC: Option<CAllocFn> = None;
static mut C_FREE: Option<CFreeFn> = None;
static mut C_REALLOC: Option<CReallocFn> = None;

/// Registers a custom C allocator.
///
/// # Safety
///
/// This function must be called before any other FFI functions that allocate.
/// The provided function pointers must remain valid for the program's lifetime.
#[no_mangle]
pub unsafe extern "C" fn register_allocator(
    alloc_fn: CAllocFn,
    free_fn: CFreeFn,
    realloc_fn: CReallocFn,
) {
    C_ALLOC = Some(alloc_fn);
    C_FREE = Some(free_fn);
    C_REALLOC = Some(realloc_fn);
}

/// Custom allocator that delegates to C
pub struct CAllocatorBridge;

unsafe impl GlobalAlloc for CAllocatorBridge {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        match C_ALLOC {
            Some(alloc_fn) => alloc_fn(layout.size()) as *mut u8,
            None => System.alloc(layout),
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        match C_FREE {
            Some(free_fn) => free_fn(ptr as *mut c_void),
            None => System.dealloc(ptr, _layout),
        }
    }

    unsafe fn realloc(&self, ptr: *mut u8, _layout: Layout, new_size: usize) -> *mut u8 {
        match C_REALLOC {
            Some(realloc_fn) => realloc_fn(ptr as *mut c_void, new_size) as *mut u8,
            None => System.realloc(ptr, _layout, new_size),
        }
    }
}

#[global_allocator]
static ALLOCATOR: CAllocatorBridge = CAllocatorBridge;
```

---

## 3. Type Safety

### 3.1 Type Mapping Reference

Complete mapping between Rust and C types:

| Rust Type | C Type | Notes |
|-----------|--------|-------|
| `i8` | `int8_t` | Signed 8-bit integer |
| `i16` | `int16_t` | Signed 16-bit integer |
| `i32` | `int32_t` | Signed 32-bit integer |
| `i64` | `int64_t` | Signed 64-bit integer |
| `isize` | `intptr_t` | Pointer-sized signed integer |
| `u8` | `uint8_t` | Unsigned 8-bit integer |
| `u16` | `uint16_t` | Unsigned 16-bit integer |
| `u32` | `uint32_t` | Unsigned 32-bit integer |
| `u64` | `uint64_t` | Unsigned 64-bit integer |
| `usize` | `uintptr_t` / `size_t` | Pointer-sized unsigned integer |
| `f32` | `float` | 32-bit IEEE 754 float |
| `f64` | `double` | 64-bit IEEE 754 float |
| `bool` | `bool` (C99) / `_Bool` | Requires `#[repr(C)]` |
| `char` | `uint32_t` | Unicode scalar value |
| `*mut T` | `T*` | Mutable pointer |
| `*const T` | `const T*` | Const pointer |
| `&T` | `const T*` | Reference (unsafe to pass) |
| `&mut T` | `T*` | Mutable reference (unsafe to pass) |
| `[T; N]` | `T[N]` | Fixed-size array |
| `Option<fn()>` | `void (*fn)()` | Nullable function pointer |
| `extern "C" fn()` | `void (*fn)()` | C calling convention |
| `()` | `void` | Unit type |
| `!` | `noreturn` (C11) | Never type |

### 3.2 Transparent Types

For types passed directly between Rust and C:

```rust
/// Point structure with C-compatible layout
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

/// Rectangle with C-compatible layout
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Rect {
    pub top_left: Point,
    pub bottom_right: Point,
}

/// Color with explicit field ordering
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Color {
    pub r: u8,
    pub g: u8,
    pub b: u8,
    pub a: u8,
}

/// Tagged union for type-safe polymorphism
#[repr(C)]
pub union ValueUnion {
    pub int_val: i64,
    pub float_val: f64,
    pub ptr_val: *mut c_void,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Value {
    pub tag: ValueTag,
    pub data: ValueUnion,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ValueTag {
    Integer = 1,
    Float = 2,
    Pointer = 3,
    Null = 0,
}

#[no_mangle]
pub extern "C" fn value_new_int(val: i64) -> Value {
    Value {
        tag: ValueTag::Integer,
        data: ValueUnion { int_val: val },
    }
}

#[no_mangle]
pub extern "C" fn value_get_int(val: &Value) -> i64 {
    if val.tag == ValueTag::Integer {
        unsafe { val.data.int_val }
    } else {
        0
    }
}
```

### 3.3 Opaque Types

For hiding implementation details:

```rust
/// Opaque type - only usable through pointers
pub struct InternalData {
    // Private fields
    buffer: Vec<u8>,
    metadata: HashMap<String, String>,
    callbacks: Vec<Box<dyn Fn() + Send>>,
}

/// Forward-declared opaque type for C
#[repr(C)]
pub struct OpaqueData {
    _private: [u8; 0], // Ensures proper size for opaque type
}

impl OpaqueData {
    /// Converts to internal type
    fn from_ptr(ptr: *mut OpaqueData) -> Option<&'static mut InternalData> {
        if ptr.is_null() {
            return None;
        }
        // SAFETY: The pointer was created from Box<InternalData>
        Some(unsafe { &mut *(ptr as *mut InternalData) })
    }
}

#[no_mangle]
pub extern "C" fn opaque_data_new() -> *mut OpaqueData {
    let data = Box::new(InternalData {
        buffer: Vec::new(),
        metadata: HashMap::new(),
        callbacks: Vec::new(),
    });
    Box::into_raw(data) as *mut OpaqueData
}

#[no_mangle]
pub unsafe extern "C" fn opaque_data_free(ptr: *mut OpaqueData) {
    if !ptr.is_null() {
        unsafe {
            drop(Box::from_raw(ptr as *mut InternalData));
        }
    }
}
```

### 3.4 String Handling

```rust
use std::ffi::{CStr, CString, NulError};
use std::os::raw::c_char;

/// Converts a Rust string to a C string.
///
/// # Safety
///
/// The returned pointer must be freed with `rust_string_free`.
#[no_mangle]
pub extern "C" fn rust_string_new(rust_str: *const c_char) -> *mut c_char {
    if rust_str.is_null() {
        return std::ptr::null_mut();
    }

    unsafe {
        let c_str = CStr::from_ptr(rust_str);
        match CString::new(c_str.to_bytes()) {
            Ok(new_cstring) => new_cstring.into_raw(),
            Err(_) => std::ptr::null_mut(),
        }
    }
}

/// Frees a string allocated by Rust.
///
/// # Safety
///
/// `ptr` must have been allocated by `rust_string_new` and not yet freed.
#[no_mangle]
pub unsafe extern "C" fn rust_string_free(ptr: *mut c_char) {
    if !ptr.is_null() {
        unsafe {
            drop(CString::from_raw(ptr));
        }
    }
}

/// Gets the length of a C string safely.
#[no_mangle]
pub unsafe extern "C" fn rust_string_len(ptr: *const c_char) -> usize {
    if ptr.is_null() {
        return 0;
    }
    unsafe {
        CStr::from_ptr(ptr).to_bytes().len()
    }
}

/// Creates a Rust string from a byte slice (handles interior nulls).
///
/// # Safety
///
/// `ptr` must point to valid memory of at least `len` bytes.
#[no_mangle]
pub unsafe extern "C" fn rust_string_from_bytes(
    ptr: *const u8,
    len: usize,
) -> *mut c_char {
    if ptr.is_null() {
        return std::ptr::null_mut();
    }

    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };

    // Replace interior nulls with spaces
    let cleaned: Vec<u8> = bytes.iter()
        .map(|&b| if b == 0 { b' ' } else { b })
        .collect();

    match CString::new(cleaned) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}
```

### 3.5 Slice Types

```rust
use std::os::raw::c_void;
use std::slice;

/// C-compatible slice type
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ByteSlice {
    pub ptr: *const u8,
    pub len: usize,
}

impl ByteSlice {
    /// Converts to a Rust slice
    ///
    /// # Safety
    ///
    /// The pointer must be valid for the specified length
    pub unsafe fn as_slice(&self) -> Option<&[u8]> {
        if self.ptr.is_null() && self.len > 0 {
            return None;
        }
        Some(unsafe { slice::from_raw_parts(self.ptr, self.len) })
    }
}

/// Mutable slice type
#[repr(C)]
#[derive(Clone, Copy)]
pub struct MutByteSlice {
    pub ptr: *mut u8,
    pub len: usize,
}

impl MutByteSlice {
    /// Converts to a mutable Rust slice
    ///
    /// # Safety
    ///
    /// The pointer must be valid for the specified length and not aliased
    pub unsafe fn as_mut_slice(&self) -> Option<&mut [u8]> {
        if self.ptr.is_null() && self.len > 0 {
            return None;
        }
        Some(unsafe { slice::from_raw_parts_mut(self.ptr, self.len) })
    }
}

/// Copies data between slices
///
/// # Safety
///
/// Both slices must point to valid memory
#[no_mangle]
pub unsafe extern "C" fn slice_copy(
    src: ByteSlice,
    dst: MutByteSlice,
) -> usize {
    let src = match unsafe { src.as_slice() } {
        Some(s) => s,
        None => return 0,
    };
    let dst = match unsafe { dst.as_mut_slice() } {
        Some(s) => s,
        None => return 0,
    };

    let len = src.len().min(dst.len());
    dst[..len].copy_from_slice(&src[..len]);
    len
}
```

---

## 4. Panic Safety

### 4.1 The Panic Problem

**Theorem FFI-PANIC-SAFETY**:
> Panics unwinding across the FFI boundary into foreign code constitute **undefined behavior**.

```rust
// This is UNDEFINED BEHAVIOR if called from C:
#[no_mangle]
pub extern "C" fn might_panic() {
    let v = vec![1, 2, 3];
    // If this panics, the unwind goes into C - UB!
    v[10]; // panic: index out of bounds
}
```

### 4.2 The Solution: catch_unwind

```rust
use std::ffi::c_void;
use std::os::raw::{c_char, c_int};
use std::panic::{self, AssertUnwindSafe};

/// Error codes for FFI operations
pub const FFI_OK: c_int = 0;
pub const FFI_ERROR_NULL_POINTER: c_int = -1;
pub const FFI_ERROR_PANIC: c_int = -2;
pub const FFI_ERROR_INVALID_ARGUMENT: c_int = -3;

/// Result type for FFI operations
#[repr(C)]
pub struct FfiResult<T> {
    pub value: T,
    pub error_code: c_int,
    pub error_message: *const c_char,
}

/// Catches panics and converts them to error codes.
fn ffi_catch_unwind<F, T>(f: F) -> FfiResult<T>
where
    F: FnOnce() -> Result<T, c_int>,
    T: Default,
{
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(Ok(value)) => FfiResult {
            value,
            error_code: FFI_OK,
            error_message: std::ptr::null(),
        },
        Ok(Err(code)) => FfiResult {
            value: T::default(),
            error_code: code,
            error_message: std::ptr::null(),
        },
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                *s
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.as_str()
            } else {
                "Unknown panic"
            };

            // Leak a CString to return the message
            let c_msg = CString::new(msg).unwrap_or_default();
            let msg_ptr = c_msg.into_raw() as *const c_char;

            FfiResult {
                value: T::default(),
                error_code: FFI_ERROR_PANIC,
                error_message: msg_ptr,
            }
        }
    }
}

/// Panic-safe wrapper for operations
#[no_mangle]
pub extern "C" fn safe_operation(input: c_int) -> FfiResult<c_int> {
    ffi_catch_unwind(|| {
        if input < 0 {
            return Err(FFI_ERROR_INVALID_ARGUMENT);
        }

        // This could panic, but it's caught
        let vec: Vec<i32> = (0..input).collect();
        let sum: i32 = vec.iter().sum();

        Ok(sum)
    })
}
```

### 4.3 Abort-on-Panic Strategy

For simpler cases, aborting may be preferred:

```rust
use std::panic;

/// Configure the runtime to abort on panic.
/// Call this during initialization.
#[no_mangle]
pub extern "C" fn configure_panic_behavior() {
    panic::set_hook(Box::new(|_info| {
        // Log the panic if possible
        eprintln!("Fatal error: panic in FFI code");
        std::process::abort();
    }));
}
```

### 4.4 Panic-Safe Data Structures

```rust
use std::sync::PoisonError;

/// Wrapper that provides panic-safe access
pub struct PanicSafeGuard<T> {
    inner: T,
}

impl<T> PanicSafeGuard<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }

    /// Access with automatic recovery from poisoned state
    pub fn access<F, R>(&self, f: F) -> Result<R, ()>
    where
        F: FnOnce(&T) -> R,
    {
        // For Mutex, we'd need to handle PoisonError
        Ok(f(&self.inner))
    }
}

/// Poison-resistant mutex wrapper
pub struct RobustMutex<T> {
    inner: std::sync::Mutex<T>,
}

impl<T> RobustMutex<T> {
    pub fn new(value: T) -> Self {
        Self {
            inner: std::sync::Mutex::new(value),
        }
    }

    /// Lock that auto-recovers from poison
    pub fn lock(&self) -> std::sync::MutexGuard<T> {
        match self.inner.lock() {
            Ok(guard) => guard,
            Err(poisoned) => {
                // Recover from poison - the data might be inconsistent
                // but we can still access it
                poisoned.into_inner()
            }
        }
    }
}
```

**Theorem FFI-PANIC-RECOVERY**:
> A panic-safe FFI boundary must either:
>
> 1. Catch all panics before they cross the boundary, or
> 2. Abort the process to prevent undefined behavior

---

## 5. Counter-Examples and Anti-Patterns

This section presents common mistakes when working with FFI. Each example demonstrates a problem, its consequences, and the correct solution.

### 5.1 Counter-Example 1: Use After Free

**The Problem:**

```rust
// ANTI-PATTERN: Use after free
#[no_mangle]
pub unsafe extern "C" fn bad_use_after_free() {
    let ptr = create_data();      // Allocate
    free_data(ptr);                // Free
    let x = (*ptr).value;          // USE AFTER FREE - Undefined Behavior!
}
```

**The Consequence:**

- Memory corruption
- Potential security vulnerability (use-after-free exploit)
- Undefined behavior - may appear to work in testing

**The Solution:**

```rust
// CORRECT: Invalidate pointer after free
#[no_mangle]
pub unsafe extern "C" fn good_lifetime_management() {
    let ptr = create_data();
    // ... use ptr ...
    free_data(ptr);
    ptr = std::ptr::null_mut(); // Invalidate
    // Any use of ptr is now obviously wrong
}
```

### 5.2 Counter-Example 2: Dangling Pointer Return

**The Problem:**

```rust
// ANTI-PATTERN: Returning pointer to local
#[no_mangle]
pub extern "C" fn bad_dangling_return() -> *const i32 {
    let local = 42;
    &local as *const i32 // Returns dangling pointer to stack variable
} // local is dropped here
```

**The Consequence:**

- Pointer points to reclaimed stack memory
- Silent data corruption or crashes

**The Solution:**

```rust
// CORRECT: Use Box for heap allocation
#[no_mangle]
pub extern "C" fn good_heap_return() -> *mut i32 {
    Box::into_raw(Box::new(42))
}

// CORRECT: Use static for truly global data
static GLOBAL_VALUE: i32 = 42;

#[no_mangle]
pub extern "C" fn good_static_return() -> *const i32 {
    &GLOBAL_VALUE
}

// CORRECT: Pass buffer from caller
#[no_mangle]
pub unsafe extern "C" fn good_caller_provided(
    out_ptr: *mut i32
) -> c_int {
    if out_ptr.is_null() {
        return -1;
    }
    unsafe { *out_ptr = 42; }
    0
}
```

### 5.3 Counter-Example 3: Null Pointer Dereference

**The Problem:**

```rust
// ANTI-PATTERN: No null check
#[no_mangle]
pub unsafe extern "C" fn bad_null_deref(ptr: *mut Data) {
    (*ptr).value = 42; // Crashes if ptr is null
}
```

**The Consequence:**

- Segmentation fault / access violation
- Denial of service

**The Solution:**

```rust
// CORRECT: Always check for null
#[no_mangle]
pub unsafe extern "C" fn good_null_check(ptr: *mut Data) -> c_int {
    if ptr.is_null() {
        return -1; // Error: null pointer
    }
    unsafe { (*ptr).value = 42; }
    0
}

// CORRECT: Using Option for explicit null handling
#[no_mangle]
pub unsafe extern "C" fn good_optional_pointer(
    ptr: Option<NonNull<Data>>
) -> c_int {
    match ptr {
        Some(p) => {
            unsafe { p.as_mut().value = 42; }
            0
        }
        None => -1,
    }
}
```

### 5.4 Counter-Example 4: Uninitialized Memory

**The Problem:**

```rust
// ANTI-PATTERN: Reading uninitialized memory
#[no_mangle]
pub unsafe extern "C" fn bad_uninitialized() -> i32 {
    let mut value: i32;
    // value is uninitialized!
    return value; // Returns garbage - undefined behavior
}
```

**The Consequence:**

- Undefined behavior - compiler may optimize unpredictably
- Information disclosure (reading sensitive stack data)

**The Solution:**

```rust
// CORRECT: Initialize before use
#[no_mangle]
pub extern "C" fn good_initialized() -> i32 {
    let value: i32 = 0; // Always initialize
    value
}

// CORRECT: MaybeUninit for complex cases
use std::mem::MaybeUninit;

#[no_mangle]
pub unsafe extern "C" fn good_maybe_uninit() -> Data {
    let mut data = MaybeUninit::<Data>::uninit();
    // ... initialize through pointer ...
    unsafe { data.assume_init() }
}
```

### 5.5 Counter-Example 5: Invalid Enum Value

**The Problem:**

```rust
#[repr(C)]
#[derive(Clone, Copy)]
pub enum Status {
    Ok = 0,
    Error = 1,
    Warning = 2,
}

// ANTI-PATTERN: No validation of enum value
#[no_mangle]
pub unsafe extern "C" fn bad_enum_value(status: Status) {
    match status {
        Status::Ok => println!("OK"),
        Status::Error => println!("Error"),
        Status::Warning => println!("Warning"),
        // Missing _ => makes this UB if invalid value passed!
    }
}
```

**The Consequence:**

- Undefined behavior on invalid enum value
- Potential security vulnerability

**The Solution:**

```rust
// CORRECT: Validate enum values
#[no_mangle]
pub unsafe extern "C" fn good_enum_value(status: u32) -> c_int {
    match status {
        0 => { /* Ok */ 0 }
        1 => { /* Error */ 1 }
        2 => { /* Warning */ 2 }
        _ => -1, // Invalid value
    }
}

// CORRECT: Use integer with constants
pub const STATUS_OK: u32 = 0;
pub const STATUS_ERROR: u32 = 1;
pub const STATUS_WARNING: u32 = 2;

#[no_mangle]
pub unsafe extern "C" fn good_int_status(status: u32) -> c_int {
    if status > 2 {
        return -1;
    }
    // Process valid status
    0
}
```

### 5.6 Counter-Example 6: String Without Null Terminator

**The Problem:**

```rust
// ANTI-PATTERN: Treating any byte array as C string
#[no_mangle]
pub unsafe extern "C" fn bad_string_handling(
    bytes: *const u8,
    len: usize,
) -> *const c_char {
    // Assuming bytes is a null-terminated string
    CStr::from_ptr(bytes as *const c_char) // May read past buffer!
}
```

**The Consequence:**

- Buffer over-read
- Information disclosure
- Crash if no null terminator in accessible memory

**The Solution:**

```rust
// CORRECT: Explicit length handling
#[no_mangle]
pub unsafe extern "C" fn good_string_handling(
    bytes: *const u8,
    len: usize,
) -> *mut c_char {
    if bytes.is_null() {
        return std::ptr::null_mut();
    }

    let slice = unsafe { std::slice::from_raw_parts(bytes, len) };

    // Check for interior nulls
    match CString::new(slice) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

// CORRECT: Use Rust strings internally, convert at boundary
#[no_mangle]
pub unsafe extern "C" fn good_string_conversion(
    c_str: *const c_char,
) -> *mut c_char {
    if c_str.is_null() {
        return std::ptr::null_mut();
    }

    let rust_str = unsafe { CStr::from_ptr(c_str) }
        .to_str()
        .unwrap_or("invalid utf8");

    // Process...
    let result = format!("Processed: {}", rust_str);

    match CString::new(result) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}
```

### 5.7 Counter-Example 7: Slice Length Mismatch

**The Problem:**

```rust
// ANTI-PATTERN: Trusting caller-provided length
#[no_mangle]
pub unsafe extern "C" fn bad_slice_handling(
    ptr: *const i32,
    len: usize,
) -> i32 {
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    slice.iter().sum() // May access invalid memory if len is wrong!
}
```

**The Consequence:**

- Buffer over-read if len is too large
- Wrong results if len is too small
- Potential segfault

**The Solution:**

```rust
// CORRECT: Validate pointer and use safe operations
#[no_mangle]
pub unsafe extern "C" fn good_slice_handling(
    ptr: *const i32,
    len: usize,
) -> i64 {
    if ptr.is_null() {
        return 0;
    }

    // Limit maximum size to prevent excessive allocation
    const MAX_LEN: usize = 1_000_000;
    let len = len.min(MAX_LEN);

    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    slice.iter().map(|&x| x as i64).sum()
}
```

### 5.8 Counter-Example 8: Panic Across Boundary

**The Problem:**

```rust
// ANTI-PATTERN: Uncontrolled panic
#[no_mangle]
pub extern "C" fn bad_panic_boundary() {
    let v = vec![1, 2, 3];
    println!("{}", v[10]); // Panic crosses into C - Undefined Behavior!
}
```

**The Consequence:**

- Undefined behavior
- Stack unwinding into foreign code
- Potential resource leaks

**The Solution:**

```rust
// CORRECT: Catch panics at boundary
use std::panic::catch_unwind;

#[no_mangle]
pub extern "C" fn good_panic_safety() -> c_int {
    match catch_unwind(|| {
        let v = vec![1, 2, 3];
        v[10] // This panic is caught
    }) {
        Ok(_) => 0,
        Err(_) => {
            eprintln!("Operation panicked");
            -1
        }
    }
}
```

### 5.9 Counter-Example 9: Thread-Unsafe Data Sharing

**The Problem:**

```rust
use std::cell::RefCell;

// ANTI-PATTERN: Non-Sync type shared across threads
thread_local! {
    static BAD_GLOBAL: RefCell<i32> = RefCell::new(0);
}

#[no_mangle]
pub extern "C" fn bad_thread_access() -> i32 {
    BAD_GLOBAL.with(|g| {
        *g.borrow_mut() += 1; // Data race if called from multiple threads!
        *g.borrow()
    })
}
```

**The Consequence:**

- Data races
- Memory corruption
- Undefined behavior

**The Solution:**

```rust
// CORRECT: Use thread-safe types
use std::sync::atomic::{AtomicI32, Ordering};

static GOOD_GLOBAL: AtomicI32 = AtomicI32::new(0);

#[no_mangle]
pub extern "C" fn good_thread_access() -> i32 {
    GOOD_GLOBAL.fetch_add(1, Ordering::SeqCst) + 1
}

// CORRECT: Use Mutex for complex types
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref PROTECTED_DATA: Mutex<Vec<i32>> = Mutex::new(Vec::new());
}

#[no_mangle]
pub extern "C" fn good_mutex_access(value: i32) -> usize {
    let mut data = PROTECTED_DATA.lock().unwrap();
    data.push(value);
    data.len()
}
```

### 5.10 Counter-Example 10: Mutable Aliasing

**The Problem:**

```rust
// ANTI-PATTERN: Creating mutable aliases
#[no_mangle]
pub unsafe extern "C" fn bad_mutable_alias(ptr: *mut Data) {
    let ref1 = unsafe { &mut *ptr };
    let ref2 = unsafe { &mut *ptr }; // Two mutable borrows! UB!
    ref1.value = 1;
    ref2.value = 2; // Aliasing violation
}
```

**The Consequence:**

- Violates Rust's aliasing rules
- Undefined behavior
- Misoptimization by compiler

**The Solution:**

```rust
// CORRECT: No aliasing through raw pointers
#[no_mangle]
pub unsafe extern "C" fn good_no_alias(ptr: *mut Data) {
    if ptr.is_null() { return; }

    unsafe {
        (*ptr).value = 42; // Single access
    }
}

// CORRECT: Use raw pointer arithmetic for multiple accesses
#[no_mangle]
pub unsafe extern "C" fn good_array_access(
    ptr: *mut i32,
    len: usize,
    index: usize,
    value: i32,
) -> c_int {
    if ptr.is_null() || index >= len {
        return -1;
    }

    unsafe {
        ptr.add(index).write(value);
    }
    0
}
```

### 5.11 Counter-Example 11: Incorrect ABI

**The Problem:**

```rust
// ANTI-PATTERN: Wrong calling convention
#[no_mangle]
pub extern "stdcall" fn bad_abi_windows(x: i32) -> i32 {
    x * 2
}

// C declares it as:
// int bad_abi_windows(int x); // cdecl, not stdcall!
```

**The Consequence:**

- Stack corruption
- Wrong parameter/return values
- Crash on function return

**The Solution:**

```rust
// CORRECT: Match the ABI on both sides
// Rust:
#[no_mangle]
pub extern "C" fn good_abi_cdecl(x: i32) -> i32 {
    x * 2
}

// C:
// int good_abi_cdecl(int x); // Default cdecl matches extern "C"

// For Windows API:
#[cfg(windows)]
#[no_mangle]
pub extern "system" fn good_abi_windows(hwnd: HWND, msg: UINT) -> LRESULT {
    // "system" is stdcall on 32-bit Windows, C on 64-bit
    0
}
```

### 5.12 Counter-Example 12: Struct Layout Mismatch

**The Problem:**

```rust
// Rust side - no repr(C)
pub struct Point {
    pub x: f64,
    pub y: f64,
}

#[no_mangle]
pub extern "C" fn process_point(p: Point) -> f64 {
    p.x + p.y
}
```

```c
// C side
typedef struct {
    double x;
    double y;
} Point;

double process_point(Point p); // Layout likely differs!
```

**The Consequence:**

- Wrong field offsets
- Reading garbage data
- Memory corruption

**The Solution:**

```rust
// CORRECT: Explicit C repr
#[repr(C)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

// CORRECT: Also for packed structs
#[repr(C, packed)]
pub struct PackedHeader {
    pub magic: u16,
    pub version: u8,
    pub flags: u8,
}

// CORRECT: Explicit alignment
#[repr(C, align(16))]
pub struct AlignedData {
    pub value: u64,
}
```

### 5.13 Counter-Example 13: Bitfield Handling

**The Problem:**

```rust
// ANTI-PATTERN: Assuming bit layout matches C
#[repr(C)]
pub struct BadBitfield {
    pub flags: u8, // Trying to use as bitfield
}
```

```c
// C side
typedef struct {
    unsigned int flag1 : 1;
    unsigned int flag2 : 1;
    unsigned int reserved : 6;
} Bitfield;
```

**The Consequence:**

- Bit layout differences between compilers
- Wrong values extracted

**The Solution:**

```rust
// CORRECT: Manual bit manipulation
#[repr(C)]
pub struct GoodBitfield {
    pub data: u8,
}

impl GoodBitfield {
    pub const FLAG1_MASK: u8 = 0b0000_0001;
    pub const FLAG2_MASK: u8 = 0b0000_0010;

    pub fn flag1(&self) -> bool {
        self.data & Self::FLAG1_MASK != 0
    }

    pub fn set_flag1(&mut self, value: bool) {
        if value {
            self.data |= Self::FLAG1_MASK;
        } else {
            self.data &= !Self::FLAG1_MASK;
        }
    }
}

// CORRECT: Using bitfield crate
use bitfield::bitfield;

bitfield! {
    #[repr(C)]
    pub struct StatusRegister(u16);
    impl Debug;
    pub bool, enable, set_enable: 0;
    pub bool, interrupt, set_interrupt: 1;
    pub u8, priority, set_priority: 3, 2;
}
```

### 5.14 Counter-Example 14: Callback Lifetime

**The Problem:**

```rust
// ANTI-PATTERN: Storing callback without lifetime tracking
type Callback = extern "C" fn(i32) -> i32;

static mut CALLBACK: Option<Callback> = None;

#[no_mangle]
pub extern "C" fn register_callback(cb: Callback) {
    unsafe {
        CALLBACK = Some(cb); // What if cb's code is unloaded?
    }
}

#[no_mangle]
pub extern "C" fn trigger_callback(x: i32) -> i32 {
    unsafe {
        match CALLBACK {
            Some(cb) => cb(x), // May call into unloaded memory!
            None => 0,
        }
    }
}
```

**The Consequence:**

- Calling code that has been unloaded
- Segmentation fault
- Security vulnerability

**The Solution:**

```rust
// CORRECT: Track callback validity
use std::sync::atomic::{AtomicBool, Ordering};

static CALLBACK_VALID: AtomicBool = AtomicBool::new(false);
static mut CALLBACK: Option<Callback> = None;

#[no_mangle]
pub extern "C" fn register_callback(cb: Callback) {
    unsafe {
        CALLBACK = Some(cb);
        CALLBACK_VALID.store(true, Ordering::SeqCst);
    }
}

#[no_mangle]
pub extern "C" fn unregister_callback() {
    CALLBACK_VALID.store(false, Ordering::SeqCst);
    unsafe {
        CALLBACK = None;
    }
}

#[no_mangle]
pub extern "C" fn trigger_callback(x: i32) -> i32 {
    if !CALLBACK_VALID.load(Ordering::SeqCst) {
        return -1;
    }
    unsafe {
        match CALLBACK {
            Some(cb) => cb(x),
            None => 0,
        }
    }
}

// CORRECT: Use user data pointer for context
#[repr(C)]
pub struct CallbackContext {
    pub callback: extern "C" fn(*mut c_void, i32) -> i32,
    pub user_data: *mut c_void,
}
```

### 5.15 Counter-Example 15: Resource Leak

**The Problem:**

```rust
// ANTI-PATTERN: Allocating without guaranteed free path
#[no_mangle]
pub extern "C" fn bad_resource_leak() -> *mut Data {
    let data = Box::new(Data::new());
    // If C never calls free, this leaks!
    Box::into_raw(data)
}
```

**The Consequence:**

- Memory leaks
- Resource exhaustion
- Poor performance over time

**The Solution:**

```rust
// CORRECT: RAII wrapper for C
#[repr(C)]
pub struct ManagedResource {
    ptr: *mut Data,
}

impl Drop for ManagedResource {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe {
                drop(Box::from_raw(self.ptr));
            }
        }
    }
}

// CORRECT: Reference counting
use std::sync::Arc;

#[no_mangle]
pub extern "C" fn good_ref_counted() -> *mut RefCountedData {
    let arc = Arc::new(Data::new());
    Arc::into_raw(arc) as *mut RefCountedData
}

#[no_mangle]
pub unsafe extern "C" fn good_ref_clone(ptr: *const RefCountedData) -> *mut RefCountedData {
    if ptr.is_null() { return std::ptr::null_mut(); }
    let arc = unsafe { Arc::from_raw(ptr) };
    let new_arc = Arc::clone(&arc);
    // Don't drop the original arc - we just borrowed it
    std::mem::forget(arc);
    Arc::into_raw(new_arc) as *mut RefCountedData
}

#[no_mangle]
pub unsafe extern "C" fn good_ref_release(ptr: *const RefCountedData) {
    if !ptr.is_null() {
        unsafe {
            drop(Arc::from_raw(ptr));
        }
    }
}
```

### 5.16 Counter-Example 16: Integer Overflow in FFI

**The Problem:**

```rust
// ANTI-PATTERN: Silent integer overflow
#[no_mangle]
pub extern "C" fn bad_integer_overflow(a: i32, b: i32) -> i32 {
    a + b // Wraps on overflow
}
```

**The Solution:**

```rust
// CORRECT: Check for overflow
#[no_mangle]
pub extern "C" fn good_checked_add(a: i32, b: i32) -> FfiResult<i32> {
    match a.checked_add(b) {
        Some(result) => FfiResult {
            value: result,
            error_code: FFI_OK,
            error_message: std::ptr::null(),
        },
        None => FfiResult {
            value: 0,
            error_code: -1,
            error_message: "Integer overflow".as_ptr() as *const c_char,
        },
    }
}
```

### 5.17 Counter-Example 17: Data Race in Global State

**The Problem:**

```rust
// ANTI-PATTERN: Unsafe static mut
static mut GLOBAL_COUNTER: i32 = 0;

#[no_mangle]
pub extern "C" fn bad_increment() -> i32 {
    unsafe {
        GLOBAL_COUNTER += 1; // Data race!
        GLOBAL_COUNTER
    }
}
```

**The Solution:**

```rust
// CORRECT: Atomic operations
use std::sync::atomic::{AtomicI32, Ordering};

static GLOBAL_COUNTER: AtomicI32 = AtomicI32::new(0);

#[no_mangle]
pub extern "C" fn good_increment() -> i32 {
    GLOBAL_COUNTER.fetch_add(1, Ordering::SeqCst) + 1
}
```

### 5.18 Counter-Example 18: Double Free

**The Problem:**

```rust
// ANTI-PATTERN: Multiple free paths
#[no_mangle]
pub unsafe extern "C" fn bad_double_free(ptr: *mut Data) {
    if !ptr.is_null() {
        drop(Box::from_raw(ptr));
        // Later in the code...
        drop(Box::from_raw(ptr)); // Double free!
    }
}
```

**The Solution:**

```rust
// CORRECT: Null after free
#[no_mangle]
pub unsafe extern "C" fn good_single_free(ptr: *mut Data) {
    if !ptr.is_null() {
        drop(Box::from_raw(ptr));
        // ptr is now dangling - don't use it again
    }
}

// CORRECT: In C, set to NULL after calling free
// free_data(ptr);
// ptr = NULL; // Good practice
```

### 5.19 Counter-Example 19: Mismatched Drop Order

**The Problem:**

```rust
// ANTI-PATTERN: Wrong destruction order
#[repr(C)]
pub struct ResourcePair {
    pub primary: *mut Data,
    pub secondary: *mut Data,
}

#[no_mangle]
pub unsafe extern "C" fn bad_drop_order(pair: *mut ResourcePair) {
    if !pair.is_null() {
        let p = unsafe { &*pair };
        // secondary may depend on primary!
        unsafe { drop(Box::from_raw(p.primary)); }
        unsafe { drop(Box::from_raw(p.secondary)); } // Use-after-free if dependency!
    }
}
```

**The Solution:**

```rust
// CORRECT: Document and respect dependencies
/// # Safety
///
/// secondary must not depend on primary (no internal references)
#[no_mangle]
pub unsafe extern "C" fn good_independent_drop(pair: *mut ResourcePair) {
    if !pair.is_null() {
        let p = unsafe { &*pair };
        unsafe {
            drop(Box::from_raw(p.secondary));
            drop(Box::from_raw(p.primary));
        }
        drop(Box::from_raw(pair));
    }
}
```

### 5.20 Counter-Example 20: FFI Type Confusion

**The Problem:**

```rust
// ANTI-PATTERN: Type punning through void*
#[no_mangle]
pub extern "C" fn bad_type_confusion(ptr: *mut c_void, type_tag: i32) {
    match type_tag {
        1 => {
            let data = unsafe { &*(ptr as *mut Data) };
        }
        2 => {
            let data = unsafe { &*(ptr as *mut OtherData) }; // Same pointer, different type!
        }
        _ => {}
    }
}
```

**The Solution:**

```rust
// CORRECT: Use tagged union
#[repr(C)]
pub enum DataTag {
    Data = 1,
    OtherData = 2,
}

#[repr(C)]
pub union DataUnion {
    pub data: std::mem::ManuallyDrop<Data>,
    pub other: std::mem::ManuallyDrop<OtherData>,
}

#[repr(C)]
pub struct TaggedData {
    pub tag: DataTag,
    pub data: DataUnion,
}
```

---

## 6. Bindgen and Cbindgen

### 6.1 Bindgen: C to Rust

Bindgen automatically generates Rust FFI bindings from C header files.

**Setup:**

```toml
# Cargo.toml
[build-dependencies]
bindgen = "0.69"
```

```rust
// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    // Tell cargo to invalidate the built crate whenever the wrapper changes
    println!("cargo:rerun-if-changed=wrapper.h");

    // The bindgen::Builder is the main entry point
    let bindings = bindgen::Builder::default()
        // The input header we would like to generate bindings for
        .header("wrapper.h")
        // Tell cargo to invalidate the built crate whenever any of the
        // included header files changed
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        // Customize options
        .derive_debug(true)
        .derive_default(true)
        .impl_debug(true)
        .generate_inline_functions(true)
        // Finish the builder and generate the bindings
        .generate()
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

**Advanced Bindgen Configuration:**

```rust
// build.rs - Advanced configuration
fn main() {
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        // Whitelist specific items
        .allowlist_function("mylib_.*")
        .allowlist_type("MyLib.*")
        .allowlist_var("MYLIB_.*")
        // Blocklist problematic items
        .blocklist_function(".*_internal")
        // Custom types
        .prepend_enum_name(false)
        .default_enum_style(bindgen::EnumVariation::Rust { non_exhaustive: false })
        // Layout tests
        .layout_tests(false)
        // Documentation
        .generate_comments(true)
        // Size_t/isize_t handling
        .size_t_is_usize(true)
        // C++ support
        .enable_cxx_namespaces()
        .clang_args(&["-x", "c++", "-std=c++17"])
        .generate()
        .expect("Unable to generate bindings");
}
```

**Using Generated Bindings:**

```rust
// src/lib.rs
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Safe wrapper around unsafe bindings
pub struct SafeDatabase {
    inner: *mut mylib_database_t,
}

impl SafeDatabase {
    pub fn new(path: &str) -> Option<Self> {
        let c_path = std::ffi::CString::new(path).ok()?;
        let ptr = unsafe { mylib_database_open(c_path.as_ptr()) };
        if ptr.is_null() {
            None
        } else {
            Some(Self { inner: ptr })
        }
    }

    pub fn query(&self, sql: &str) -> Result<Vec<Row>, Error> {
        // Safe wrapper implementation
        todo!()
    }
}

impl Drop for SafeDatabase {
    fn drop(&mut self) {
        unsafe {
            mylib_database_close(self.inner);
        }
    }
}
```

### 6.2 Cbindgen: Rust to C

Cbindgen generates C/C++ headers from Rust source code.

**Configuration:**

```toml
# cbindgen.toml
language = "C"
cpp_compat = true
include_guard = "MY_LIBRARY_H"

[export]
include = ["DataStore", "compute_distance"]
exclude = ["internal_*"]
prefix = "MyLib"

[fn]
rename_types = "PascalCase"

[struct]
rename_fields = "None"

[enum]
rename_variants = "ScreamingSnakeCase"

[parse]
parse_deps = true
include = ["my-crate"]

[documentation]
documentation_style = "c"
```

**Rust Source:**

```rust
// src/lib.rs

/// A data store for user information
#[repr(C)]
pub struct DataStore {
    internal: *mut c_void,
}

/// Error codes for data store operations
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub enum DataStoreError {
    Ok = 0,
    InvalidArgument = 1,
    OutOfMemory = 2,
    IoError = 3,
}

/// Creates a new data store
///
/// # Safety
///
/// The returned pointer must be freed with `datastore_free`
#[no_mangle]
pub extern "C" fn datastore_new() -> DataStore {
    // Implementation
    todo!()
}

/// Frees a data store
///
/// # Safety
///
/// `store` must be a valid pointer from `datastore_new`
#[no_mangle]
pub unsafe extern "C" fn datastore_free(store: *mut DataStore) {
    // Implementation
}
```

**Generated C Header:**

```c
#ifndef MY_LIBRARY_H
#define MY_LIBRARY_H

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/**
 * Error codes for data store operations
 */
typedef enum {
  MYLIB_DATA_STORE_ERROR_OK = 0,
  MYLIB_DATA_STORE_ERROR_INVALID_ARGUMENT = 1,
  MYLIB_DATA_STORE_ERROR_OUT_OF_MEMORY = 2,
  MYLIB_DATA_STORE_ERROR_IO_ERROR = 3,
} MyLibDataStoreError;

/**
 * A data store for user information
 */
typedef struct {
  void *internal;
} MyLibDataStore;

/**
 * Creates a new data store
 *
 * # Safety
 *
 * The returned pointer must be freed with `datastore_free`
 */
MyLibDataStore MyLib_datastore_new(void);

/**
 * Frees a data store
 *
 * # Safety
 *
 * `store` must be a valid pointer from `datastore_new`
 */
void MyLib_datastore_free(MyLibDataStore *store);

#endif /* MY_LIBRARY_H */
```

---

## 7. CXX Crate for Safe C++ Interop

The `cxx` crate provides safe, zero-cost interoperability between Rust and C++.

### 7.1 Basic Setup

```toml
# Cargo.toml
[dependencies]
cxx = "1.0"

[build-dependencies]
cxx-build = "1.0"
```

```rust
// build.rs
fn main() {
    cxx_build::bridge("src/main.rs")
        .file("src/my_cpp_code.cpp")
        .flag_if_supported("-std=c++17")
        .compile("my_rust_cpp_project");
}
```

### 7.2 CXX Bridge

```rust
// src/lib.rs
#[cxx::bridge]
mod ffi {
    // Rust types exposed to C++
    extern "Rust" {
        type MyRustType;

        fn create_rust_type() -> Box<MyRustType>;
        fn process_data(self: &MyRustType, input: &str) -> String;
    }

    // C++ types exposed to Rust
    unsafe extern "C++" {
        include!("my_cpp_code.h");

        type MyCppType;

        fn create_cpp_type() -> UniquePtr<MyCppType>;
        fn get_value(self: Pin<&mut MyCppType>) -> i32;
        fn set_value(self: Pin<&mut MyCppType>, value: i32);
    }
}

// Rust implementation
pub struct MyRustType {
    data: Vec<u8>,
}

fn create_rust_type() -> Box<MyRustType> {
    Box::new(MyRustType { data: Vec::new() })
}

impl MyRustType {
    fn process_data(&self, input: &str) -> String {
        format!("Processed: {}", input)
    }
}
```

### 7.3 Safe String Handling

```rust
#[cxx::bridge]
mod ffi {
    unsafe extern "C++" {
        include!("cxx_helper.h");

        // C++ std::string
        type CxxString;

        fn new_cxx_string() -> UniquePtr<CxxString>;
        fn push_str(string: Pin<&mut CxxString>, s: &str);
        fn to_string(string: &CxxString) -> &str;
    }
}

// Usage
fn use_cxx_string() {
    let mut s = ffi::new_cxx_string();
    ffi::push_str(s.pin_mut(), "Hello");
    ffi::push_str(s.pin_mut(), " World");
    println!("{}", ffi::to_string(&s));
}
```

### 7.4 Safe Vectors

```rust
#[cxx::bridge]
mod ffi {
    unsafe extern "C++" {
        include!("cxx_helper.h");

        // C++ std::vector
        type CxxVector<T>;

        fn create_vector() -> UniquePtr<CxxVector<u8>>;
        fn push_back(vec: Pin<&mut CxxVector<u8>>, value: u8);
        fn get(vec: &CxxVector<u8>, index: usize) -> &u8;
    }
}

// Rust can also expose vectors to C++
#[cxx::bridge]
mod rust_ffi {
    extern "Rust" {
        fn get_data() -> Vec<u8>;
        fn process_vector(data: &Vec<u8>) -> i32;
    }
}
```

### 7.5 Safe Exceptions

```rust
#[cxx::bridge]
mod ffi {
    extern "Rust" {
        fn may_panic() -> Result<String>;
    }

    unsafe extern "C++" {
        fn may_throw() -> Result<String>;
    }
}

fn may_panic() -> Result<String, cxx::Exception> {
    // If this panics, it's caught and converted to an exception
    Ok(some_operation())
}

fn use_cpp() {
    match ffi::may_throw() {
        Ok(s) => println!("Got: {}", s),
        Err(e) => eprintln!("C++ exception: {}", e.what()),
    }
}
```

### 7.6 Shared Types

```rust
#[cxx::bridge]
mod ffi {
    // Shared struct - layout guaranteed compatible
    struct Point {
        x: f64,
        y: f64,
    }

    struct Rectangle {
        top_left: Point,
        bottom_right: Point,
    }

    extern "Rust" {
        fn compute_area(rect: &Rectangle) -> f64;
    }

    unsafe extern "C++" {
        fn is_valid_rect(rect: &Rectangle) -> bool;
    }
}

fn compute_area(rect: &ffi::Rectangle) -> f64 {
    let width = rect.bottom_right.x - rect.top_left.x;
    let height = rect.bottom_right.y - rect.top_left.y;
    width * height
}
```

---

## 8. Case Study: Embedding Python

Complete example of a Python extension module written in Rust using `pyo3`.

### 8.1 Project Setup

```toml
# Cargo.toml
[package]
name = "my_python_module"
crate-type = ["cdylib"]

[dependencies]
pyo3 = { version = "0.20", features = ["extension-module"] }
```

### 8.2 Basic Module Structure

```rust
// src/lib.rs
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};
use pyo3::exceptions::PyValueError;
use std::sync::{Arc, Mutex};

/// A Rust struct exposed to Python
#[pyclass]
struct DataProcessor {
    data: Vec<f64>,
    config: Config,
}

#[pymethods]
impl DataProcessor {
    /// Constructor
    #[new]
    fn new() -> Self {
        Self {
            data: Vec::new(),
            config: Config::default(),
        }
    }

    /// Add a value to the dataset
    fn add_value(&mut self, value: f64) {
        self.data.push(value);
    }

    /// Compute the mean of the data
    fn mean(&self) -> PyResult<f64> {
        if self.data.is_empty() {
            return Err(PyValueError::new_err("No data points"));
        }
        Ok(self.data.iter().sum::<f64>() / self.data.len() as f64)
    }

    /// Compute the standard deviation
    fn std_dev(&self) -> PyResult<f64> {
        if self.data.len() < 2 {
            return Err(PyValueError::new_err("Need at least 2 data points"));
        }
        let mean = self.mean()?;
        let variance = self.data.iter()
            .map(|&x| (x - mean).powi(2))
            .sum::<f64>() / (self.data.len() - 1) as f64;
        Ok(variance.sqrt())
    }

    /// Get the data as a Python list
    fn get_data<'py>(&self, py: Python<'py>) -> Bound<'py, PyList> {
        let list = PyList::empty(py);
        for &value in &self.data {
            list.append(value).unwrap();
        }
        list
    }

    /// Set data from a Python list
    fn set_data(&mut self, data: Vec<f64>) {
        self.data = data;
    }
}

/// Configuration struct
#[pyclass]
#[derive(Clone, Default)]
struct Config {
    #[pyo3(get, set)]
    precision: i32,
    #[pyo3(get, set)]
    enable_logging: bool,
}

#[pymethods]
impl Config {
    #[new]
    fn new() -> Self {
        Self::default()
    }
}

/// Thread-safe processor
#[pyclass]
struct ThreadSafeProcessor {
    inner: Arc<Mutex<DataProcessor>>,
}

#[pymethods]
impl ThreadSafeProcessor {
    #[new]
    fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(DataProcessor::new())),
        }
    }

    fn add_value(&self, value: f64) -> PyResult<()> {
        let mut processor = self.inner.lock()
            .map_err(|_| PyValueError::new_err("Lock poisoned"))?;
        processor.add_value(value);
        Ok(())
    }

    fn mean(&self) -> PyResult<f64> {
        let processor = self.inner.lock()
            .map_err(|_| PyValueError::new_err("Lock poisoned"))?;
        processor.mean()
    }
}

/// Function that accepts Python callbacks
#[pyfunction]
fn process_with_callback(
    data: Vec<f64>,
    callback: &Bound<'_, PyAny>,
) -> PyResult<Vec<f64>> {
    let mut results = Vec::new();

    for value in data {
        // Call Python callback
        let result: f64 = callback.call1((value,))?.extract()?;
        results.push(result);
    }

    Ok(results)
}

/// Function with keyword arguments
#[pyfunction]
#[pyo3(signature = (x, y, *, scale=1.0, offset=0.0))]
fn compute_distance(
    x: f64,
    y: f64,
    scale: f64,
    offset: f64,
) -> f64 {
    (x * x + y * y).sqrt() * scale + offset
}

/// Exception type
pyo3::create_exception!(my_module, ValidationError, pyo3::exceptions::PyException);

/// Module definition
#[pymodule]
fn my_python_module(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<DataProcessor>()?;
    m.add_class::<Config>()?;
    m.add_class::<ThreadSafeProcessor>()?;
    m.add_function(wrap_pyfunction!(process_with_callback, m)?)?;
    m.add_function(wrap_pyfunction!(compute_distance, m)?)?;
    m.add("ValidationError", m.py().get_type::<ValidationError>())?;
    Ok(())
}
```

### 8.3 Python Usage

```python
# Usage example
import my_python_module as mpm

# Create processor
processor = mpm.DataProcessor()
processor.add_value(1.0)
processor.add_value(2.0)
processor.add_value(3.0)

print(f"Mean: {processor.mean()}")
print(f"Std Dev: {processor.std_dev()}")

# Thread-safe version
ts_processor = mpm.ThreadSafeProcessor()
ts_processor.add_value(42.0)

# With callback
def my_callback(x):
    return x * 2

results = mpm.process_with_callback([1, 2, 3], my_callback)
print(results)  # [2, 4, 6]

# Keyword arguments
dist = mpm.compute_distance(3, 4, scale=2.0, offset=1.0)
print(dist)  # 11.0
```

### 8.4 Memory Management in PyO3

```rust
use pyo3::prelude::*;
use std::ffi::CString;

/// Demonstrates proper memory management
#[pyfunction]
fn process_bytes(data: &[u8]) -> PyResult<Vec<u8>> {
    // Rust borrows the bytes from Python - no copy
    // Process...
    let mut result = data.to_vec();
    result.reverse();
    Ok(result)
}

/// Handling strings
#[pyfunction]
fn process_string(input: &str) -> String {
    // Rust gets a &str backed by Python's string
    format!("Hello, {}!", input.to_uppercase())
}

/// Returning owned data
#[pyclass]
struct LargeBuffer {
    data: Vec<u8>,
}

#[pymethods]
impl LargeBuffer {
    #[new]
    fn new(size: usize) -> Self {
        Self {
            data: vec![0u8; size],
        }
    }

    /// Python can access slices without copying
    fn as_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.data)
    }

    /// Or take ownership (move to Python)
    fn into_bytes(self, py: Python) -> Bound<'_, PyBytes> {
        PyBytes::new(py, &self.data)
    }
}

impl Drop for LargeBuffer {
    fn drop(&mut self) {
        println!("LargeBuffer dropped, freeing {} bytes", self.data.len());
    }
}
```

---

## 9. Case Study: Ruby Extensions

Creating Ruby native extensions with Rust using the `rb-sys` crate.

### 9.1 Setup

```toml
# Cargo.toml
[package]
name = "my_ruby_gem"
crate-type = ["cdylib"]

[dependencies]
rb-sys = "0.9"
magnus = { version = "0.6", features = ["full"] }
```

### 9.2 Basic Extension

```rust
// src/lib.rs
use magnus::{
    class, define_module, function, method, prelude::*, wrap, Error, RArray, RHash, RString, Value,
};
use std::cell::RefCell;
use std::sync::{Arc, Mutex};

/// A Rust struct wrapped for Ruby
#[derive(Debug)]
struct RustDataProcessor {
    values: Vec<f64>,
    name: String,
}

impl RustDataProcessor {
    fn new(name: String) -> Self {
        Self {
            values: Vec::new(),
            name,
        }
    }

    fn add(&mut self, value: f64) {
        self.values.push(value);
    }

    fn sum(&self) -> f64 {
        self.values.iter().sum()
    }

    fn average(&self) -> Option<f64> {
        if self.values.is_empty() {
            None
        } else {
            Some(self.sum() / self.values.len() as f64)
        }
    }
}

/// Wrap the Rust struct for Ruby's GC
#[wrap(class = "MyRubyGem::DataProcessor")]
struct DataProcessorWrapper(RefCell<RustDataProcessor>);

impl DataProcessorWrapper {
    fn new(name: String) -> Self {
        Self(RefCell::new(RustDataProcessor::new(name)))
    }

    fn add(&self, value: f64) {
        self.0.borrow_mut().add(value);
    }

    fn sum(&self) -> f64 {
        self.0.borrow().sum()
    }

    fn average(&self) -> Option<f64> {
        self.0.borrow().average()
    }

    fn name(&self) -> String {
        self.0.borrow().name.clone()
    }

    fn to_h(&self) -> RHash {
        let hash = RHash::new();
        let processor = self.0.borrow();
        hash.as_ref().set(
            RString::new("name"),
            RString::new(&processor.name),
        );
        hash.as_ref().set(
            RString::new("count"),
            processor.values.len() as i64,
        );
        hash.as_ref().set(
            RString::new("sum"),
            processor.sum(),
        );
        hash
    }
}

/// Thread-safe counter
#[derive(Debug)]
struct ThreadSafeCounter {
    count: Mutex<i64>,
}

impl ThreadSafeCounter {
    fn new() -> Self {
        Self {
            count: Mutex::new(0),
        }
    }

    fn increment(&self) -> i64 {
        let mut count = self.count.lock().unwrap();
        *count += 1;
        *count
    }

    fn get(&self) -> i64 {
        *self.count.lock().unwrap()
    }
}

#[wrap(class = "MyRubyGem::Counter")]
struct CounterWrapper(Arc<ThreadSafeCounter>);

impl CounterWrapper {
    fn new() -> Self {
        Self(Arc::new(ThreadSafeCounter::new()))
    }

    fn increment(&self) -> i64 {
        self.0.increment()
    }

    fn get(&self) -> i64 {
        self.0.get()
    }
}

/// Functions
fn fibonacci(n: i64) -> i64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn process_array(input: RArray) -> Result<RArray, Error> {
    let output = RArray::new();

    for item in input.each() {
        let item = item?;
        let value: i64 = item.try_convert()?;
        output.push(value * 2)?;
    }

    Ok(output)
}

fn string_reverse(input: String) -> String {
    input.chars().rev().collect()
}

/// Initialize the module
#[magnus::init]
fn init() -> Result<(), Error> {
    let module = define_module("MyRubyGem")?;

    // Define classes
    let data_class = module.define_class("DataProcessor", class::object())?;
    data_class.define_singleton_method("new", function!(DataProcessorWrapper::new, 1))?;
    data_class.define_method("add", method!(DataProcessorWrapper::add, 1))?;
    data_class.define_method("sum", method!(DataProcessorWrapper::sum, 0))?;
    data_class.define_method("average", method!(DataProcessorWrapper::average, 0))?;
    data_class.define_method("name", method!(DataProcessorWrapper::name, 0))?;
    data_class.define_method("to_h", method!(DataProcessorWrapper::to_h, 0))?;

    let counter_class = module.define_class("Counter", class::object())?;
    counter_class.define_singleton_method("new", function!(CounterWrapper::new, 0))?;
    counter_class.define_method("increment", method!(CounterWrapper::increment, 0))?;
    counter_class.define_method("get", method!(CounterWrapper::get, 0))?;

    // Define module functions
    module.define_module_function("fibonacci", function!(fibonacci, 1))?;
    module.define_module_function("process_array", function!(process_array, 1))?;
    module.define_module_function("string_reverse", function!(string_reverse, 1))?;

    Ok(())
}
```

### 9.3 Ruby Usage

```ruby
require 'my_ruby_gem'

# DataProcessor
processor = MyRubyGem::DataProcessor.new("sales")
processor.add(10.5)
processor.add(20.3)
processor.add(15.0)

puts processor.sum      # 45.8
puts processor.average  # 15.2666...
puts processor.name     # "sales"
p processor.to_h        # { "name" => "sales", "count" => 3, "sum" => 45.8 }

# Thread-safe counter
counter = MyRubyGem::Counter.new
puts counter.increment  # 1
puts counter.increment  # 2
puts counter.get        # 2

# Module functions
puts MyRubyGem.fibonacci(20)  # 6765

arr = MyRubyGem.process_array([1, 2, 3, 4, 5])
p arr  # [2, 4, 6, 8, 10]

puts MyRubyGem.string_reverse("hello")  # "olleh"
```

### 9.4 Error Handling

```rust
use magnus::{Error, exception};

/// Custom error type
#[derive(Debug)]
enum MyGemError {
    InvalidInput(String),
    ComputationFailed { reason: String, code: i32 },
}

impl std::fmt::Display for MyGemError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MyGemError::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            MyGemError::ComputationFailed { reason, code } => {
                write!(f, "Computation failed (code {}): {}", code, reason)
            }
        }
    }
}

impl std::error::Error for MyGemError {}

/// Convert to Ruby exception
fn to_ruby_error(e: MyGemError) -> Error {
    match e {
        MyGemError::InvalidInput(_) => {
            Error::new(exception::arg_error(), e.to_string())
        }
        MyGemError::ComputationFailed { .. } => {
            Error::new(exception::runtime_error(), e.to_string())
        }
    }
}

fn risky_operation(input: i64) -> Result<i64, Error> {
    if input < 0 {
        return Err(to_ruby_error(MyGemError::InvalidInput(
            "input must be non-negative".to_string()
        )));
    }

    if input > 1000 {
        return Err(to_ruby_error(MyGemError::ComputationFailed {
            reason: "value too large".to_string(),
            code: 42,
        }));
    }

    Ok(input * 2)
}
```

---

## 10. Case Study: Node.js Native Modules

Creating Node.js native modules with Rust using `napi-rs`.

### 10.1 Setup

```bash
# Using napi-rs CLI
npx @napi-rs/cli new my_node_module
cd my_node_module
```

```toml
# Cargo.toml
[package]
name = "my_node_module"
crate-type = ["cdylib"]

[dependencies]
napi = { version = "2", features = ["full"] }
napi-derive = "2"

[build-dependencies]
napi-build = "2"
```

### 10.2 Basic Module

```rust
// src/lib.rs
use napi::bindgen_prelude::*;
use napi_derive::napi;
use std::sync::{Arc, Mutex};
use std::thread;

/// A struct exported to JavaScript
#[napi]
pub struct DataAnalyzer {
    values: Vec<f64>,
    cache: Option<Cache>,
}

#[napi]
struct Cache {
    mean: f64,
    std_dev: f64,
}

#[napi]
impl DataAnalyzer {
    #[napi(constructor)]
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            cache: None,
        }
    }

    #[napi]
    pub fn add(&mut self, value: f64) {
        self.values.push(value);
        self.cache = None; // Invalidate cache
    }

    #[napi]
    pub fn add_batch(&mut self, values: Vec<f64>) {
        self.values.extend(values);
        self.cache = None;
    }

    #[napi]
    pub fn mean(&mut self) -> Result<f64> {
        if let Some(ref cache) = self.cache {
            return Ok(cache.mean);
        }

        if self.values.is_empty() {
            return Err(Error::from_reason("No values to analyze"));
        }

        let mean = self.values.iter().sum::<f64>() / self.values.len() as f64;
        self.update_cache(mean);
        Ok(mean)
    }

    #[napi]
    pub fn std_dev(&mut self) -> Result<f64> {
        if let Some(ref cache) = self.cache {
            return Ok(cache.std_dev);
        }

        let mean = self.mean()?;
        let variance = self.values.iter()
            .map(|&v| (v - mean).powi(2))
            .sum::<f64>() / self.values.len() as f64;

        let std_dev = variance.sqrt();
        if let Some(ref mut cache) = self.cache {
            cache.std_dev = std_dev;
        }
        Ok(std_dev)
    }

    #[napi(getter)]
    pub fn count(&self) -> u32 {
        self.values.len() as u32
    }

    #[napi]
    pub fn percentile(&self, p: f64) -> Result<f64> {
        if p < 0.0 || p > 100.0 {
            return Err(Error::from_reason("Percentile must be between 0 and 100"));
        }

        if self.values.is_empty() {
            return Err(Error::from_reason("No values"));
        }

        let mut sorted = self.values.clone();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

        let index = ((p / 100.0) * (sorted.len() - 1) as f64) as usize;
        Ok(sorted[index.min(sorted.len() - 1)])
    }

    fn update_cache(&mut self, mean: f64) {
        self.cache = Some(Cache { mean, std_dev: 0.0 });
    }
}

/// Thread-safe counter
#[napi]
pub struct AtomicCounter {
    inner: Arc<Mutex<i64>>,
}

#[napi]
impl AtomicCounter {
    #[napi(constructor)]
    pub fn new(initial: i64) -> Self {
        Self {
            inner: Arc::new(Mutex::new(initial)),
        }
    }

    #[napi]
    pub fn increment(&self) -> i64 {
        let mut count = self.inner.lock().unwrap();
        *count += 1;
        *count
    }

    #[napi]
    pub fn decrement(&self) -> i64 {
        let mut count = self.inner.lock().unwrap();
        *count -= 1;
        *count
    }

    #[napi(getter)]
    pub fn value(&self) -> i64 {
        *self.inner.lock().unwrap()
    }
}

/// Async computation
#[napi]
pub async fn async_compute(data: Vec<f64>) -> Result<f64> {
    // Move to thread pool
    let result = tokio::task::spawn_blocking(move || {
        thread::sleep(std::time::Duration::from_millis(100));
        data.iter().sum::<f64>()
    })
    .await
    .map_err(|e| Error::from_reason(e.to_string()))?;

    Ok(result)
}

/// Stream processing
#[napi]
pub fn stream_process(input: Vec<String>) -> Result<Vec<String>> {
    input
        .into_iter()
        .map(|s| {
            if s.len() > 100 {
                Err(Error::from_reason("String too long"))
            } else {
                Ok(s.to_uppercase())
            }
        })
        .collect()
}

/// Buffer handling
#[napi]
pub fn process_buffer(buffer: Buffer) -> Buffer {
    let mut data = buffer.to_vec();
    data.reverse();
    Buffer::from(data)
}

/// Task with callback (using threadsafe function)
use napi::threadsafe_function::{ThreadsafeFunction, ThreadsafeFunctionCallMode};

#[napi(ts_args_type = "callback: (err: null | Error, result: number) => void")]
pub fn compute_with_callback(
    data: Vec<f64>,
    callback: JsFunction,
) -> Result<()> {
    let tsfn: ThreadsafeFunction<f64> = callback
        .create_threadsafe_function(0, |ctx| {
            ctx.env.create_double(ctx.value).map(|v| vec![v])
        })?;

    thread::spawn(move || {
        let result = data.iter().sum::<f64>();
        tsfn.call(result, ThreadsafeFunctionCallMode::Blocking);
    });

    Ok(())
}

/// External buffer (zero-copy)
#[napi]
pub struct ExternalBuffer {
    data: Vec<u8>,
}

#[napi]
impl ExternalBuffer {
    #[napi(constructor)]
    pub fn new(size: u32) -> Self {
        Self {
            data: vec![0u8; size as usize],
        }
    }

    #[napi]
    pub fn as_buffer<'a>(&'a self, env: Env) -> Result<napi::bindgen_prelude::Buffer> {
        env.create_buffer_with_data(self.data.clone())
            .map(|b| b.into())
    }
}
```

### 10.3 TypeScript Definitions

```typescript
// index.d.ts
export class DataAnalyzer {
  constructor()
  add(value: number): void
  addBatch(values: number[]): void
  mean(): number
  stdDev(): number
  readonly count: number
  percentile(p: number): number
}

export class AtomicCounter {
  constructor(initial: number)
  increment(): number
  decrement(): number
  readonly value: number
}

export class ExternalBuffer {
  constructor(size: number)
  asBuffer(): Buffer
}

export function asyncCompute(data: number[]): Promise<number>
export function streamProcess(input: string[]): string[]
export function processBuffer(buffer: Buffer): Buffer
export function computeWithCallback(
  data: number[],
  callback: (err: null | Error, result: number) => void
): void
```

### 10.4 JavaScript Usage

```javascript
const {
    DataAnalyzer,
    AtomicCounter,
    asyncCompute,
    processBuffer,
    computeWithCallback
} = require('./my_node_module');

// DataAnalyzer
const analyzer = new DataAnalyzer();
analyzer.add(10.5);
analyzer.add(20.3);
analyzer.addBatch([15.0, 25.0, 30.0]);

console.log(analyzer.mean());     // 20.16
console.log(analyzer.stdDev());   // 7.02
console.log(analyzer.count);      // 5
console.log(analyzer.percentile(50));  // 20.3

// AtomicCounter
const counter = new AtomicCounter(100);
console.log(counter.increment());  // 101
console.log(counter.decrement());  // 100
console.log(counter.value);        // 100

// Async
asyncCompute([1, 2, 3, 4, 5]).then(sum => {
    console.log(sum);  // 15
});

// Buffer
const input = Buffer.from('hello world');
const output = processBuffer(input);
console.log(output.toString());  // 'dlrow olleh'

// Callback
computeWithCallback([1, 2, 3, 4, 5], (err, result) => {
    if (err) console.error(err);
    else console.log(result);  // 15
});
```

---

## 11. Advanced Patterns

### 11.1 Object Pools

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::os::raw::c_int;

pub struct ObjectPool<T> {
    available: Arc<Mutex<VecDeque<T>>>,
    create: Box<dyn Fn() -> T + Send>,
    max_size: usize,
}

impl<T> ObjectPool<T> {
    pub fn new<F>(create: F, max_size: usize) -> Self
    where
        F: Fn() -> T + Send + 'static,
    {
        Self {
            available: Arc::new(Mutex::new(VecDeque::new())),
            create: Box::new(create),
            max_size,
        }
    }

    pub fn acquire(&self) -> PooledObject<T> {
        let mut available = self.available.lock().unwrap();
        let obj = available.pop_front().unwrap_or_else(|| (self.create)());

        PooledObject {
            inner: Some(obj),
            pool: Arc::clone(&self.available),
        }
    }
}

pub struct PooledObject<T> {
    inner: Option<T>,
    pool: Arc<Mutex<VecDeque<T>>>,
}

impl<T> std::ops::Deref for PooledObject<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.inner.as_ref().unwrap()
    }
}

impl<T> std::ops::DerefMut for PooledObject<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.as_mut().unwrap()
    }
}

impl<T> Drop for PooledObject<T> {
    fn drop(&mut self) {
        if let Some(obj) = self.inner.take() {
            let mut pool = self.pool.lock().unwrap();
            if pool.len() < pool.capacity() {
                pool.push_back(obj);
            }
            // Otherwise, drop the object
        }
    }
}

// FFI wrapper
pub struct BufferPool {
    pool: ObjectPool<Vec<u8>>,
}

#[no_mangle]
pub extern "C" fn buffer_pool_new(
    buffer_size: usize,
    max_buffers: usize,
) -> *mut BufferPool {
    let pool = BufferPool {
        pool: ObjectPool::new(
            move || vec![0u8; buffer_size],
            max_buffers,
        ),
    };
    Box::into_raw(Box::new(pool))
}
```

### 11.2 Zero-Copy Serialization

```rust
use std::slice;
use std::os::raw::c_char;

/// Zero-copy view of serialized data
#[repr(C)]
pub struct SerializedView {
    data: *const u8,
    len: usize,
    owned: bool,
}

impl SerializedView {
    /// Creates a view from Rust data (no copy)
    pub fn from_slice(data: &[u8]) -> Self {
        Self {
            data: data.as_ptr(),
            len: data.len(),
            owned: false,
        }
    }

    /// Creates an owned copy
    pub fn to_owned(&self) -> Vec<u8> {
        unsafe {
            slice::from_raw_parts(self.data, self.len).to_vec()
        }
    }
}

/// FlatBuffers-style serialization
#[repr(C, packed)]
pub struct MessageHeader {
    magic: u32,
    version: u16,
    type_id: u16,
    payload_offset: u32,
    payload_size: u32,
}

impl MessageHeader {
    pub const MAGIC: u32 = 0x46524944; // "DRIF"

    pub fn validate(&self) -> bool {
        self.magic == Self::MAGIC
    }

    pub fn payload<'a>(&'a self) -> Option<&'a [u8]> {
        if !self.validate() {
            return None;
        }
        let base = self as *const _ as *const u8;
        unsafe {
            let start = base.add(self.payload_offset as usize);
            Some(slice::from_raw_parts(start, self.payload_size as usize))
        }
    }
}
```

### 11.3 Async FFI with Futures

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::sync::Arc;
use std::ffi::c_void;

/// FFI-compatible future handle
pub struct FutureHandle<T> {
    inner: Arc<Mutex<FutureState<T>>>,
}

enum FutureState<T> {
    Pending(Pin<Box<dyn Future<Output = T> + Send>>),
    Ready(T),
    Consumed,
}

impl<T> FutureHandle<T> {
    pub fn new<F>(future: F) -> Self
    where
        F: Future<Output = T> + Send + 'static,
    {
        Self {
            inner: Arc::new(Mutex::new(FutureState::Pending(Box::pin(future)))),
        }
    }

    pub fn poll(&self) -> Option<T> {
        let mut state = self.inner.lock().unwrap();
        match &mut *state {
            FutureState::Pending(fut) => {
                let waker = dummy_waker();
                let mut context = Context::from_waker(&waker);
                match fut.as_mut().poll(&mut context) {
                    Poll::Ready(val) => {
                        *state = FutureState::Ready(val);
                        None // Return on next call
                    }
                    Poll::Pending => None,
                }
            }
            FutureState::Ready(_) => {
                if let FutureState::Ready(val) = std::mem::replace(&mut *state, FutureState::Consumed) {
                    Some(val)
                } else {
                    unreachable!()
                }
            }
            FutureState::Consumed => None,
        }
    }
}

fn dummy_waker() -> std::task::Waker {
    struct Dummy;
    impl std::task::Wake for Dummy {
        fn wake(self: Arc<Self>) {}
    }
    std::task::Waker::from(Arc::new(Dummy))
}

// FFI interface
#[no_mangle]
pub extern "C" fn async_operation_new() -> *mut FutureHandle<i32> {
    let handle = FutureHandle::new(async {
        // Some async work
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        42
    });
    Box::into_raw(Box::new(handle))
}

#[no_mangle]
pub unsafe extern "C" fn async_operation_poll(
    handle: *mut FutureHandle<i32>,
    result: *mut i32,
) -> c_int {
    if handle.is_null() || result.is_null() {
        return -1;
    }

    let handle = unsafe { &*handle };
    match handle.poll() {
        Some(val) => {
            unsafe { *result = val; }
            1 // Ready
        }
        None => 0, // Pending
    }
}

#[no_mangle]
pub unsafe extern "C" fn async_operation_free(handle: *mut FutureHandle<i32>) {
    if !handle.is_null() {
        unsafe { drop(Box::from_raw(handle)); }
    }
}
```

### 11.4 Memory-Mapped I/O

```rust
use std::fs::OpenOptions;
use std::os::raw::c_int;

/// Memory-mapped file for zero-copy I/O
pub struct MmapBuffer {
    mmap: memmap2::MmapMut,
}

#[no_mangle]
pub extern "C" fn mmap_create(path: *const c_char, size: usize) -> *mut MmapBuffer {
    if path.is_null() {
        return std::ptr::null_mut();
    }

    let path_str = unsafe {
        match std::ffi::CStr::from_ptr(path).to_str() {
            Ok(s) => s,
            Err(_) => return std::ptr::null_mut(),
        }
    };

    let file = match OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(path_str)
    {
        Ok(f) => f,
        Err(_) => return std::ptr::null_mut(),
    };

    if let Err(_) = file.set_len(size as u64) {
        return std::ptr::null_mut();
    }

    let mmap = match unsafe { memmap2::MmapMut::map_mut(&file) } {
        Ok(m) => m,
        Err(_) => return std::ptr::null_mut(),
    };

    Box::into_raw(Box::new(MmapBuffer { mmap }))
}

#[no_mangle]
pub unsafe extern "C" fn mmap_as_ptr(buffer: *mut MmapBuffer) -> *mut u8 {
    if buffer.is_null() {
        return std::ptr::null_mut();
    }
    let buffer = unsafe { &*buffer };
    buffer.mmap.as_ptr() as *mut u8
}

#[no_mangle]
pub unsafe extern "C" fn mmap_len(buffer: *const MmapBuffer) -> usize {
    if buffer.is_null() {
        return 0;
    }
    let buffer = unsafe { &*buffer };
    buffer.mmap.len()
}

#[no_mangle]
pub unsafe extern "C" fn mmap_free(buffer: *mut MmapBuffer) {
    if !buffer.is_null() {
        unsafe { drop(Box::from_raw(buffer)); }
    }
}
```

---

## 12. Best Practices Summary

### 12.1 Safety Checklist

- [ ] All FFI functions are marked `unsafe` or have `# Safety` documentation
- [ ] Null pointers are checked before dereferencing
- [ ] Panics are caught at the FFI boundary using `catch_unwind`
- [ ] Structs crossing FFI have `#[repr(C)]`
- [ ] Enums have explicit discriminants and validation
- [ ] Allocated memory has a documented owner and free function
- [ ] Thread-safety is documented and enforced with proper synchronization
- [ ] ABI calling convention matches on both sides
- [ ] Error codes are checked and propagated
- [ ] Slice lengths are validated against pointer validity

### 12.2 Theorems Summary

**Theorem FFI-BOUNDARY-SAFETY**:
> For any FFI boundary crossing, at least one side must be marked `unsafe`, and the safe side bears the burden of proof for all safety invariants.

**Theorem FFI-PANIC-SAFETY**:
> Panics unwinding across the FFI boundary into foreign code constitute undefined behavior.

**Theorem FFI-PANIC-RECOVERY**:
> A panic-safe FFI boundary must either catch all panics before they cross the boundary, or abort the process to prevent undefined behavior.

**Theorem FFI-TYPE-SAFETY**:
> Types crossing FFI boundaries must have identical memory layout and ABI on both sides, verified through `#[repr(C)]` and matching type definitions.

### 12.3 Pattern Selection Guide

| Scenario | Recommended Pattern | Notes |
|----------|-------------------|-------|
| Simple C integration | Rust Allocates/Rust Frees | Full Rust control |
| C codebase integration | C Allocates/C Frees | Match C conventions |
| Shared mutable state | Shared Ownership (Arc<Mutex<T>>) | Thread-safe |
| High-performance buffers | Zero-copy views | Careful lifetime management |
| C++ integration | CXX crate | Type-safe, zero-cost |
| Large C API | Bindgen | Automated binding generation |
| Exposing Rust to C | Cbindgen | Header generation |
| Python extension | PyO3 | Full Python integration |
| Ruby extension | Magnus | Safe Ruby bindings |
| Node.js module | NAPI-RS | Async support |

### 12.4 Common Pitfalls to Avoid

1. **Never** trust pointer arguments without validation
2. **Never** unwind panics across FFI boundaries
3. **Never** assume C and Rust struct layouts match without `#[repr(C)]`
4. **Never** use `&T` or `&mut T` in FFI signatures
5. **Never** forget to document ownership semantics
6. **Never** mix allocators (don't free C-allocated memory with Rust's free)
7. **Never** expose Rust generics directly to FFI
8. **Never** use `Option<T>` where T isn't nullable in C
9. **Never** ignore error return values from FFI functions
10. **Never** create data races with global mutable state

---

## Conclusion

Foreign Function Interface programming in Rust requires careful attention to memory safety, ownership, and the boundary between safe and unsafe code. By following the patterns and avoiding the anti-patterns documented in this chapter, developers can create robust, safe, and performant FFI bindings.

The key principles are:

1. **Document everything** - Safety contracts, ownership, thread-safety
2. **Validate at boundaries** - Check all inputs from foreign code
3. **Contain unsafety** - Keep unsafe blocks as small as possible
4. **Catch panics** - Never let panics cross FFI boundaries
5. **Match types exactly** - Use `#[repr(C)]` and verify layouts
6. **Be explicit about ownership** - Document who allocates and who frees

With these principles in mind, Rust's FFI capabilities enable seamless integration with the vast ecosystem of existing C, C++, and other language libraries while maintaining Rust's memory safety guarantees.

---

*This chapter is part of the Rust Ownership and Decidability documentation series.*
