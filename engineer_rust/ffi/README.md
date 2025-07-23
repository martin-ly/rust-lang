# FFI（Foreign Function Interface）

## 理论基础

- FFI 原理与跨语言调用模型
- ABI（应用二进制接口）与内存布局
- 安全性与未定义行为风险
- 类型映射与数据兼容性

## 工程实践

- Rust FFI 语法（extern、#[repr(C)]、unsafe 等）
- 与 C/C++ 互操作实践
- FFI 绑定生成工具（bindgen、cbindgen 等）
- 内存管理与生命周期协调
- FFI 安全防护与测试

## 形式化要点

- ABI 兼容性的形式化建模
- 类型映射与边界安全的可验证性
- FFI 行为的未定义性分析

## 推进计划

1. 理论基础与 FFI 模型梳理
2. Rust FFI 语法与工具实践
3. 形式化建模与安全验证
4. 跨语言协作与测试集成
5. 推进快照与断点恢复

## 断点快照

- [x] 目录结构与 README 初稿
- [ ] 理论基础与 FFI 模型补全
- [ ] 工程案例与代码片段
- [ ] 形式化建模与验证
- [ ] 交叉引用与持续完善

---

## 深度扩展：理论阐释

### FFI 原理与跨语言调用模型

- FFI（Foreign Function Interface）允许 Rust 与 C/C++/其他语言互操作。
- ABI（应用二进制接口）定义数据布局与调用约定。

### 类型映射与数据兼容性

- #[repr(C)] 保证结构体内存布局兼容 C。
- Rust/C 类型需一一对应，避免未定义行为。

### 安全性与未定义行为风险

- FFI 需手动管理内存、生命周期与线程安全。
- unsafe 代码块需严格边界与审计。

---

## 深度扩展：工程代码片段

### 1. extern "C" 函数导出

```rust
#[no_mangle]
pub extern "C" fn add(a: i32, b: i32) -> i32 { a + b }
```

### 2. C 语言调用 Rust

```c
// C 代码
extern int add(int a, int b);
int r = add(1, 2);
```

### 3. Rust 调用 C 库

```rust
extern "C" { fn c_func(x: i32) -> i32; }
unsafe { c_func(42); }
```

### 4. bindgen 自动生成绑定

```sh
cargo install bindgen
bindgen wrapper.h -o bindings.rs
```

---

## 深度扩展：典型场景案例

### Rust 与 C/C++ 互操作

- 性能敏感模块用 Rust 重写，C/C++ 负责底层驱动。

### 跨平台库集成

- Rust 作为安全高效的 glue 语言集成多语言库。

### FFI 安全防护与测试

- 自动化测试覆盖边界条件，防止未定义行为。

---

## 深度扩展：形式化证明与自动化测试

### 形式化证明思路

- ABI 兼容性建模，自动检测类型与布局不一致。
- unsafe 边界可用 miri 动态检测。

### 自动化测试用例

```rust
#[test]
fn test_add_ffi() {
    assert_eq!(unsafe { add(1, 2) }, 3);
}
```
