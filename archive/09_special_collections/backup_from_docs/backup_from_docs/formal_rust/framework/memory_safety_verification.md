# 内存安全验证(Memory Safety Verification)


## 📊 目录

- [1. 目标](#1-目标)
- [2. 不变式](#2-不变式)
- [3. 规则(摘要)](#3-规则摘要)
- [4. Rust示例(安全释放)](#4-rust示例安全释放)
  - [4.1 边界安全示例（切片写入）](#41-边界安全示例切片写入)
  - [4.2 最小 unsafe 边界（经由不变式保护）](#42-最小-unsafe-边界经由不变式保护)
- [5. 定理](#5-定理)
- [6. 工具化](#6-工具化)
- [最小可验证示例(MVE)](#最小可验证示例mve)
  - [MVE-2：FFI 边界与不变式检查（示意）](#mve-2ffi-边界与不变式检查示意)
- [证明义务(Proof Obligations)](#证明义务proof-obligations)
- [形式化证明映射](#形式化证明映射)


- 文档版本: 1.0  
- 创建日期: 2025-01-27  
- 状态: 已完成

## 1. 目标

- 消除悬垂引用、双重释放、越界访问与数据竞争(在安全子集)。

## 2. 不变式

```math
\text{Aliasing} \Rightarrow \text{Immutability} \quad \land \quad \text{Mutability} \Rightarrow \text{Uniqueness}
```

进一步细化：

- 值级不变式：对任意内存位置 p，若存在两个活跃别名 r1, r2，则二者均为只读引用（不可变别名），或仅存在唯一的可变引用 r_mut。
- 作用域不变式：所有借用的生命周期均被其所有者的生命周期上界；超出作用域的引用不可被使用。
- 边界不变式：切片 `&[T]` 与 `&mut [T]` 的边界由构造时刻确定，任意索引访问必须满足 0 ≤ i < len。
- 释放不变式：每个分配恰有一次释放；释放后不得再访问或再次释放（无悬垂、无双重释放）。

## 3. 规则(摘要)

- 借用规则: `&T` 只读别名; `&mut T` 唯一可变
- 生命周期收敛: 所有借用在owner有效期内
- 边界检查: 切片索引、指针算术与原始指针解引用需满足边界与对齐要求
- 零成本抽象约束: 不引入隐藏的别名或延长生命周期的未声明行为

## 4. Rust示例(安全释放)

```rust
struct Resource { buf: Vec<u8> }
impl Resource { fn len(&self) -> usize { self.buf.len() } }
fn use_resource(r: &Resource) -> usize { r.len() }
```

### 4.1 边界安全示例（切片写入）

```rust
fn fill(xs: &mut [u8], v: u8) {
    for x in xs { *x = v; }
}

#[test]
fn slice_fill_ok() {
    let mut buf = vec![0u8; 8];
    fill(&mut buf[..], 7);
    assert!(buf.iter().all(|&b| b == 7));
}
```

### 4.2 最小 unsafe 边界（经由不变式保护）

```rust
pub struct NonNullBuf { ptr: std::ptr::NonNull<u8>, len: usize }

impl NonNullBuf {
    pub fn as_slice(&self) -> &[u8] {
        // 不变式：ptr 指向 len 字节连续内存且对齐；对象拥有只读别名权限
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        // 不变式：当前对象对底层区域拥有唯一可变访问权（无别名）
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}
```

## 5. 定理

- Safety: 遵循借用与生命周期规则的程序不触发UB。
- Bounds: 对切片与指针算术的边界约束在运行期或编译期可被证明满足。
- Uniqueness: 存在可变引用时，不存在并发的其他别名对同一内存位置进行读/写。

## 6. 工具化

- Miri/Valgrind 交叉验证
- 符号执行: 针对边界与释放路径
- IR 检查与 UB 探测：以 `-Z sanitizer`、`-Z miri`、`-C overflow-checks` 等组合执行
- FFI 边界契约：对 `extern "C"` 函数指定所有权/别名/对齐/寿命约束并以注释与测试约束保持一致

## 最小可验证示例(MVE)

```rust
fn sum(xs: &[i32]) -> i32 { xs.iter().copied().sum() }

#[test]
fn borrow_rules_hold() {
    let data = vec![1,2,3];
    let s = sum(&data);
    assert_eq!(s, 6);
    // 编译期禁止可变与不可变混用别名：
    // let r = &data; let m = &mut data; // should not compile
}
```

### MVE-2：FFI 边界与不变式检查（示意）

```rust
#[repr(C)]
pub struct CBuf { data: *mut u8, len: usize }

extern "C" { fn ext_fill(buf: *mut u8, len: usize, v: u8); }

pub fn ffi_fill_safe(buf: &mut [u8], v: u8) {
    // 不变式：buf.as_mut_ptr() 对应的区域唯一可变，长度为 buf.len()
    // 与外部函数协定：ext_fill 对范围 [ptr, ptr+len) 写入且不越界、不保存别名
    unsafe { ext_fill(buf.as_mut_ptr(), buf.len(), v); }
}

#[test]
fn ffi_fill_contract_holds() {
    let mut v = vec![0u8; 4];
    ffi_fill_safe(&mut v, 9);
    assert_eq!(&v, &[9,9,9,9]);
}
```

## 证明义务(Proof Obligations)

- M1: 对切片 `&[T]` 仅存在不可变别名(不变式保持)
- M2: 任何可变借用不存在并发别名(唯一性)
- M3: 生命周期终止前不发生释放(无悬垂)
- M4: 边界访问满足 0 ≤ i < len；指针对齐满足目标类型要求
- M5: unsafe 块仅在局部满足并输出全局可验证不变式；FFI 协定被单元/属性测试覆盖

---

## 形式化证明映射

- 所有权/借用与生命周期：
  - 文档：`formal_rust/language/01_ownership_borrowing/01_formal_ownership_system.md`、`formal_rust/language/21_lifetime_elision_theory.md`
- 类型安全骨架（进展/保持）：
  - Coq：`formal_rust/framework/proofs/coq/type_system_progress_preservation.v`
  - Lean：`formal_rust/framework/proofs/lean/TypeSystem/ProgressPreservation.lean`
