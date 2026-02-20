# Rust 版本演进链（1.89–1.93）

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 演进概览

| 版本 | 发布日期 | 主要变更摘要 |
| :--- | :--- | :--- || 1.89 | 2025-08 | 稳定化、性能、错误诊断 |
| 1.90 | 2025-09 | LLD 默认链接器、cargo publish --workspace、平台变更 |
| 1.91 | 2025-10 | aarch64-pc-windows-msvc Tier 1、dangling_pointers_from_locals lint |
| 1.92 | 2025-12 | Never 类型 Lint 严格化、musl 预告、标准库 API |
| 1.93 | 2026-01 | musl 1.2.5、全局分配器 TLS、asm_cfg、大量 API 稳定化、兼容性变更 |

---

## 1.89 → 1.90

**关键变更**:

- **LLD 默认链接器**：`x86_64-unknown-linux-gnu` 默认使用 LLD
- **cargo publish --workspace**：工作区一并发布
- **平台**：`x86_64-apple-darwin` 等平台支持调整

**参考**：[Rust 1.90.0](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)

---

## 1.90 → 1.91

**关键变更**:

- **aarch64-pc-windows-msvc** 升级为 Tier 1
- **dangling_pointers_from_locals** lint（warn-by-default）

**参考**：[Rust 1.91.0](https://blog.rust-lang.org/2025/10/30/Rust-1.91.0/)

---

## 1.91 → 1.92

**关键变更**:

- **Never 类型 Lint**：`never_type_fallback_flowing_into_unsafe`、`dependency_on_unit_never_type_fallback` 从 warn 升级为 deny
- **musl 更新预告**：为 1.93 musl 1.2.5 做准备
- **标准库**：Box::new_zeroed、Rc/Arc::new_zeroed、迭代器特化等

**参考**：[Rust 1.92.0](https://blog.rust-lang.org/2025/12/11/Rust-1.92.0/)

---

## 1.92 → 1.93

**关键变更**:

- **musl 1.2.5**：DNS 解析改进
- **全局分配器**：支持 thread_local
- **asm_cfg**：asm! 行上 cfg
- **API 稳定化**：MaybeUninit、String/Vec raw parts、VecDeque、Duration、char、fmt 等
- **兼容性**：deref_nullptr deny、#[test] 无效位置报错、Emscripten ABI、offset_of 等

**参考**：[05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md)、[06_rust_1.93_compatibility_notes.md](./06_rust_1.93_compatibility_notes.md)

---

## 迁移路径建议

| 当前版本 | 目标 1.93 | 建议 |
| :--- | :--- | :--- || 1.89 | 1.93 | 检查 Never 类型 Lint、deref_nullptr、#[test] |
| 1.90 | 1.93 | 检查 LLD、cargo 变更 |
| 1.91 | 1.93 | 检查平台、dangling_pointers |
| 1.92 | 1.93 | 少量变更，关注兼容性文档 |

---

## 相关文档

- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md)
- [Rust 1.93 完整变更清单](./07_rust_1.93_full_changelog.md)

---

## 演进代码示例

### 版本特性演进示例

```rust
//! Rust 1.89→1.93 版本演进示例代码

/// 1.90 LLD 链接器配置演进
pub mod linker_evolution {
    /// Rust 1.90 之前：使用系统默认链接器
    /// Rust 1.90+：默认使用 LLD（Linux x86_64）
    /// 
    /// .cargo/config.toml 配置演进：
    pub const CARGO_CONFIG_1_90: &str = r#"
# Rust 1.90+ 默认使用 LLD
# 如需回退：
[target.x86_64-unknown-linux-gnu]
linker = "cc"
rustflags = ["-C", "link-arg=-fuse-ld=gold"]
"#;
}

/// 1.91 悬垂指针 lint 演进
pub mod dangling_pointer_lint_evolution {
    /// Rust 1.91 新增 dangling_pointers_from_locals lint (warn-by-default)
    /// 
    /// ❌ 会触发 lint 警告：
    #[allow(dead_code)]
    fn bad_pointer_return() -> *const i32 {
        let x = 42;
        &x as *const i32  // 警告：返回局部变量的指针
    }
    
    /// ✅ 正确做法：
    fn good_pointer_return() -> Box<i32> {
        Box::new(42)
    }
}

/// 1.92 Never 类型 lint 演进
pub mod never_type_lint_evolution {
    /// Rust 1.92 将以下 lint 从 warn 提升为 deny：
    /// - never_type_fallback_flowing_into_unsafe
    /// - dependency_on_unit_never_type_fallback
    
    /// 示例：正确处理 Never 类型
    pub fn handle_never_type(result: Result<i32, !>) -> i32 {
        // 由于 Err 类型是 !，匹配是全面的
        match result {
            Ok(x) => x,
            Err(e) => e, // 这行永远不会执行，但类型检查通过
        }
    }
}

/// 1.93 API 演进示例
pub mod api_evolution {
    use std::collections::VecDeque;
    
    /// 1.93 前：手动实现条件弹出
    pub fn old_pop_front_if<T>(deque: &mut VecDeque<T>, pred: impl Fn(&T) -> bool) -> Option<T> {
        if deque.front().map_or(false, |v| pred(v)) {
            deque.pop_front()
        } else {
            None
        }
    }
    
    /// 1.93+：使用原生 pop_front_if
    pub fn new_pop_front_if<T>(deque: &mut VecDeque<T>) {
        // ✅ 直接使用方法
        let _ = deque.pop_front_if(|&x| x > 0);
    }
}

/// 1.89→1.93 累积变更代码对比
pub mod cumulative_changes {
    use std::mem::MaybeUninit;
    
    /// 1.89：基础 MaybeUninit 使用
    pub fn init_array_1_89() -> [i32; 5] {
        let mut arr: [MaybeUninit<i32>; 5] = unsafe {
            MaybeUninit::uninit().assume_init()
        };
        
        for i in 0..5 {
            arr[i] = MaybeUninit::new(i as i32);
        }
        
        // 需要手动 transmute
        unsafe { std::mem::transmute(arr) }
    }
    
    /// 1.93+：使用新 API 简化
    pub fn init_array_1_93() -> [i32; 5] {
        let src = [0, 1, 2, 3, 4];
        let mut dst = [MaybeUninit::<i32>::uninit(); 5];
        
        // ✅ 使用 write_copy_of_slice
        MaybeUninit::write_copy_of_slice(&mut dst, &src);
        
        unsafe { std::mem::transmute_copy::<_, [i32; 5]>(&dst) }
    }
}
```

### 迁移路径代码示例

```rust
//! 版本迁移辅助代码

/// 检测当前 Rust 版本并执行相应代码
#[macro_export]
macro_rules! version_aware {
    (1.90 => $e190:expr, 1.91 => $e191:expr, 1.92 => $e192:expr, 1.93 => $e193:expr) => {
        {
            #[cfg(rustc_1_90)]
            { $e190 }
            
            #[cfg(rustc_1_91)]
            { $e191 }
            
            #[cfg(rustc_1_92)]
            { $e192 }
            
            #[cfg(rustc_1_93)]
            { $e193 }
            
            #[cfg(not(any(rustc_1_90, rustc_1_91, rustc_1_92, rustc_1_93)))]
            { compile_error!("Unsupported Rust version") }
        }
    };
}

/// 渐进式迁移检查
pub struct MigrationChecker {
    from_version: (u32, u32),
    to_version: (u32, u32),
}

impl MigrationChecker {
    pub fn new(from: (u32, u32), to: (u32, u32)) -> Self {
        Self {
            from_version: from,
            to_version: to,
        }
    }
    
    /// 获取迁移步骤
    pub fn migration_steps(&self) -> Vec<&'static str> {
        let mut steps = Vec::new();
        
        // 1.89 → 1.90
        if self.from_version < (1, 90) && self.to_version >= (1, 90) {
            steps.push("检查 LLD 链接器兼容性");
            steps.push("更新 Cargo.toml 使用 workspace 发布");
        }
        
        // 1.90 → 1.91
        if self.from_version < (1, 91) && self.to_version >= (1, 91) {
            steps.push("修复 dangling_pointers_from_locals 警告");
            steps.push("检查 Windows ARM64 目标支持");
        }
        
        // 1.91 → 1.92
        if self.from_version < (1, 92) && self.to_version >= (1, 92) {
            steps.push("处理 Never 类型 lint 提升");
            steps.push("准备 musl 1.2.5 升级");
        }
        
        // 1.92 → 1.93
        if self.from_version < (1, 93) && self.to_version >= (1, 93) {
            steps.push("修复 deref_nullptr deny lint");
            steps.push("检查 #[test] 属性使用");
            steps.push("升级 libc 到 0.2.146+");
            steps.push("检查 offset_of! 类型约束");
            steps.push("迁移到新 API（MaybeUninit, VecDeque 等）");
        }
        
        steps
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_migration_steps() {
        let checker = MigrationChecker::new((1, 89), (1, 93));
        let steps = checker.migration_steps();
        
        assert!(steps.len() >= 8);
        assert!(steps.iter().any(|s| s.contains("LLD")));
        assert!(steps.iter().any(|s| s.contains("dangling")));
        assert!(steps.iter().any(|s| s.contains("deref_nullptr")));
    }
}
```

---

## 形式化演进参考

### 类型系统演进

| 版本 | 类型系统变更 | 形式化影响 |
| :--- | :--- | :--- |
| 1.90 | LLD 默认 | 无直接类型系统影响 |
| 1.91 | dangling_pointers lint | 加强内存安全形式化保证 |
| 1.92 | Never 类型严格化 | 完善底部类型 (⊥) 处理 |
| 1.93 | LUB coercion 修正 | 改进类型推导形式化 |

### 内存模型演进

- **1.91**: 引入新的内存安全 lint，加强悬垂指针检测
- **1.92**: Never 类型语义进一步明确
- **1.93**: const 求值指针操作支持，扩展编译期计算能力

### 形式化规范参考

- [Ferrocene Specification](https://spec.ferrocene.dev/) - 工业级 Rust 形式化规范
- [Rust Belt](https://plv.mpi-sws.org/rustbelt/) - Rust 形式化验证研究

---

**最后对照 releases.rs**: 2026-02-14
