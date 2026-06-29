// [来源: Michael 2004 (Hazard Pointers) / Fraser 2004 (EBR) / crossbeam-epoch]
//! Hazard Pointer / Epoch-Based Reclamation 桥接层
//!
//! 本模块并非从零实现完整 Hazard Pointer 记录表，而是基于成熟库 `crossbeam-epoch`
//! 提供**概念等价的内存回收抽象**：
//!
//! - `pin()`：线程声明“我正在访问共享节点”，对应 Hazard Pointer 的 `protect`。
//! - `Guard` 生命周期结束：自动清除保护，对应 Hazard Pointer 的 `clear`。
//! - `defer_delete` / `retire`：将节点放入待释放列表，直到所有已保护的线程离开当前 epoch。
//!
//! ## 为什么桥接 crossbeam-epoch？
//!
//! 生产级 Hazard Pointer 需要为每个线程维护 hazard 记录列表、扫描退役列表、
//! 处理线程退出等复杂逻辑。`crossbeam-epoch` 实现了这些细节，并提供与 Hazard
//! Pointer 等价的安全保证（无悬垂指针、无 ABA 导致的提前释放）。

pub use crossbeam_epoch::{Atomic, Guard, Owned, Shared, pin};

use std::sync::atomic::Ordering;

/// 基于 `crossbeam-epoch` 的 Hazard Pointer 保护句柄。
///
/// 该结构体是对 `crossbeam_epoch::Guard` 的薄包装，使代码意图更贴近
/// "Hazard Pointer" 概念。
#[derive(Debug)]
pub struct HazardPointer {
    guard: Guard,
}

impl HazardPointer {
    /// 创建一个新的 Hazard Pointer，等价于 `epoch::pin()` 后持有的 Guard。
    pub fn new() -> Self {
        Self {
            guard: crossbeam_epoch::pin(),
        }
    }

    /// 保护给定的共享指针。
    ///
    /// # Safety
    ///
    /// `ptr` 必须指向当前仍在生命周期内的节点（即使它可能已被逻辑删除）。
    pub unsafe fn protect<'a, T>(&self, ptr: Shared<'a, T>) -> Shared<'a, T> {
        // Guard 本身已经 pin 住当前 epoch；返回的 Shared 生命周期与传入指针一致。
        // 在该 epoch 内，ptr 不会被回收。
        ptr
    }

    /// 清除 Hazard Pointer。
    ///
    /// 在 `crossbeam-epoch` 中，Guard 的生命周期结束即自动 unpin；
    /// 此方法显式表达“不再保护任何指针”的语义。
    pub fn clear(self) {
        // Guard 会在 drop 时自动 unpin。
        drop(self.guard);
    }

    /// 访问底层 Guard，用于需要显式 `defer_unchecked` 的场景。
    pub fn guard(&self) -> &Guard {
        &self.guard
    }
}

impl Default for HazardPointer {
    fn default() -> Self {
        Self::new()
    }
}

/// 退役并延迟删除节点。
///
/// # Safety
///
/// `ptr` 必须已经从数据结构中移除，且不再被任何线程访问（除非被 Hazard Pointer / Guard 保护）。
pub unsafe fn defer_delete<T>(guard: &Guard, ptr: Shared<T>) {
    unsafe {
        guard.defer_unchecked(move || {
            let _ = ptr.into_owned();
        });
    }
}

/// 退役节点的类型化包装，用于演示“退役列表”概念。
#[derive(Debug)]
pub struct RetiredNode<'g, T> {
    ptr: Shared<'g, T>,
}

impl<'g, T> RetiredNode<'g, T> {
    /// 创建一条退役记录。
    ///
    /// # Safety
    ///
    /// 同 [`defer_delete`]。
    pub unsafe fn new(ptr: Shared<'g, T>) -> Self {
        Self { ptr }
    }

    /// 在当前 Guard 下安全释放该节点。
    ///
    /// # Safety
    ///
    /// 调用者必须确保没有任何其他线程的 Hazard Pointer 仍指向该节点。
    pub unsafe fn reclaim(self, guard: &Guard) {
        unsafe {
            guard.defer_unchecked(move || {
                let _ = self.ptr.into_owned();
            });
        }
    }
}

/// 读取 `Atomic<T>` 并在当前 Guard 下返回受保护的 `Shared<T>`。
///
/// 这是 Hazard Pointer 使用模式中最常见的操作：先 pin，再 load，再验证。
pub fn load_protected<'g, T>(atomic: &Atomic<T>, guard: &'g Guard) -> Shared<'g, T> {
    atomic.load(Ordering::Acquire, guard)
}

/// 将 `Owned<T>` 发布到共享数据结构。
pub fn publish<T>(owned: Owned<T>, guard: &Guard) -> Shared<'_, T> {
    owned.into_shared(guard)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hazard_pointer_lifecycle() {
        let hp = HazardPointer::new();
        let owned = Owned::new(42);
        let guard = hp.guard();
        let shared = publish(owned, guard);

        unsafe {
            let protected = hp.protect(shared);
            assert_eq!(*protected.deref(), 42);
        }

        hp.clear();
    }

    #[test]
    fn test_defer_delete() {
        let guard = pin();
        let owned = Owned::new(String::from("retire me"));
        let shared = owned.into_shared(&guard);

        unsafe {
            defer_delete(&guard, shared);
        }

        // Guard 离开作用域后会触发 epoch 回收逻辑。
        drop(guard);
    }

    #[test]
    fn test_load_protected() {
        let guard = pin();
        let atomic = Atomic::new(100);
        let shared = load_protected(&atomic, &guard);

        unsafe {
            assert_eq!(*shared.deref(), 100);
        }
    }
}
