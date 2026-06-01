//! Hazard Pointer 实现
//! 的 ABA 问题和安全内存释放问题。
//! ABA problem and memory problem 。
//! ## 核心概念
//! ## core concept
//! - **回收扫描**: 定期检查退役列表中的节点是否可以安全释放
//! - ****: in node can
//! ## 工作流程
//! ## workflow
//! ## process
//! ## 工作process
//! ## workprocess
//! 2. 重新验证指针仍然有效
//! 2. pointer effective
//! 3. 使用完成后清除 Hazard Pointer
//! 3. after Hazard Pointer
//! 4. 需要删除的节点放入退役列表
//! 4. node
use std::collections::VecDeque;
// 使用原始指针而非 NonNull，因为原始指针天然实现 Send + Sync
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock};

/// Hazard Pointer 记录
/// Hazard Pointer record
#[derive(Debug)]
pub struct HazardPointer {
    ptr: AtomicPtr<u8>,
}

impl HazardPointer {
    const fn new() -> Self {
        Self {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    /// 设置 Hazard Pointer
    /// Sets Hazard Pointer
    /// # Safety
    /// 调用者必须确保 ptr 指向有效的内存。
    /// must ptr effective memory 。
    pub unsafe fn protect<T>(&self, ptr: *mut T) {
        self.ptr.store(ptr as *mut u8, Ordering::Release);
    }

    /// 清除 Hazard Pointer
    pub fn clear(&self) {
        self.ptr.store(std::ptr::null_mut(), Ordering::Release);
    }

    /// 获取当前保护的指针
    /// Gets当前保护的指针
    /// when before pointer
    pub fn get(&self) -> *mut u8 {
        self.ptr.load(Ordering::Acquire)
    }
}

/// 线程本地 Hazard Pointer 集合
pub const MAX_HAZARD_POINTERS: usize = 4;

/// 全局 Hazard Pointer 记录
/// global Hazard Pointer record
/// global Hazard Pointer 记录
/// global Hazard Pointer record
pub struct HazardPointerRegistry {
    hazards: RwLock<Vec<*mut HazardPointer>>,
    retired_count: AtomicUsize,
}

// HazardPointerRegistry 使用原始指针是设计上的选择，
// 所有访问都通过 RwLock 保护，因此是线程安全的。
unsafe impl Sync for HazardPointerRegistry {}
unsafe impl Send for HazardPointerRegistry {}

impl Default for HazardPointerRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl HazardPointerRegistry {
    pub const fn new() -> Self {
        Self {
            hazards: RwLock::new(Vec::new()),
            retired_count: AtomicUsize::new(0),
        }
    }

    /// 注册 Hazard Pointer
    pub fn register(&self, hp: *mut HazardPointer) {
        if let Ok(mut guard) = self.hazards.write() {
            guard.push(hp);
        }
    }

    /// 注销 Hazard Pointer
    pub fn unregister(&self, hp: *mut HazardPointer) {
        if let Ok(mut guard) = self.hazards.write() {
            guard.retain(|&p| p != hp);
        }
    }

    pub fn is_protected(&self, ptr: *mut u8) -> bool {
        if let Ok(guard) = self.hazards.read() {
            for &hp in guard.iter() {
                unsafe {
                    if (*hp).get() == ptr {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// 增加退役计数
    /// Increases退役计数
    pub fn increment_retired(&self) {
        self.retired_count.fetch_add(1, Ordering::Relaxed);
    }
}

/// 退役节点记录
/// node
struct RetiredNode {
    ptr: *mut u8,
    deleter: Box<dyn FnOnce(*mut u8) + Send>,
}

/// 内存回收器
/// memory
/// 管理退役节点，在确保安全时释放内存。
/// node ，in memory 。
pub struct MemoryReclaimer {
    retired: Mutex<VecDeque<RetiredNode>>,
    registry: &'static HazardPointerRegistry,
}

impl MemoryReclaimer {
    /// 创建新的内存回收器
    /// Creates新的内存回收器
    /// memory
    pub const fn new(registry: &'static HazardPointerRegistry) -> Self {
        Self {
            retired: Mutex::new(VecDeque::new()),
            registry,
        }
    }

    /// 退役节点
    /// node
    /// 节点不会立即释放，而是加入退役列表等待安全回收。
    /// node ，while etc. 。
    pub fn retire<T>(&self, ptr: *mut T) {
        let deleter = Box::new(|p: *mut u8| unsafe {
            let _ = Box::from_raw(p as *mut T);
        });

        if let Ok(mut guard) = self.retired.lock() {
            guard.push_back(RetiredNode {
                ptr: ptr as *mut u8,
                deleter,
            });
        }
        self.registry.increment_retired();

        // 当退役节点达到一定数量时尝试扫描回收
        if self
            .registry
            .retired_count
            .load(Ordering::Relaxed)
            .is_multiple_of(32)
        {
            self.try_reclaim();
        }
    }

    /// 尝试回收不再被保护的退役节点
    /// Attempts to回收不再被保护的退役节点
    /// is node
    pub fn try_reclaim(&self) {
        let mut to_reclaim = Vec::new();

        if let Ok(mut guard) = self.retired.lock() {
            let mut i = 0;
            while i < guard.len() {
                let node = &guard[i];
                if !self.registry.is_protected(node.ptr) {
                    let node = guard.remove(i).unwrap();
                    to_reclaim.push(node);
                } else {
                    i += 1;
                }
            }
        }

        for node in to_reclaim {
            (node.deleter)(node.ptr);
        }
    }
}

/// 线程本地 Hazard Pointer 上下文
/// thread this Hazard Pointer on under
pub struct ThreadLocalHP {
    hazards: [HazardPointer; MAX_HAZARD_POINTERS],
    registry: &'static HazardPointerRegistry,
}

impl ThreadLocalHP {
    pub const fn new(registry: &'static HazardPointerRegistry) -> Self {
        Self {
            hazards: [
                HazardPointer::new(),
                HazardPointer::new(),
                HazardPointer::new(),
                HazardPointer::new(),
            ],
            registry,
        }
    }

    pub fn hazard(&self, index: usize) -> &HazardPointer {
        assert!(index < MAX_HAZARD_POINTERS);
        &self.hazards[index]
    }

    /// 注册所有 Hazard Pointer
    pub fn register(&self) {
        for hp in &self.hazards {
            self.registry.register(&raw const *hp as *mut HazardPointer);
        }
    }

    /// 注销所有 Hazard Pointer
    pub fn unregister(&self) {
        for hp in &self.hazards {
            self.registry
                .unregister(&raw const *hp as *mut HazardPointer);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    static REGISTRY: HazardPointerRegistry = HazardPointerRegistry::new();

    #[test]
    fn test_hazard_pointer_protect() {
        let hp = HazardPointer::new();
        let data = Box::into_raw(Box::new(42i32));

        unsafe {
            hp.protect(data);
        }
        assert!(!hp.get().is_null());

        hp.clear();
        assert!(hp.get().is_null());

        unsafe {
            let _ = Box::from_raw(data);
        }
    }

    #[test]
    fn test_registry_protection() {
        let tl = ThreadLocalHP::new(&REGISTRY);
        tl.register();

        let data = Box::into_raw(Box::new(42i32));
        unsafe {
            tl.hazard(0).protect(data);
        }

        assert!(REGISTRY.is_protected(data as *mut u8));

        tl.hazard(0).clear();
        tl.unregister();

        unsafe {
            let _ = Box::from_raw(data);
        }
    }

    #[test]
    fn test_memory_reclaimer() {
        let reclaimer = MemoryReclaimer::new(&REGISTRY);
        let tl = ThreadLocalHP::new(&REGISTRY);
        tl.register();

        let data = Box::into_raw(Box::new(42i32));
        reclaimer.retire(data);

        // 由于没有 Hazard Pointer 保护，应该可以回收
        tl.hazard(0).clear();
        reclaimer.try_reclaim();

        tl.unregister();
    }
}
