//! C++ 互操作概念演示
//!
//! `cxx` crate 提供了安全、双向的 C++/Rust 桥接。
//! 核心理念：
//! - Rust 拥有共享结构体的内存安全保证
//! - C++ 只能看到 opaque Rust 类型或共享的 trivial 类型
//! - 自动生成的桥接头文件确保 ABI 兼容

#[cfg(feature = "cxx-interop")]
pub mod cxx_bridge {
    //! 真实的 cxx 桥接需要 `#[cxx::bridge]` 模块和 build.rs 支持。
    //! 此处展示概念性结构。

    /// 由 cxx 生成的共享结构体概念
    #[derive(Debug, Clone, Copy)]
    pub struct SharedPoint {
        /// x 坐标
        pub x: f64,
        /// y 坐标
        pub y: f64,
    }

    /// Opaque C++ 类型概念
    pub enum CppOpaqueType {}
}

#[cfg(not(feature = "cxx-interop"))]
pub mod cxx_stub {
    //! cxx feature 未启用时的占位实现

    /// cxx 桥接概念说明
    pub fn explain_cxx_bridge() {
        println!(
            "cxx crate 桥接模式核心概念:\n\
             1. 共享类型 (Shared Types): 在 #[cxx::bridge] 中定义的 struct，C++ 和 Rust 都能看到完整定义\n\
             2. 不透明类型 (Opaque Types): Rust 只能持有 UniquePtr<T> 或 Pin<&mut T>，C++ 拥有完整实现\n\
             3. 函数绑定: unsafe extern \"C++\" 块声明 C++ 函数，extern \"Rust\" 块暴露 Rust 函数给 C++\n\
             4. 构建流程: build.rs 调用 cxx_build::bridge 自动生成 C++ 头文件和实现\n\
             5. 内存安全: cxx 编译器检查所有跨边界调用，禁止不安全的指针传递"
        );
    }

    /// bindgen 工作流程概念
    pub fn explain_bindgen_workflow() {
        println!(
            "bindgen 工作流程:\n\
             1. 编写 wrapper.h 包含需要绑定的 C/C++ 头文件\n\
             2. build.rs 中调用 bindgen::Builder::default().header(\"wrapper.h\").generate()\n\
             3. 生成的 Rust 代码包含 extern \"C\" 函数声明和 #[repr(C)] 结构体\n\
             4. 手动编写安全封装层（raw FFI -> safe Rust API）\n\
             5. 链接原生库（通过 build.rs 的 cc 或 pkg-config）"
        );
    }
}

/// 统一接口：cxx 桥接说明
pub fn explain_cxx_bridge() {
    #[cfg(feature = "cxx-interop")]
    println!("cxx bridge active: SharedPoint size = {} bytes", std::mem::size_of::<cxx_bridge::SharedPoint>());
    #[cfg(not(feature = "cxx-interop"))]
    cxx_stub::explain_cxx_bridge();
}

/// 统一接口：bindgen 流程说明
pub fn explain_bindgen_workflow() {
    #[cfg(feature = "cxx-interop")]
    println!("bindgen workflow: see build.rs for details");
    #[cfg(not(feature = "cxx-interop"))]
    cxx_stub::explain_bindgen_workflow();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cxx_concepts() {
        explain_cxx_bridge();
        explain_bindgen_workflow();
    }
}
