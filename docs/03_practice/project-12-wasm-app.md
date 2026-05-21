# 实践项目 12: WebAssembly应用

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c12 (WASM)
> **预计时间**: 6-8小时

---

## 项目目标
> **[来源: Rust Official Docs]**

创建编译到WebAssembly的浏览器应用。

---

## 功能需求
> **[来源: Rust Official Docs]**

- [ ] Rust编译到WASM
- [ ] JavaScript互操作
- [ ] DOM操作
- [ ] Canvas绘图
- [ ] 游戏或可视化

---

## 学习要点
> **[来源: Rust Official Docs]**

### WASM绑定

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);
}
```

---

## 参考实现

完整参考实现位于: `examples/wasm-app/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)


---

- [README](./README.md)
