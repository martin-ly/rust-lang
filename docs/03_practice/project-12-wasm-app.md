# 实践项目 12: WebAssembly应用

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c12 (WASM)
> **预计时间**: 6-8小时

---

## 项目目标

创建编译到WebAssembly的浏览器应用。

---

## 功能需求

- [ ] Rust编译到WASM
- [ ] JavaScript互操作
- [ ] DOM操作
- [ ] Canvas绘图
- [ ] 游戏或可视化

---

## 学习要点

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
