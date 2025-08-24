# JavaScript互操作

## 1. JS与WASM互调机制

- JS调用WASM导出函数，WASM调用JS导入函数
- wasm-bindgen、js-sys等工具支持

## 2. 数据类型转换与回调

- 数值类型直接传递，字符串/对象需编码转换
- 回调机制实现事件驱动交互

## 3. 工程案例

```rust
// Rust导出函数供JS调用
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 { a + b }
// JS调用WASM
const result = wasmModule.instance.exports.add(1, 2);
```

## 4. 批判性分析与未来展望

- JS互操作提升生态集成能力，但类型转换与调试复杂度需关注
- 未来可探索自动化类型桥接与高效回调机制
