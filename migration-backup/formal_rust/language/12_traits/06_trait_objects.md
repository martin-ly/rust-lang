# 特质对象实现

## 1. dyn Trait与对象安全

- dyn Trait：运行时多态，vtable机制
- 对象安全条件：无泛型方法、Self: Sized等

## 2. vtable与动态分发

- vtable存储方法指针，动态分发调用

## 3. 工程案例

```rust
trait Draw { fn draw(&self); }
impl Draw for i32 { fn draw(&self) { println!("draw i32"); } }
fn show(x: &dyn Draw) { x.draw(); }
```

## 4. 批判性分析与未来展望

- 特质对象提升灵活性与抽象能力，但动态分发有性能开销
- 未来可探索对象安全自动检测与vtable优化
