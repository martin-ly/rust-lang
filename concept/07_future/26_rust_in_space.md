# Rust in Space Preview
>
> **受众**: [专家]
> **内容分级**: [综述级]

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **A+S+P** — Application + Structure + Procedure
> **双维定位**: P×Eva — 评价 Rust 在太空环境中的适用性
> **前置依赖**: [Embedded](../06_ecosystem/22_embedded_systems.md) · [Unsafe](../03_advanced/03_unsafe.md)
> **后置延伸**: [Rust for Linux](./19_rust_for_linux.md)

> **来源**: [Ferrocene](https://ferrocene.dev/) · [Rust Embedded WG](https://github.com/rust-embedded/wg)

### 10.4 边界测试：太空环境的单事件翻转（SEU）与 Rust 的内存安全（运行时错误）

```rust,ignore
// 概念代码: 太空辐射导致的位翻转
fn critical_checksum(data: &[u8]) -> u32 {
    let mut sum: u32 = 0;
    for &byte in data {
        sum = sum.wrapping_add(byte as u32);
    }
    sum
}

fn main() {
    let data = b"important data";
    let checksum = critical_checksum(data);
    // ❌ 运行时错误: 太空辐射可能翻转 checksum 或 data 的某一位
    // Rust 的内存安全不保护硬件层面的位翻转
    assert_eq!(checksum, critical_checksum(data));
}
```

> **修正**: **单事件翻转**（SEU, Single Event Upset）是太空辐射导致的位翻转：1) 发生在 SRAM、寄存器、逻辑电路；2) 可翻转指针值 → 指向无效地址；3) 可翻转校验和 → 数据损坏不被检测。Rust 的内存安全在此无效：1) 位翻转不违反 Rust 的引用规则（翻转后的指针仍"合法"，只是指向错误地址）；2) `unsafe` 代码的 raw pointer 更脆弱；3) 需硬件级保护（EDAC、三模冗余）。缓解策略：1) **EDAC**（Error Detection And Correction）内存；2) **CRC** 或 **双校验和**；3) **看门狗定时器**；4) **Rust 的 `no_std` + 自定义 panic handler**（优雅降级）。这与 C 的同样脆弱（无内存安全优势）或 Ada 的 SPARK（形式化验证，但不抗硬件错误）类似——太空软件需多层防护：形式化验证 + 内存安全 + 硬件冗余 + 错误检测。[来源: [Space Software](https://www.nasa.gov/software/)] · [来源: [SEU Mitigation](https://www.sciencedirect.com/topics/engineering/single-event-upset)]
