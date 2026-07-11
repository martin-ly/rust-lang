#!/usr/bin/env python3
"""
为 L1-L3 核心文件批量添加 ⟸ 反向推理段落。
"""

from pathlib import Path

BACKWARD_SECTIONS = {
    "concept/01_foundation/01_ownership.md": """

## 逆向推理链（Backward Reasoning）

> **从编译错误反推定理链**：
>
> ```text
> C3(Safe Rust 内存安全完备性) ⟸ T5(无数据竞争) ⟸ T4(&mut 唯一性) ⟸ L1(所有权唯一性)
> C2(裸指针危险) ⟸ C1(无所有权) ⟸ T1(RAII 失效)
> ```
>
> **诊断方法**：当编译器报告借用检查错误时，从错误类型定位到失效的定理节点，向上追溯至需要修正的前提。
> - E0382 (use of moved value) → L2(Move 语义) 违反 → 检查是否误用已移动变量
> - E0499 (cannot borrow `x` as mutable more than once) → T4(&mut 唯一性) 违反 → L1(所有权唯一性) 约束未满足
> - E0502 (cannot borrow `x` as immutable because it is also borrowed as mutable) → T1(AXM) 违反 → 检查 &mut T 与 &T 的生命周期重叠
""",
    "concept/01_foundation/02_borrowing.md": """

## 逆向推理链（Backward Reasoning）

> **从编译错误反推定理链**：
>
> ```text
> T5(借用 ⟹ 无数据竞争) ⟸ T1(AXM) ⟸ L2(&mut T 独占写) + L1(&T 共享读)
> T6(Two-Phase Borrow 安全) ⟸ T3(Reborrow 安全) ⟸ T2(引用有效性)
> ```
>
> **诊断方法**：
> - E0501 (cannot borrow `x` as mutable more than once at a time) → L2(&mut 独占写) 违反
> - E0503 (cannot use `x` because it was mutably borrowed) → T1(AXM) 违反 → 检查 &mut 与使用点的作用域
> - E0716 (temporary value dropped while borrowed) → T2(引用有效性) 违反 → 生命周期标注不足
""",
    "concept/01_foundation/03_lifetimes.md": """

## 逆向推理链（Backward Reasoning）

> **从生命周期错误反推定理链**：
>
> ```text
> T3(Variance 子类型安全) ⟸ L2(生命周期偏序集) ⟸ L1(引用不能比数据活得久)
> C2(HRTB 全称量化) ⟸ T1(Elision 推导正确性) ⟸ L2(生命周期偏序集)
> ```
>
> **诊断方法**：
> - E0597 (`x` does not live long enough) → L1(引用不能比数据活得久) 违反 → 检查被引用值的作用域
> - E0623 (lifetime mismatch) → L2(偏序集约束) 违反 → 显式标注生命周期关系
> - E0308 (mismatched types involving lifetimes) → T3(Variance) 违反 → 检查协变/逆变/不变位置
""",
    "concept/01_foundation/04_type_system.md": """

## 逆向推理链（Backward Reasoning）

> **从类型错误反推定理链**：
>
> ```text
> C1(Option<T> 空指针消除) ⟸ T1(match 穷尽性) + L2(NPO)
> T3(类型一致性 / Progress + Preservation) ⟸ L1(ADT 代数完备性) + L2(NPO)
> ```
>
> **诊断方法**：
> - E0004 (non-exhaustive patterns) → T1(match 穷尽性) 违反 → 补全 match 分支或添加 `_`
> - E0308 (mismatched types) → T3(类型一致性) 违反 → 检查类型转换或添加显式转换
> - E0277 (the trait bound is not satisfied) → L1(ADT 完备性) + Trait 约束不满足
""",
    "concept/02_intermediate/01_traits.md": """

## 逆向推理链（Backward Reasoning）

> **从 Trait 错误反推定理链**：
>
> ```text
> 单态化零成本 ⟸ Coherence ⟸ Orphan Rule
> dyn Trait 可行性 ⟸ Trait 对象安全条件
> ```
>
> **诊断方法**：
> - E0117 (only traits defined in the current crate can be implemented for arbitrary types) → Orphan Rule 违反
> - E0038 (trait cannot be made into an object) → Trait 对象安全条件不满足 → 检查 `Self: Sized` 方法
> - E0283 (type annotations needed) → 单态化类型推断歧义 → 显式指定类型参数
""",
    "concept/02_intermediate/02_generics.md": """

## 逆向推理链（Backward Reasoning）

> **从泛型错误反推定理链**：
>
> ```text
> 语义保持 ⟸ 单态化零成本 ⟸ 参数多态
> 约束可满足性 ⟸ System F 类型规则
> ```
>
> **诊断方法**：
> - E0282 (type annotations needed) → 参数多态类型推断不足 → 显式标注类型参数
> - E0277 (trait bound not satisfied) → 约束可满足性 违反 → 为泛型参数添加 Trait Bound
> - E0792 (expected generic lifetime parameter) → 生命周期约束未满足 → 显式关联生命周期参数
""",
    "concept/03_advanced/01_concurrency.md": """

## 逆向推理链（Backward Reasoning）

> **从并发错误反推定理链**：
>
> ```text
> T5(Rayon 数据并行) ⟸ T1(类型系统排他性) ⟸ L1(Send/Sync 安全性)
> T4(Channel 消息安全) ⟸ T2(Arc<T> 共享所有权) ⟸ L1(Send/Sync 安全性)
> ```
>
> **诊断方法**：
> - E0277 (`Rc<Mutex<T>>` cannot be sent between threads safely) → L1(Send 不满足) → 改用 Arc
> - E0277 (`&T` cannot be sent between threads safely) → Sync 不满足 → 检查 T 的字段类型
> - E0499 (cannot borrow data in `Arc` as mutable) → T2(Arc 只共享) 违反 → 使用 Mutex/RwLock 或 Atomic
""",
    "concept/03_advanced/02_async.md": """

## 逆向推理链（Backward Reasoning）

> **从异步错误反推定理链**：
>
> ```text
> T1(async/await 状态机变换) ⟸ L2(Pin<&mut Self> 自引用安全) ⟸ L1(Future trait 语义)
> T2(Send Future) ⟸ L2(Pin<&mut Self> 自引用安全)
> C1(!Send 类型跨 await ⟹ 编译错误) ⟸ T2(Send Future)
> ```
>
> **诊断方法**：
> - E0277 (future cannot be sent between threads safely) → T2(Send Future) 违反 → 检查 async 块内捕获的变量类型
> - E0769 (awaited future has type `!Send`) → C1(!Send 跨 await) → 将 !Send 变量移出 async 块
> - E0746 (type contains a self-referential struct) → L2(Pin 安全) 违反 → 使用 `pin!` 或 `Box::pin`
""",
    "concept/03_advanced/03_unsafe.md": """

## 逆向推理链（Backward Reasoning）

> **从 UB 反推安全条件**：
>
> ```text
> safe 接口可信 ⟸ unsafe 实现正确 + safe 接口封装 + 人工证明
> Miri 报错 ⟸ 程序违反了 Stacked/Tree Borrows 别名模型
> ```
>
> **诊断方法**：
> - Miri: error: Undefined Behavior (dangling pointer) → 违反了 T2(引用有效性) → 检查裸指针生命周期
> - Miri: error: Undefined Behavior (data race) → 违反了 T5(无数据竞争) → 检查 UnsafeCell 使用或原子序数
> - Miri: error: invalid enum value → Validity Invariant 违反 → 检查 transmute 的目标类型
""",
}


def insert_before_reference(filepath: Path, section: str) -> bool:
    """在 ## 参考来源 / ## 权威来源索引 / ## 导航 之前插入段落"""
    content = filepath.read_text(encoding="utf-8")
    
    # 查找插入点：在参考来源或导航之前
    markers = ["## 参考来源", "## 权威来源索引", "## 导航"]
    insert_pos = -1
    for marker in markers:
        pos = content.find(marker)
        if pos != -1:
            insert_pos = pos
            break
    
    if insert_pos == -1:
        print(f"  ⚠️ 未找到插入点: {filepath}")
        return False
    
    # 在 marker 前插入（保留换行）
    new_content = content[:insert_pos] + section + "\n" + content[insert_pos:]
    filepath.write_text(new_content, encoding="utf-8")
    return True


def main():
    total = 0
    for rel_path, section in BACKWARD_SECTIONS.items():
        filepath = Path(rel_path)
        if not filepath.exists():
            print(f"  ⚠️ 文件不存在: {filepath}")
            continue
        if insert_before_reference(filepath, section):
            print(f"  ✅ 已添加反向推理: {filepath}")
            total += 1
    print(f"\n总计: 为 {total} 个文件添加了反向推理链")


if __name__ == "__main__":
    main()
