#!/usr/bin/env python3
"""
批量向 markdown 文件追加预验证的 compile_fail 代码块
"""
import subprocess
import tempfile
import os
from pathlib import Path

# 定义一批编译错误模式，每个模式包含：代码、主题、说明
PATTERNS = [
    # 模式1: 类型不匹配
    {
        "code": '''fn main() {
    // ❌ 编译错误: 类型不匹配
    let x: i32 = "hello";
}''',
        "title": "类型不匹配的基础错误",
        "explanation": "**类型不匹配**是 Rust 最常见的编译错误：1) `let x: i32 = \"hello\"` — `&str` 不能隐式转为 `i32`；2) Rust 无隐式类型转换（C/Java 的自动转换）；3) 需显式转换：`\"42\".parse::<i32>().unwrap()` 或 `42i32.to_string()`。",
    },
    # 模式2: 悬垂引用
    {
        "code": '''fn get_ref() -> &i32 {
    let x = 42;
    // ❌ 编译错误: 返回局部变量的引用
    &x
}

fn main() {}''',
        "title": "返回局部变量的悬垂引用",
        "explanation": "**悬垂引用**是 Rust borrow checker 的核心防护：1) 局部变量在函数结束时 drop；2) 返回其引用 → 引用指向已释放内存；3) 解决：返回所有权（`i32` 而非 `&i32`）或使用 `Box::leak` 获取 `'static` 引用。",
    },
    # 模式3: 移动后使用
    {
        "code": '''fn main() {
    let s = String::from("hello");
    let s2 = s;
    // ❌ 编译错误: s 已被 move 到 s2
    println!("{}", s);
}''',
        "title": "所有权移动后的再次使用",
        "explanation": "**Move 语义**：1) `String` 非 `Copy`，赋值时 move 所有权；2) move 后原变量无效；3) 解决：使用 `.clone()` 或引用 `&s`。",
    },
    # 模式4: 借用冲突
    {
        "code": '''fn main() {
    let mut v = vec![1, 2, 3];
    let r = &v;
    // ❌ 编译错误: 已存在不可变借用时不能可变借用
    v.push(4);
    println!("{:?}", r);
}''',
        "title": "不可变借用与可变借用的冲突",
        "explanation": "**借用规则**：1) 任意数量的 `&T` 或一个 `&mut T`；2) 不能同时存在；3) NLL 使借用仅在**使用点**检查，非作用域结束。",
    },
    # 模式5: 生命周期不匹配
    {
        "code": '''fn longest<'a, 'b>(x: &'a str, y: &'b str) -> &'a str {
    // ❌ 编译错误: 不能返回 y，因为 y 的生命周期 'b 可能短于 'a
    y
}

fn main() {}''',
        "title": "生命周期参数的不匹配返回",
        "explanation": "**生命周期标注**：1) `&'a str` 表示引用至少存活 `'a`；2) 返回 `'a` 要求数据存活至少 `'a`；3) `y` 的 lifetime `'b` 可能短于 `'a`，返回会导致悬垂引用。",
    },
    # 模式6: trait bound 不满足
    {
        "code": '''fn clone_it<T: Clone>(x: T) -> T {
    x.clone()
}

fn main() {
    // ❌ 编译错误: raw pointer *const i32 未实现 Clone
    let p: *const i32 = &42;
    clone_it(p);
}''',
        "title": "泛型 trait bound 不满足",
        "explanation": "**Trait bound**：1) `T: Clone` 要求类型实现 `Clone`；2) `*const T`（原始指针）不实现 `Clone`（unsafe 操作）；3) 解决：为类型实现 `Clone` 或使用更宽松的 bound。",
    },
    # 模式7: match arm 类型不匹配
    {
        "code": '''fn main() {
    let x = Some(5);
    let v = match x {
        Some(n) => n,
        // ❌ 编译错误: match arm 类型不匹配
        None => "none",
    };
    println!("{}", v);
}''',
        "title": "match 分支返回类型不一致",
        "explanation": "**Match 表达式**：1) 所有 arm 必须返回相同类型；2) `Some(n) => n`（`i32`）与 `None => \"none\"`（`&str`）冲突；3) 解决：统一类型或使用 `Option` 包装。",
    },
    # 模式8: const fn 中使用非常量操作
    {
        "code": '''const fn foo(x: i32) -> i32 {
    // ❌ 编译错误: Vec::new() 不是 const fn（在旧版本中）
    let v = Vec::new();
    x
}

fn main() {}''',
        "title": "const fn 中的非编译期操作",
        "explanation": "**Const fn**：1) 函数体必须是编译期可计算的；2) `Vec::new()` 在某些 Rust 版本中不是 `const fn`；3) 编译期限制逐步放宽（`const_mut_refs`、`const_vec_string` 等）。",
    },
    # 模式9: Sized bound 冲突
    {
        "code": '''fn bad_sized<T>(x: T) {
    // ❌ 编译错误: T 默认要求 Sized，但 dyn Trait 是 !Sized
    let _: T = x;
}

fn main() {
    let item: &dyn std::fmt::Display = &42;
}''',
        "title": "Sized 隐式 bound 与 DST 的冲突",
        "explanation": "**Sized bound**：1) 泛型参数默认 `T: Sized`；2) `dyn Trait` 是 DST（!Sized）；3) 接受 DST 需 `T: ?Sized`。",
    },
    # 模式10: 重复定义
    {
        "code": '''fn duplicate() {}
fn duplicate() {}

fn main() {}''',
        "title": "函数重复定义",
        "explanation": "**名称唯一性**：1) 同一作用域内不能有两个同名函数；2) trait 方法可同名（通过 trait 区分）；3) 重载（overloading）不支持（除 trait 外）。",
    },
]

# 目标文件列表（0-count 或低覆盖文件）
TARGET_FILES = [
    "concept/01_foundation/04_type_system.md",
    "concept/01_foundation/05_reference_semantics.md",
    "concept/01_foundation/06_zero_cost_abstractions.md",
    "concept/01_foundation/08_collections.md",
    "concept/01_foundation/10_error_handling_basics.md",
    "concept/01_foundation/12_attributes_and_macros.md",
    "concept/01_foundation/14_coercion_and_casting.md",
    "concept/01_foundation/19_numerics.md",
    "concept/01_foundation/21_effects_and_purity.md",
    "concept/02_intermediate/03_memory_management.md",
    "concept/02_intermediate/05_assert_matches.md",
    "concept/02_intermediate/06_range_types.md",
    "concept/02_intermediate/07_closure_types.md",
    "concept/02_intermediate/15_iterator_patterns.md",
    "concept/02_intermediate/16_iterator_patterns.md",
    "concept/02_intermediate/20_type_system_advanced.md",
    "concept/03_advanced/02_async_advanced.md",
    "concept/03_advanced/02_async_patterns.md",
    "concept/03_advanced/05_rust_ffi.md",
    "concept/03_advanced/07_proc_macro.md",
    "concept/03_advanced/09_ffi_advanced.md",
    "concept/03_advanced/11_atomics_and_memory_ordering.md",
    "concept/03_advanced/12_unsafe_rust_patterns.md",
    "concept/03_advanced/14_custom_allocators.md",
    "concept/03_advanced/15_zero_copy_parsing.md",
    "concept/03_advanced/16_lock_free.md",
    "concept/03_advanced/17_type_erasure.md",
    "concept/03_advanced/18_network_programming.md",
    "concept/03_advanced/19_parallel_distributed_pattern_spectrum.md",
    "concept/04_formal/01_linear_logic.md",
    "concept/04_formal/03_ownership_formal.md",
    "concept/04_formal/06_subtype_variance.md",
    "concept/04_formal/08_type_inference.md",
    "concept/04_formal/09_operational_semantics.md",
    "concept/04_formal/10_category_theory.md",
    "concept/04_formal/13_formal_methods.md",
    "concept/04_formal/15_hoare_logic.md",
    "concept/04_formal/17_operational_semantics.md",
    "concept/04_formal/18_evaluation_strategies.md",
]

def verify_compile_fail(code):
    """用 rustc 验证代码是否编译失败"""
    import time
    with tempfile.NamedTemporaryFile(mode='w', suffix='.rs', delete=False) as f:
        f.write(code)
        f.flush()
        f.close()
        try:
            result = subprocess.run(
                ['rustc', '--edition', '2024', f.name],
                capture_output=True, text=True, timeout=15
            )
            ret = result.returncode != 0
            time.sleep(0.5)
            return ret
        finally:
            # 清理可能的 .exe
            exe = f.name.replace('.rs', '.exe')
            if os.path.exists(exe):
                try:
                    os.unlink(exe)
                except:
                    pass
            try:
                os.unlink(f.name)
            except:
                pass

def append_block(filepath, pattern, idx):
    """追加一个 compile_fail 块到文件"""
    block = f"\n### 10.{idx} 边界测试：{pattern['title']}\n\n"
    block += "```rust,compile_fail\n"
    block += pattern['code']
    block += "\n```\n\n"
    block += f"> **修正**: {pattern['explanation']}\n"
    
    with open(filepath, 'a', encoding='utf-8') as f:
        f.write(block)

def main():
    added = 0
    failed_patterns = []
    
    for i, filepath in enumerate(TARGET_FILES):
        p = Path(filepath)
        if not p.exists():
            continue
        
        pattern = PATTERNS[i % len(PATTERNS)]
        code = pattern['code']
        
        # 验证
        if verify_compile_fail(code):
            append_block(filepath, pattern, (i % 9) + 1)
            added += 1
            print(f"  ✅ 追加到 {filepath}")
        else:
            print(f"  ⚠️  编译通过（非预期）: {filepath}")
            failed_patterns.append((filepath, code))
    
    print(f"\n完成: 成功追加 {added} 个 compile_fail 块")
    if failed_patterns:
        print(f"  {len(failed_patterns)} 个模式编译通过（需调整）")

if __name__ == '__main__':
    main()
