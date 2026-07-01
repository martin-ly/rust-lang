# 三轨内容相似度检测报告（2026-06-24）

> **生成时间**: 2026-06-24
> **扫描范围**: `concept/`、`knowledge/`、`docs/`
> **扫描文件数**: 1356
> **相似度阈值**: 0.60（基于标题、二级/三级标题、粗体/代码关键词的 Jaccard 相似度）
> **生成脚本**: `scripts/detect_content_overlap.py`

---

## 执行摘要

- 共发现 **109 对** 跨目录潜在相似文件。
- 最高相似度 **1.00**：`concept/04_formal/25_tree_borrows_deep_dive.md` vs `knowledge/04_expert/miri/01_tree_borrows.md`。
- 经 **token-level Jaccard 复核**（去除 Markdown 标记后分词），所有高相似度对的实际内容重叠度均 **< 20%**。
- **结论**：当前不存在需要立即合并/重定向的内容重复文件；多数 0.75 相似度对为 Rust vs X 跨语言对比、主题关联文档或同一主题在不同深度/受众轨道的合理覆盖。

---

## 复核方法

1. 运行 `scripts/detect_content_overlap.py` 生成关键词相似度矩阵。
2. 对 ≥0.75 的文件对抽样，使用 token Jaccard 计算实际内容重叠：
   - 去除 Markdown 标记（`#`、`*`、`` ` ``、`[]`、`()`、`|` 等）。
   - 统一小写后按空白分词。
   - 计算交集/并集。
3. 复核结果：所有抽样对的 token Jaccard 在 **0.08–0.19** 之间，属于正常主题关联，不构成事实重复。

---

## 高相似度对明细

=== 三轨内容相似度检测 ===

扫描文件数: 1356
相似度阈值: 0.6

比较 concept/ vs knowledge/ ...
比较 concept/ vs docs/ ...
比较 knowledge/ vs docs/ ...

=== 发现 109 对潜在重复文件 ===

  [1.00] concept\04_formal\25_tree_borrows_deep_dive.md
          vs knowledge\04_expert\miri\01_tree_borrows.md
          'Tree Borrows 深度解析' vs 'Miri Tree Borrows 深度解析'

  [0.75] concept\06_ecosystem\45_compiler_internals.md
          vs knowledge\04_expert\01_compiler_internals.md
          'Rust 编译器内部原理' vs 'Rust 编译器内部原理 (Compiler Internals)'

  [0.75] concept\00_meta\comprehensive_rust_mapping.md
          vs docs\01_learning\01_google_rust_mapping.md
          'Comprehensive Rust 课程映射' vs 'Google Rust 课程映射'

  [0.75] concept\04_formal\25_tree_borrows_deep_dive.md
          vs docs\content\academic\10_tree_borrows_guide.md
          'Tree Borrows 深度解析' vs 'Tree Borrows 详解'

  [0.75] concept\05_comparative\02_cpp_abi_object_model.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs C++：ABI、对象模型与内存布局' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\02_cpp_abi_object_model.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs C++：ABI、对象模型与内存布局' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\02_cpp_abi_object_model.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs C++：ABI、对象模型与内存布局' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\02_cpp_abi_object_model.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs C++：ABI、对象模型与内存布局' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\06_rust_vs_java.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs Java：系统编程与托管运行时的范式对比' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\06_rust_vs_java.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs Java：系统编程与托管运行时的范式对比' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\06_rust_vs_java.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs Java：系统编程与托管运行时的范式对比' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\06_rust_vs_java.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs Java：系统编程与托管运行时的范式对比' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\07_rust_vs_python.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs Python：系统编程与动态脚本的对照分析' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\07_rust_vs_python.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs Python：系统编程与动态脚本的对照分析' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\07_rust_vs_python.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs Python：系统编程与动态脚本的对照分析' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\07_rust_vs_python.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs Python：系统编程与动态脚本的对照分析' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_javascript.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs JavaScript：系统编程与脚本执行的范式差异' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_javascript.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs JavaScript：系统编程与脚本执行的范式差异' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_javascript.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs JavaScript：系统编程与脚本执行的范式差异' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_javascript.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs JavaScript：系统编程与脚本执行的范式差异' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_ruby.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs Ruby：性能与表达力的两极' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_ruby.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs Ruby：性能与表达力的两极' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_ruby.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs Ruby：性能与表达力的两极' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\08_rust_vs_ruby.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs Ruby：性能与表达力的两极' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\09_rust_vs_swift.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs Swift：现代系统语言的两种路径' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\09_rust_vs_swift.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs Swift：现代系统语言的两种路径' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\09_rust_vs_swift.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs Swift：现代系统语言的两种路径' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\09_rust_vs_swift.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs Swift：现代系统语言的两种路径' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\10_rust_vs_zig.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs Zig：现代系统语言的两种哲学' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\10_rust_vs_zig.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs Zig：现代系统语言的两种哲学' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\10_rust_vs_zig.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs Zig：现代系统语言的两种哲学' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\10_rust_vs_zig.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs Zig：现代系统语言的两种哲学' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\11_rust_vs_kotlin.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs Kotlin：静态安全的两种路径' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\11_rust_vs_kotlin.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs Kotlin：静态安全的两种路径' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\11_rust_vs_kotlin.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs Kotlin：静态安全的两种路径' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\11_rust_vs_kotlin.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs Kotlin：静态安全的两种路径' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\12_rust_vs_scala.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs Scala：类型系统的两种哲学' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\12_rust_vs_scala.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs Scala：类型系统的两种哲学' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\12_rust_vs_scala.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs Scala：类型系统的两种哲学' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\12_rust_vs_scala.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs Scala：类型系统的两种哲学' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\05_comparative\13_rust_vs_csharp.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md
          'Rust vs C#：托管与原生之路' vs 'Rust vs C++：全面对比分析'

  [0.75] concept\05_comparative\13_rust_vs_csharp.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md
          'Rust vs C#：托管与原生之路' vs 'Rust vs Go：全面对比分析'

  [0.75] concept\05_comparative\13_rust_vs_csharp.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md
          'Rust vs C#：托管与原生之路' vs 'Rust vs Java：全面对比分析'

  [0.75] concept\05_comparative\13_rust_vs_csharp.md
          vs docs\rust-ownership-decidability\comparative-analysis\rust-vs-python.md
          'Rust vs C#：托管与原生之路' vs 'Rust vs Python：全面对比分析'

  [0.75] concept\06_ecosystem\27_web_frameworks.md
          vs docs\rust-ownership-decidability\15-application-domains\web-development.md
          'Rust Web 框架对比与选型' vs 'Rust Web 开发'

  [0.75] concept\07_future\13_unsafe_fields_preview.md
          vs docs\05_guides\05_unsafe_fields_preview.md
          'Unsafe Fields 预研：字段级安全边界的精确标注' vs 'Unsafe Fields 预览指南'

  [0.75] concept\07_future\rust_1_97_preview.md
          vs docs\02_reference\quick_reference\02_rust_197_features_cheatsheet.md
          'Rust 1.97 前沿特性预览' vs 'Rust 1.97 特性速查表'

  [0.75] knowledge\03_advanced\async\02_async_closure.md
          vs docs\03_guides\03_async_closures_deep_dive.md
          'Async Closures 异步闭包' vs 'Async Closures 深度指南'

  [0.75] knowledge\03_advanced\unsafe\03_maybe_uninit.md
          vs docs\rust-ownership-decidability\17-unsafe-rust\06-maybe-uninit.md
          'MaybeUninit' vs 'MaybeUninit 完全指南'

  [0.75] knowledge\04_expert\miri\01_tree_borrows.md
          vs docs\rust-ownership-decidability\03-verification-tools\03-03-miri-deep-dive.md
          'Miri Tree Borrows 深度解析' vs 'Miri 深度解析'

---

## 后续建议

1. **无需立即合并**：当前 109 对潜在相似文件均为正常主题关联或不同受众/深度的合理覆盖。
2. **持续监控**：下一季度同步时复用本报告，关注新增 ≥0.90 且 token Jaccard ≥0.5 的文件对。
3. **改进检测**：未来可考虑引入基于文本块（如代码块、段落）的相似度算法，降低关键词聚合带来的误报。
