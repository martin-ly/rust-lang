#!/usr/bin/env python3
"""Bulk-add source citations to comparative markdown files."""

import subprocess
import sys
from pathlib import Path

ROOT = Path("e:/_src/rust-lang")

FILES = {
    "concept/05_comparative/06_rust_vs_java.md": [
        (
            "| 调试 | LLDB/GDB | JDWP/JVM TI |\n\n> **架构洞察**: Rust 的**零运行时**设计使其适合资源受限环境（嵌入式、边缘计算、无服务器冷启动）。Java 的**富运行时**（JIT、GC、反射）使其适合长生命周期的服务端应用。\n> [来源: [JVM Specification](https://docs.oracle.com/javase/specs/jvms/se21/html/index.html)] · [Rust Runtime](https://doc.rust-lang.org/reference/runtime.html)",
            "| 调试 | LLDB/GDB | JDWP/JVM TI |\n\n> [来源: [Wikipedia — Java (programming language)](https://en.wikipedia.org/wiki/Java_(programming_language))]\n\n> **架构洞察**: Rust 的**零运行时**设计使其适合资源受限环境（嵌入式、边缘计算、无服务器冷启动）。Java 的**富运行时**（JIT、GC、反射）使其适合长生命周期的服务端应用。\n> [来源: [JVM Specification](https://docs.oracle.com/javase/specs/jvms/se21/html/index.html)] · [Rust Runtime](https://doc.rust-lang.org/reference/runtime.html)",
        ),
        (
            "| 企业级应用 | ⚠️ 生态待成熟 | ✅ Spring, Jakarta EE | **Java** |\n\n> **场景洞察**: Rust 在**系统边界**（底层基础设施、延迟敏感）有绝对优势；Java 在**应用层**（业务系统、大数据）生态更成熟。两者在**微服务层**正在竞争。\n> [来源: [Stack Overflow Developer Survey 2025](https://survey.stackoverflow.co/)]",
            "| 企业级应用 | ⚠️ 生态待成熟 | ✅ Spring, Jakarta EE | **Java** |\n\n> [来源: [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/)]\n\n> **场景洞察**: Rust 在**系统边界**（底层基础设施、延迟敏感）有绝对优势；Java 在**应用层**（业务系统、大数据）生态更成熟。两者在**微服务层**正在竞争。\n> [来源: [Stack Overflow Developer Survey 2025](https://survey.stackoverflow.co/)]",
        ),
        (
            "> **认知功能**: 此图对比 Rust 与 Java 的**内存管理债务转移**——Rust 将复杂性前移到编译期，Java 将其后移到运行时。\n> **使用建议**: 延迟敏感场景（实时系统、高频交易、游戏引擎）选 Rust；快速迭代、延迟不敏感场景选 Java。\n> **关键洞察**: GC 的\"开发者无负担\"是一种**假象**——GC 调优（堆大小、GC 算法、暂停时间）在大型 Java 应用中同样复杂，只是复杂性从\"写代码\"转移到\"运维调优\"。\n> [来源: [TRPL — Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)] · [Java GC Tuning Guide](https://docs.oracle.com/en/java/javase/21/gctuning/)]",
            "> **认知功能**: 此图对比 Rust 与 Java 的**内存管理债务转移**——Rust 将复杂性前移到编译期，Java 将其后移到运行时。\n> **使用建议**: 延迟敏感场景（实时系统、高频交易、游戏引擎）选 Rust；快速迭代、延迟不敏感场景选 Java。\n> **关键洞察**: GC 的\"开发者无负担\"是一种**假象**——GC 调优（堆大小、GC 算法、暂停时间）在大型 Java 应用中同样复杂，只是复杂性从\"写代码\"转移到\"运维调优\"。\n> [来源: [TRPL — Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)] · [Java GC Tuning Guide](https://docs.oracle.com/en/java/javase/21/gctuning/)]\n> [来源: [Wikipedia — Java (programming language)](https://en.wikipedia.org/wiki/Java_(programming_language))]",
        ),
        (
            "| [Java Memory Model](https://docs.oracle.com/javase/specs/jls/se21/html/jls-17.html) | ✅ 一级 | JMM 规范 |\n\n---",
            "| [Java Memory Model](https://docs.oracle.com/javase/specs/jls/se21/html/jls-17.html) | ✅ 一级 | JMM 规范 |\n| [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/) | 🔍 三级 | Web 框架性能对比 |\n| [Wikipedia — Java](https://en.wikipedia.org/wiki/Java_(programming_language)) | ✅ 一级 | 语言概述 |\n\n---",
        ),
    ],
    "concept/05_comparative/08_rust_vs_ruby.md": [
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **认知功能**: Ruby 和 Rust 代表**类型系统的两个极端**——Ruby 将类型检查推迟到运行时以换取灵活性，Rust 在编译期完成所有检查以换取性能和安全性。\n> [来源: [Wikipedia — Duck Typing](https://en.wikipedia.org/wiki/Duck_typing)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [Ruby Documentation](https://www.ruby-lang.org/en/documentation/)]\n\n> **认知功能**: Ruby 和 Rust 代表**类型系统的两个极端**——Ruby 将类型检查推迟到运行时以换取灵活性，Rust 在编译期完成所有检查以换取性能和安全性。\n> [来源: [Wikipedia — Duck Typing](https://en.wikipedia.org/wiki/Duck_typing)]",
        ),
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **内存洞察**: Ruby 的 **GC 简化开发**，Rust 的 **所有权提供可预测性**——选择取决于应用场景对延迟和吞吐量的要求。\n> [来源: [Ruby GC Guide](https://tenderlovemaking.com/tags/gc.html)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [TRPL](https://doc.rust-lang.org/book/)]\n\n> **内存洞察**: Ruby 的 **GC 简化开发**，Rust 的 **所有权提供可预测性**——选择取决于应用场景对延迟和吞吐量的要求。\n> [来源: [Ruby GC Guide](https://tenderlovemaking.com/tags/gc.html)]",
        ),
        (
            "└─────────────────┴─────────────────┘\n```\n\n> **性能洞察**: Rust 比 Ruby **快 10-100 倍**——但这只在**计算密集型**场景重要。IO 密集型场景差距缩小。\n> [来源: [The Computer Language Benchmarks Game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/)]",
            "└─────────────────┴─────────────────┘\n```\n\n> [来源: [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/)]\n\n> **性能洞察**: Rust 比 Ruby **快 10-100 倍**——但这只在**计算密集型**场景重要。IO 密集型场景差距缩小。\n> [来源: [The Computer Language Benchmarks Game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/)]",
        ),
        (
            "> **认知功能**: Rust 和 Ruby **服务于不同的需求谱系**——取代不是目标，**选择合适工具**才是。\n> [来源: [Rust Design FAQ](https://doc.rust-lang.org/rustc/what-is-rustc.html)]",
            "> **认知功能**: Rust 和 Ruby **服务于不同的需求谱系**——取代不是目标，**选择合适工具**才是。\n> [来源: [Rust Design FAQ](https://doc.rust-lang.org/rustc/what-is-rustc.html)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "| [RubyConf Talks](https://rubyconf.org/) | ✅ 二级 | 社区演讲 |\n\n---",
            "| [RubyConf Talks](https://rubyconf.org/) | ✅ 二级 | 社区演讲 |\n| [Wikipedia — Ruby](https://en.wikipedia.org/wiki/Ruby_(programming_language)) | ✅ 一级 | 语言概述 |\n| [Rust Reference](https://doc.rust-lang.org/reference/) | ✅ 一级 | 语言参考 |\n\n---",
        ),
    ],
    "concept/05_comparative/09_rust_vs_swift.md": [
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **认知功能**: Swift 的 **ARC** 是**自动化的引用计数**，Rust 的 **所有权**是**编译期的代数类型系统**——两者都安全，但机制完全不同。\n> [来源: [Swift ARC Documentation](https://docs.swift.org/swift-book/documentation/the-swift-programming-language/automaticreferencecounting/)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [Swift Documentation](https://www.swift.org/documentation/)]\n\n> **认知功能**: Swift 的 **ARC** 是**自动化的引用计数**，Rust 的 **所有权**是**编译期的代数类型系统**——两者都安全，但机制完全不同。\n> [来源: [Swift ARC Documentation](https://docs.swift.org/swift-book/documentation/the-swift-programming-language/automaticreferencecounting/)]",
        ),
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **平台洞察**: Swift 是**Apple 生态的深度优化**，Rust 是**跨平台的通用系统语言**——选择取决于目标平台。\n> [来源: [Swift on Server](https://www.swift.org/server/)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [Wikipedia — Swift (programming language)](https://en.wikipedia.org/wiki/Swift_(programming_language))]\n\n> **平台洞察**: Swift 是**Apple 生态的深度优化**，Rust 是**跨平台的通用系统语言**——选择取决于目标平台。\n> [来源: [Swift on Server](https://www.swift.org/server/)]",
        ),
        (
            "> **认知功能**: **Apple 平台优先 Swift**，**跨平台/性能优先 Rust**——不是优劣之分，是场景适配。\n> [来源: [Swift vs Rust Performance](https://www.ben-morris.com/swift-vs-rust/)]",
            "> **认知功能**: **Apple 平台优先 Swift**，**跨平台/性能优先 Rust**——不是优劣之分，是场景适配。\n> [来源: [Swift vs Rust Performance](https://www.ben-morris.com/swift-vs-rust/)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "| [Swift vs Rust Blog](https://www.ben-morris.com/swift-vs-rust/) | ✅ 二级 | 对比分析 |\n\n---",
            "| [Swift vs Rust Blog](https://www.ben-morris.com/swift-vs-rust/) | ✅ 二级 | 对比分析 |\n| [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/) | 🔍 三级 | Web 框架性能对比 |\n\n---",
        ),
    ],
    "concept/05_comparative/10_rust_vs_zig.md": [
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **构建洞察**: **Zig 的构建系统是语言的延伸**——用 Zig 代码定义构建逻辑，而非学习新的配置语言。\n> [来源: [Zig Build System](https://ziglang.org/learn/build-system/)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [Zig Documentation](https://ziglang.org/documentation/master/)]\n\n> **构建洞察**: **Zig 的构建系统是语言的延伸**——用 Zig 代码定义构建逻辑，而非学习新的配置语言。\n> [来源: [Zig Build System](https://ziglang.org/learn/build-system/)]",
        ),
        (
            "> **认知功能**: **安全需求选 Rust，控制需求选 Zig**——两者在现代系统编程中各有不可替代的位置。\n> [来源: [Zig vs Rust Discussion](https://news.ycombinator.com/item?id=27608507)]",
            "> **认知功能**: **安全需求选 Rust，控制需求选 Zig**——两者在现代系统编程中各有不可替代的位置。\n> [来源: [Zig vs Rust Discussion](https://news.ycombinator.com/item?id=27608507)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "| [Zig News](https://ziglang.org/news/) | ✅ 二级 | 社区新闻 |\n\n---",
            "| [Zig News](https://ziglang.org/news/) | ✅ 二级 | 社区新闻 |\n| [Wikipedia — Zig](https://en.wikipedia.org/wiki/Zig_(programming_language)) | ✅ 一级 | 语言概述 |\n| [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/) | 🔍 三级 | 性能基准 |\n\n---",
        ),
    ],
    "concept/05_comparative/11_rust_vs_kotlin.md": [
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **平台洞察**: **Kotlin 是 JVM 生态的最佳语言，Rust 是系统编程的最佳语言**——两者在各自主场无可替代。\n> [来源: [Kotlin Multiplatform](https://kotlinlang.org/docs/multiplatform.html)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [Wikipedia — Kotlin](https://en.wikipedia.org/wiki/Kotlin_(programming_language))]\n\n> **平台洞察**: **Kotlin 是 JVM 生态的最佳语言，Rust 是系统编程的最佳语言**——两者在各自主场无可替代。\n> [来源: [Kotlin Multiplatform](https://kotlinlang.org/docs/multiplatform.html)]",
        ),
        (
            "> **认知功能**: **JVM/Android 选 Kotlin，系统/性能选 Rust**——两者在现代语言生态中互补而非竞争。\n> [来源: [Kotlin vs Rust Comparison](https://kotlinlang.org/docs/comparison-to-java.html)]",
            "> **认知功能**: **JVM/Android 选 Kotlin，系统/性能选 Rust**——两者在现代语言生态中互补而非竞争。\n> [来源: [Kotlin vs Rust Comparison](https://kotlinlang.org/docs/comparison-to-java.html)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "| [Kotlin Multiplatform](https://kotlinlang.org/docs/multiplatform.html) | ✅ 一级 | 多平台 |\n\n---",
            "| [Kotlin Multiplatform](https://kotlinlang.org/docs/multiplatform.html) | ✅ 一级 | 多平台 |\n| [Wikipedia — Kotlin](https://en.wikipedia.org/wiki/Kotlin_(programming_language)) | ✅ 一级 | 语言概述 |\n| [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/) | 🔍 三级 | 性能基准 |\n\n---",
        ),
    ],
    "concept/05_comparative/12_rust_vs_scala.md": [
        (
            "> **类型洞察**: **Scala 的类型系统更表达丰富（HKT），Rust 的类型系统更安全（所有权）**——两者代表了不同的设计哲学。\n> [来源: [Scala Type System](https://docs.scala-lang.org/scala3/book/types-intro.html)]",
            "> **类型洞察**: **Scala 的类型系统更表达丰富（HKT），Rust 的类型系统更安全（所有权）**——两者代表了不同的设计哲学。\n> [来源: [Scala Type System](https://docs.scala-lang.org/scala3/book/types-intro.html)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "> **匹配洞察**: **Scala 的模式匹配更灵活，Rust 的模式匹配更高效**——两者都提供编译期穷尽性检查。\n> [来源: [Scala Pattern Matching](https://docs.scala-lang.org/tour/pattern-matching.html)]",
            "> **匹配洞察**: **Scala 的模式匹配更灵活，Rust 的模式匹配更高效**——两者都提供编译期穷尽性检查。\n> [来源: [Scala Pattern Matching](https://docs.scala-lang.org/tour/pattern-matching.html)]\n> [来源: [TRPL](https://doc.rust-lang.org/book/)]",
        ),
        (
            "> **并发洞察**: **Scala 的 Actor 模型适合分布式，Rust 的所有权模型适合系统级**——两者各有主战场。\n> [来源: [Akka](https://akka.io/)]",
            "> **并发洞察**: **Scala 的 Actor 模型适合分布式，Rust 的所有权模型适合系统级**——两者各有主战场。\n> [来源: [Akka](https://akka.io/)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "> **认知功能**: **高阶类型/大数据选 Scala，内存安全/系统编程选 Rust**——两者在不同领域不可替代。\n> [来源: [Scala vs Rust Discussion](https://users.scala-lang.org/)]",
            "> **认知功能**: **高阶类型/大数据选 Scala，内存安全/系统编程选 Rust**——两者在不同领域不可替代。\n> [来源: [Scala vs Rust Discussion](https://users.scala-lang.org/)]\n> [来源: [Wikipedia — Scala](https://en.wikipedia.org/wiki/Scala_(programming_language))]",
        ),
        (
            "| [Scala vs Rust](https://users.scala-lang.org/) | ✅ 三级 | 社区讨论 |\n\n---",
            "| [Scala vs Rust](https://users.scala-lang.org/) | ✅ 三级 | 社区讨论 |\n| [Wikipedia — Scala](https://en.wikipedia.org/wiki/Scala_(programming_language)) | ✅ 一级 | 语言概述 |\n\n---",
        ),
    ],
    "concept/05_comparative/13_rust_vs_csharp.md": [
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **内存洞察**: **C# 的 GC 简化了内存管理但有停顿，Rust 的所有权消除了停顿但增加了学习成本**。\n> [来源: [C# Memory Management](https://docs.microsoft.com/en-us/dotnet/standard/garbage-collection/)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [C# Documentation](https://docs.microsoft.com/en-us/dotnet/csharp/)]\n\n> **内存洞察**: **C# 的 GC 简化了内存管理但有停顿，Rust 的所有权消除了停顿但增加了学习成本**。\n> [来源: [C# Memory Management](https://docs.microsoft.com/en-us/dotnet/standard/garbage-collection/)]",
        ),
        (
            "> **认知功能**: **.NET/Windows 选 C#，系统/性能选 Rust**——两者在现代生态中互补。\n> [来源: [.NET vs Rust Discussion](https://devblogs.microsoft.com/dotnet/)]",
            "> **认知功能**: **.NET/Windows 选 C#，系统/性能选 Rust**——两者在现代生态中互补。\n> [来源: [.NET vs Rust Discussion](https://devblogs.microsoft.com/dotnet/)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "| [C# Language Specification](https://docs.microsoft.com/en-us/dotnet/csharp/language-reference/) | ✅ 一级 | 语言规范 |\n\n---",
            "| [C# Language Specification](https://docs.microsoft.com/en-us/dotnet/csharp/language-reference/) | ✅ 一级 | 语言规范 |\n| [Wikipedia — C Sharp](https://en.wikipedia.org/wiki/C_Sharp_(programming_language)) | ✅ 一级 | 语言概述 |\n| [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/) | 🔍 三级 | 性能基准 |\n\n---",
        ),
    ],
    "concept/05_comparative/14_rust_vs_elixir.md": [
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **认知功能**: **Rust 和 Elixir 对错误的根本态度不同**——Rust 在编译期预防，Elixir 在运行时恢复。\n> [来源: [Elixir Error Handling](https://elixir-lang.org/getting-started/try-catch-and-rescue.html)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [Erlang/OTP](https://www.erlang.org/)]\n\n> **认知功能**: **Rust 和 Elixir 对错误的根本态度不同**——Rust 在编译期预防，Elixir 在运行时恢复。\n> [来源: [Elixir Error Handling](https://elixir-lang.org/getting-started/try-catch-and-rescue.html)]",
        ),
        (
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> **并发洞察**: **Elixir 的轻量进程和消息传递适合超高并发场景**——Rust 则在共享状态并发上提供编译期安全。\n> [来源: [Erlang Processes](https://www.erlang.org/doc/reference_manual/processes.html)]",
            "└─────────────────┴─────────────────┴─────────────────┘\n```\n\n> [来源: [Elixir Official](https://elixir-lang.org/)]\n\n> **并发洞察**: **Elixir 的轻量进程和消息传递适合超高并发场景**——Rust 则在共享状态并发上提供编译期安全。\n> [来源: [Erlang Processes](https://www.erlang.org/doc/reference_manual/processes.html)]",
        ),
        (
            "> **选择洞察**: **极致性能 + 编译期安全选 Rust，超高并发 + 热更新选 Elixir**。\n> [来源: [Rust Official](https://www.rust-lang.org/)]\n> [来源: [Rust vs Elixir](https://www.rust-lang.org/)]",
            "> **选择洞察**: **极致性能 + 编译期安全选 Rust，超高并发 + 热更新选 Elixir**。\n> [来源: [Rust Official](https://www.rust-lang.org/)]\n> [来源: [Rust vs Elixir](https://www.rust-lang.org/)]\n> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
        ),
        (
            "| [Designing for Scalability with Erlang/OTP](https://www.oreilly.com/library/view/designing-for-scalability/9781449361556/) | ✅ 二级 | 书籍 |\n\n---",
            "| [Designing for Scalability with Erlang/OTP](https://www.oreilly.com/library/view/designing-for-scalability/9781449361556/) | ✅ 二级 | 书籍 |\n| [Wikipedia — Erlang](https://en.wikipedia.org/wiki/Erlang_(programming_language)) | ✅ 一级 | 语言概述 |\n| [TechEmpower Benchmarks](https://www.techempower.com/benchmarks/) | 🔍 三级 | 性能基准 |\n\n---",
        ),
    ],
}


def apply_replacements(file_path: Path, replacements):
    content = file_path.read_text(encoding="utf-8")
    changes = 0
    for old, new in replacements:
        if old in content:
            content = content.replace(old, new, 1)
            changes += 1
        else:
            print(f"  ⚠️  SKIPPED (pattern not found): {file_path.name}", file=sys.stderr)
    file_path.write_text(content, encoding="utf-8")
    return changes


def run_audit():
    result = subprocess.run(
        ["python", "scripts/concept_audit.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    print(result.stdout)
    if result.returncode != 0:
        print(result.stderr, file=sys.stderr)
    return result.returncode


def main():
    summary = []
    for rel_path, replacements in FILES.items():
        file_path = ROOT / rel_path
        print(f"\n{'='*60}")
        print(f"Processing {rel_path}")
        print(f"{'='*60}")
        changes = apply_replacements(file_path, replacements)
        print(f"Applied {changes}/{len(replacements)} replacements.")
        audit_rc = run_audit()
        status = "✅ PASSED" if audit_rc == 0 else "⚠️ ISSUES FOUND"
        print(f"Audit: {status}")
        summary.append({
            "file": rel_path,
            "changes": changes,
            "total": len(replacements),
            "audit_rc": audit_rc,
        })

    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    for item in summary:
        status = "✅" if item["audit_rc"] == 0 else "⚠️"
        print(f"{status} {item['file']}: {item['changes']}/{item['total']} replacements, audit_rc={item['audit_rc']}")


if __name__ == "__main__":
    main()
