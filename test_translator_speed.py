from deep_translator import GoogleTranslator
import time

t = GoogleTranslator(source='zh-CN', target='en')

phrases = [
    "网络编程错误处理模块",
    "本模块定义了网络编程中使用的各种错误类型",
    "Rust 1.95 新特性实现模块",
    "练习 1: 修复借用检查错误",
    "难度: Medium",
]

start = time.time()
for p in phrases:
    result = t.translate(p)
    print(f"{p} -> {result}")
elapsed = time.time() - start
print(f"\nTotal time for {len(phrases)} phrases: {elapsed:.1f}s")
print(f"Average per phrase: {elapsed/len(phrases):.1f}s")
