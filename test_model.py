import json
import urllib.request
import time

OLLAMA_URL = "http://localhost:11434/api/generate"

blocks = [
    "//! 网络编程错误处理模块\n//!\n//! 本模块定义了网络编程中使用的各种错误类型",
    "/// # Trait 对象向上转换\n///\n/// Rust 1.86.0 稳定了 trait 对象的向上转换（upcasting）",
]

for model in ["qwen3.5:latest", "gemma4:e4b"]:
    prompt = (
        "Translate these Chinese Rust doc comment blocks to English. "
        "Preserve the doc comment style (/// or //!) and markdown formatting. "
        "Output each translated block separated by ---BLOCK--- on its own line. "
        "Do not add explanations, only output the translations.\n\n"
    )
    for idx, block in enumerate(blocks, 1):
        prompt += f"Block {idx}:\n{block}\n\n"

    data = json.dumps(
        {"model": model, "prompt": prompt, "stream": False}
    ).encode("utf-8")

    req = urllib.request.Request(
        OLLAMA_URL,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )

    start = time.time()
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            result = json.loads(resp.read().decode("utf-8"))
            elapsed = time.time() - start
            print(f"{model}: {elapsed:.1f}s")
            print(result.get("response", "")[:200])
            print()
    except Exception as e:
        elapsed = time.time() - start
        print(f"{model}: ERROR after {elapsed:.1f}s: {e}")
        print()
