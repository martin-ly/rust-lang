import json
import urllib.request
import time

OLLAMA_URL = "http://localhost:11434/api/generate"

blocks = [
    "/// 网络编程错误处理模块",
    "/// 安全相关错误",
    "/// 错误统计",
    "/// 延迟初始化的协议处理器注册表",
    "/// 注册协议处理器",
]

prompt = (
    "Translate these 5 Chinese Rust doc comments to English. "
    "Preserve /// style. Output ONLY the translations, one per line, no explanations.\n\n"
)
for idx, block in enumerate(blocks, 1):
    prompt += f"{idx}. {block}\n"

data = json.dumps({
    "model": "gemma4:e4b",
    "prompt": prompt,
    "stream": False,
    "keep_alive": "10m",
}).encode("utf-8")

req = urllib.request.Request(
    OLLAMA_URL,
    data=data,
    headers={"Content-Type": "application/json"},
    method="POST",
)

start = time.time()
try:
    with urllib.request.urlopen(req, timeout=90) as resp:
        result = json.loads(resp.read().decode("utf-8"))
        elapsed = time.time() - start
        print(f"Time: {elapsed:.1f}s")
        print("Response:")
        print(result.get("response", "ERROR"))
except Exception as e:
    elapsed = time.time() - start
    print(f"Error after {elapsed:.1f}s: {e}")
