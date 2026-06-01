import json
import urllib.request
import time

OLLAMA_URL = "http://localhost:11434/api/generate"

def translate(text):
    prompt = f"Translate this Chinese Rust doc comment to English. Preserve /// or //! style. Output ONLY the translation, no explanation.\n\n{text}\n"
    data = json.dumps({
        "model": "gemma4:e4b",
        "prompt": prompt,
        "stream": False,
        "keep_alive": "30m",
    }).encode("utf-8")
    req = urllib.request.Request(OLLAMA_URL, data=data, headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=60) as resp:
        result = json.loads(resp.read().decode("utf-8"))
        return result.get("response", "")

# Warmup
t1 = time.time()
r1 = translate("/// 网络编程错误处理模块")
print(f"Warmup: {time.time()-t1:.1f}s -> {r1.strip()}")

# Second call
t2 = time.time()
r2 = translate("/// 安全相关错误")
print(f"Call 2: {time.time()-t2:.1f}s -> {r2.strip()}")

# Third call
t3 = time.time()
r3 = translate("/// 延迟初始化的协议处理器注册表")
print(f"Call 3: {time.time()-t3:.1f}s -> {r3.strip()}")
