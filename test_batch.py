import json
import urllib.request
import time

OLLAMA_MODEL = "qwen3.5:latest"
OLLAMA_URL = "http://localhost:11434/api/generate"

with open('chinese_blocks.txt', 'r', encoding='utf-8') as f:
    content = f.read()

blocks = [b for b in content.split('---BLOCK---\n')[1:] if b.strip()]
# Take 30 blocks
batch = blocks[:30]

prompt = (
    "Translate these Chinese Rust doc comment blocks to English. "
    "Preserve the doc comment style (/// or //!) and markdown formatting. "
    "Output each translated block separated by ---BLOCK--- on its own line. "
    "Do not add explanations, only output the translations.\n\n"
)
for idx, block in enumerate(batch, 1):
    prompt += f"Block {idx}:\n{block}\n\n"

data = json.dumps(
    {"model": OLLAMA_MODEL, "prompt": prompt, "stream": False}
).encode("utf-8")

req = urllib.request.Request(
    OLLAMA_URL,
    data=data,
    headers={"Content-Type": "application/json"},
    method="POST",
)

start = time.time()
try:
    with urllib.request.urlopen(req, timeout=120) as resp:
        result = json.loads(resp.read().decode("utf-8"))
        output = result.get("response", "")
        elapsed = time.time() - start
        print(f"Elapsed: {elapsed:.1f}s")
        parts = output.split('---BLOCK---')
        print(f"Expected: {len(batch)}, Got: {len([p for p in parts if p.strip()])}")
except Exception as e:
    elapsed = time.time() - start
    print(f"Error after {elapsed:.1f}s: {e}")
