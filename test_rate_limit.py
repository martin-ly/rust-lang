from deep_translator import GoogleTranslator
import time

t = GoogleTranslator(source='zh-CN', target='en')

phrases = [f"测试短语 {i}" for i in range(20)]

start = time.time()
for i, p in enumerate(phrases):
    try:
        r = t.translate(p)
        print(f"{i+1}: OK")
    except Exception as e:
        print(f"{i+1}: ERROR - {e}")
        break
elapsed = time.time() - start
print(f"Total: {elapsed:.1f}s")
