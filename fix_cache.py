import json

cache = json.load(open('google_translation_cache.json'))

# Strip trailing newlines from keys and values
new_cache = {}
for k, v in cache.items():
    new_k = k.rstrip('\n')
    new_v = v.rstrip('\n')
    new_cache[new_k] = new_v

with open('google_translation_cache.json', 'w', encoding='utf-8') as f:
    json.dump(new_cache, f, ensure_ascii=False, indent=2)

print(f"Fixed {len(new_cache)} entries")
