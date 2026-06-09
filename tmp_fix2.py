with open('tmp_insert_quizzes.py', 'r', encoding='utf-8') as f:
    lines = f.readlines()
for i, line in enumerate(lines):
    if 'edition = "..."' in line:
        lines[i] = line.replace('"..."', "'...'")
with open('tmp_insert_quizzes.py', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Fixed')
