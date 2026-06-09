with open('tmp_insert_quizzes.py', 'r', encoding='utf-8') as f:
    lines = f.readlines()
lines[81] = lines[81].replace('"..."', "'...'")
with open('tmp_insert_quizzes.py', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Fixed')
