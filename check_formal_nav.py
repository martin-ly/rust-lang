#!/usr/bin/env python3
import json

d = json.load(open('docs/link_check_report.json'))
file_path = 'archive/temp/FORMAL_AND_PRACTICAL_NAVIGATION.md'

if file_path in d['broken_by_file']:
    print(f'Broken links in {file_path}:')
    for link in d['broken_by_file'][file_path]:
        print(f"  [{link['link_text']}]({link['link_target']})")
