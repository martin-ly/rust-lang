#!/usr/bin/env python3
import json

d = json.load(open('docs/link_check_report.json'))
file_path = 'rust-ownership-decidability/17-unsafe-rust/README.md'

if file_path in d['broken_by_file']:
    print(f'Broken links in {file_path}:')
    for link in d['broken_by_file'][file_path]:
        print(f"  [{link['link_text']}]({link['link_target']})")
else:
    print(f'No broken links found for {file_path}')
