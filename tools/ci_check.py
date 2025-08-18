#!/usr/bin/env python3
import subprocess
import sys

def run(cmd):
    print(f"==> {cmd}")
    r = subprocess.run(cmd, shell=True)
    if r.returncode != 0:
        sys.exit(r.returncode)

if __name__ == "__main__":
    run("python tools/scan_refs.py")
    run("python tools/crossref_check.py")
    run("python formal_rust/framework/verify_integrity.py")
    print("CI checks passed.") 