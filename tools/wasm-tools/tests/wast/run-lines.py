#!/usr/bin/env python3
"""Print the `wast` RUN lines of wasm-tools' tests/cli scripts as argument vectors.

Usage: run-lines.py SRC_ROOT

For every tests/cli/**/*.wast file under SRC_ROOT, each `;; RUN: wast ...` line (with `\\`
continuations on following `;;` lines) is printed as one line: the file (relative to SRC_ROOT),
a tab, then the arguments separated by tabs, `%` replaced by the file. Plain splitting on
whitespace (the RUN lines use no quoting).
"""
import os
import sys

root = sys.argv[1]
base = os.path.join(root, "tests", "cli")
for dirpath, _, names in sorted(os.walk(base)):
    for name in sorted(names):
        if not name.endswith(".wast"):
            continue
        rel = os.path.relpath(os.path.join(dirpath, name), root)
        with open(os.path.join(dirpath, name), encoding="utf-8", errors="replace") as f:
            lines = f.read().split("\n")
        i = 0
        while i < len(lines):
            line = lines[i]
            if line.startswith(";; RUN:"):
                cmd = line[len(";; RUN:"):].strip()
                while cmd.endswith("\\") and i + 1 < len(lines) and lines[i + 1].startswith(";;"):
                    i += 1
                    cmd = cmd[:-1].strip() + " " + lines[i][2:].strip()
                args = cmd.split()
                if args and args[0] == "wast":
                    print("\t".join([rel] + [rel if a == "%" else a for a in args]))
            i += 1
