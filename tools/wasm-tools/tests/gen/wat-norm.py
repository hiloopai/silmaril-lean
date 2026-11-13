#!/usr/bin/env python3
"""Normalise wasmprinter text up to binary-encoding choices that do not change the module.

Usage: python3 -I wat-norm.py FILE      (prints the normalised text)

Used by fuzz-tools.sh to compare two texts of one module modulo:
* an empty `else` arm (`else` directly followed by `end`): present or absent in the binary;
* the encoding of an element segment of function indices: `(table 0)` spelled or not, and
  `(ref func) (ref.func N)...` (expression form) versus `func N...` (index form).
"""
import re
import sys

lines = open(sys.argv[1], encoding="utf-8", errors="replace").read().split("\n")
out = []
for i, line in enumerate(lines):
    if line.strip() == "else" and i + 1 < len(lines) and lines[i + 1].strip() == "end":
        continue
    if line.lstrip().startswith("(elem "):
        line = re.sub(r"^(\s*\(elem \(;\d+;\) )\(table 0\) ", r"\1", line)
        m = re.match(r"^(.*?(?:\) |declare ))\(ref func\)((?: \(ref\.func \d+\))*)\)$", line)
        if m:
            idx = re.findall(r"\(ref\.func (\d+)\)", m.group(2))
            line = m.group(1) + "func" + "".join(" " + x for x in idx) + ")"
    out.append(line)
sys.stdout.write("\n".join(out))
