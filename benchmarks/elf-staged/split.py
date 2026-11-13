"""Split a module emitted by `elf-staged emit` into one file per stage, for timing.

    python3 -I split.py BENCH.lean OUTDIR      prints the stage names, one per line

Each output keeps the shared prefix (imports, `include_bytes`, pages, the layout literal) and
the theorems of one stage; `none` keeps only the prefix. The `rela_*` windows form one stage.
"""
import os
import re
import sys

src, outdir = sys.argv[1], sys.argv[2]
blocks = open(src).read().split("\n\n")


def stage(block):
    m = re.search(r"^theorem (\S+)", block, re.M)
    if not m or m.group(1) == "hc":
        return None
    name = m.group(1)
    return "rela" if name.startswith("rela_") else name


stages = []
for b in blocks:
    s = stage(b)
    if s and s not in stages:
        stages.append(s)
os.makedirs(outdir, exist_ok=True)
for name in ["none"] + stages:
    body = "\n\n".join(b for b in blocks if stage(b) in (None, name))
    with open(os.path.join(outdir, name + ".lean"), "w") as f:
        f.write(body)
    print(name)
