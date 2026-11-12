#!/usr/bin/env python3
"""Print the definitions of tools/wasm-tools/WasmTools/HelpV.lean: upstream's -h/--help output of
validate, strip, objdump and dump, from the pinned wasm-tools 1.262.0 (python3 -I).

python3 -I tools/wasm-tools/tests/gen-helpv.py UPSTREAM
"""
import subprocess
import sys


def lit(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'


upstream = sys.argv[1]
for cmd in ["validate", "strip", "objdump", "dump"]:
    for flag, name in (("-h", "short"), ("--help", "long")):
        out = subprocess.run([upstream, cmd, flag], capture_output=True, check=True).stdout.decode()
        print(f"def {cmd}_{name} : String :=\n  {lit(out)}\n")
