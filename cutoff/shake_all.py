"""Run `lake shake --fix` over every module, dropping one side of each duplicate-declaration clash.

`lake shake` imports all requested modules into one environment, so two modules that declare the
same name cannot both be requested. On each clash this drops the side with fewer importers, plus
everything that imports it, and retries. Writes the dropped set to out/shake-excluded.json.
"""

import json
import re
import subprocess
import sys
from pathlib import Path

IMP = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)\s*$")
CLASH = re.compile(r"import (\S+) failed, environment already contains '[^']*' from (\S+)")


def strip_comments(t: str) -> str:
    out, i, n = [], 0, len(t)
    while i < n:
        if t.startswith("--", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
        elif t.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if t.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif t.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            out.append(t[i])
            i += 1
    return "".join(out)


def importers(paths: dict[str, Path]) -> dict[str, set[str]]:
    rev: dict[str, set[str]] = {m: set() for m in paths}
    for m, f in paths.items():
        for line in strip_comments(f.read_text(errors="replace")[:20000]).splitlines():
            s = line.strip()
            if not s or s in ("module", "prelude"):
                continue
            hit = IMP.match(s)
            if not hit:
                break
            if hit.group(4) in rev:
                rev[hit.group(4)].add(m)
    return rev


def closure(rev: dict[str, set[str]], m: str) -> set[str]:
    seen, stack = set(), [m]
    while stack:
        x = stack.pop()
        if x not in seen:
            seen.add(x)
            stack.extend(rev.get(x, ()))
    return seen


def main() -> None:
    paths = {".".join(f.with_suffix("").parts): f for f in Path("Silmaril").rglob("*.lean")}
    paths["Silmaril"] = Path("Silmaril.lean")
    paths["ProjectSelfTest"] = Path("examples/project/ProjectSelfTest.lean")
    rev = importers(paths)
    mods = set(paths)
    excluded: list[dict[str, object]] = []
    for attempt in range(200):
        proc = subprocess.run(["lake", "shake", "--fix", *sorted(mods)], capture_output=True, text=True)
        log = proc.stdout + proc.stderr
        Path("out/shake.log").write_text(log)
        clash = CLASH.search(log)
        if proc.returncode == 0 or not clash:
            break
        a, b = clash.group(1), clash.group(2)
        drop = min((a, b), key=lambda m: (len(closure(rev, m)), m))
        gone = closure(rev, drop) & mods
        excluded.append({"clash": [a, b], "dropped": drop, "with_importers": sorted(gone)})
        print(f"attempt {attempt}: {a} vs {b}; dropping {drop} and {len(gone) - 1} importers", flush=True)
        mods -= gone
    Path("out/shake-excluded.json").write_text(json.dumps(excluded, indent=1))
    Path("out/shake-mods.txt").write_text("\n".join(sorted(mods)) + "\n")
    print(f"shake rc={proc.returncode}; checked {len(mods)} modules; excluded {len(paths) - len(mods)}")
    sys.exit(proc.returncode)


if __name__ == "__main__":
    main()
