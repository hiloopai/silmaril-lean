#!/usr/bin/env python3
"""Check the glibc code bytes transcribed in the ptmalloc proofs against the pinned files.

    scripts/ptmalloc/check-code.py DIR

DIR holds <pin>/libc.so.6 for each pin below (the `libc6` packages named in
docs/projects/ptmalloc.md). For every transcribed definition the script checks the file's
sha256 and that the Lean list literal is exactly the file's bytes at the given offset (`.text`
file offsets equal virtual addresses in these builds). Untrusted tooling: it ties the literals to
the files; the theorems are about the literals.
"""
import hashlib, pathlib, re, sys

PINS = {
    "ubuntu_2_39_0ubuntu8_9": "3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf",
    "ubuntu_2_40_1ubuntu3_1": "132ba50d4abaeff314e64f5d84daa4e4e6d9b227135bc035fde1b69a81aab204",
    "debian_2_36_9_deb12u14": "6b4a45352fd0c540a9c7c718f35ce8c8e46a4e482f9d3885a910c32d1a0e1421",
}
P = "Silmaril/Proofs/Libc/Ptmalloc/"
ROWS = [  # (module file, definition, pin, file offset, length)
    (P + "X86sim/V239/Code.lean", "mallocCode", "ubuntu_2_39_0ubuntu8_9", 0xad750, 796),
    (P + "X86sim/V239/Code.lean", "freeCode", "ubuntu_2_39_0ubuntu8_9", 0xade30, 272),
    (P + "X86sim/V239/Code.lean", "intFreeCode", "ubuntu_2_39_0ubuntu8_9", 0xab250, 897),
    (P + "Versions/V240/Code.lean", "mallocCode", "ubuntu_2_40_1ubuntu3_1", 0xb2c60, 820),
    (P + "Versions/V240/Code.lean", "freeCode", "ubuntu_2_40_1ubuntu3_1", 0xb3370, 271),
    (P + "Versions/V240/Code.lean", "intFreeCode", "ubuntu_2_40_1ubuntu3_1", 0xb07c0, 1019),
    (P + "Versions/V236/Code.lean", "mallocCode", "debian_2_36_9_deb12u14", 0x98930, 791),
]

def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip(), file=sys.stderr); return 2
    root = pathlib.Path(__file__).resolve().parents[2]
    pins = pathlib.Path(sys.argv[1])
    files, bad = {}, 0
    for pin, sha in PINS.items():
        data = (pins / pin / "libc.so.6").read_bytes()
        if hashlib.sha256(data).hexdigest() != sha:
            print(f"{pin}: sha256 mismatch"); bad += 1
        files[pin] = data
    for mod, name, pin, off, n in ROWS:
        text = (root / mod).read_text()
        m = re.search(r"def " + name + r" : List \(BitVec 8\) :=\s*\[(.*?)\]", text, re.S)
        if not m:
            print(f"{mod}: {name} not found"); bad += 1; continue
        lit = bytes(int(x, 16) for x in re.findall(r"0x([0-9a-f]{2})#8", m.group(1)))
        ok = lit == files[pin][off:off + n]
        print(f"{'ok ' if ok else 'BAD'} {mod} {name} ({pin} +{off:#x}, {n} bytes)")
        bad += not ok
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
