#!/usr/bin/env python3
"""Compare litmus_hw outcome counts with the model verdicts.

Usage: ./litmus_hw 2000000 | python3 check.py

For each test, FORBID lists the outcome keys (as litmus_hw encodes them) that a
model forbids, with the Lean statement that proves the verdict. The script
fails if hardware shows an outcome that x86-TSO forbids on a TSO-covered test,
or one XL forbids on any test, and reports which separating outcomes were seen.
"""
import sys

# test -> (coverage, {model: forbidden keys}, separating key or None, Lean source)
TESTS = {
    "SB": ("tso", {"sc": {0}, "tso": set(), "xl": set()}, 0,
           "Xl.Thms Sanity.sb_verdict; Lattice.Thms sep_sc_tso"),
    "SB+mfences": ("tso", {"sc": {0}, "tso": {0}, "xl": {0}}, None,
                   "Xl.Thms Sanity.sbMfence_verdict"),
    "SB+xchgs": ("tso", {"sc": {0}, "tso": {0}, "xl": {0}}, None,
                 "x86tso.cat: implied (locked write before read)"),
    "MP": ("tso", {"sc": {2}, "tso": {2}, "xl": {2}}, None, "Lattice.Thms weak_verdicts (mp)"),
    "LB": ("tso", {"sc": {3}, "tso": {3}, "xl": {3}}, None, "Lattice.Thms weak_verdicts (lb)"),
    # IRIW key = r2x*8 + r2y*4 + r3y*2 + r3x; weak: T2 sees x=1,y=0, T3 sees y=1,x=0
    "IRIW": ("tso", {"sc": {10}, "tso": {10}, "xl": {10}}, None,
             "Lattice.Thms sep_tso_ra (allowed by RA only)"),
    # 2+2W key = x*3 + y; weak final x=1, y=1
    "2+2W": ("tso", {"sc": {4}, "tso": {4}, "xl": {4}}, None,
             "Lattice.Thms weak_verdicts (w22; allowed by RA)"),
    "MP+movnti": ("xl", {"sc": {2}, "tso": {2}, "xl": set()}, 2,
                  "Xl.Thms Sanity.mpNt_verdict; Lattice.Thms sep_tso_xl"),
    "MP+movnti+sfence": ("xl", {"sc": {2}, "tso": {2}, "xl": {2}}, None,
                         "Xl.Thms Sanity.mpNtSfence_verdict"),
    # SPLIT8 key: 0 old, 1 new, 2 torn
    "SPLIT8": ("xl", {"sc": {2}, "tso": {2}, "xl": set()}, 2,
               "Xl.Thms Sanity.torn_verdict; Lattice.Thms sep_tso_xl_torn"),
    # unlocked inc is a load and a store: final 1 is allowed even by SC
    "INC2": ("tso", {"sc": set(), "tso": set(), "xl": set()}, None, "SC interleaving"),
    "LOCKINC2": ("tso", {"sc": {1}, "tso": {1}, "xl": {1}}, None,
                 "Xl.Thms Sanity.lockInc_verdict (atomicity)"),
}

counts = {}
for line in sys.stdin:
    name, key, n = line.split()
    counts.setdefault(name, {})[int(key)] = int(n)

bad = 0
for name, (cov, forbid, sep, src) in TESTS.items():
    seen = counts.get(name, {})
    total = sum(seen.values())
    for model in ("sc", "tso", "xl"):
        hits = {k: seen[k] for k in forbid[model] if k in seen}
        if hits and (model == "xl" or (model == "tso" and cov == "tso")):
            print(f"VIOLATION {name}: {model} forbids {hits} [{src}]")
            bad += 1
    note = ""
    if sep is not None:
        note = f"; separating outcome {sep} seen {seen.get(sep, 0)} times"
    print(f"{name}: {total} runs, outcomes {dict(sorted(seen.items()))}{note}")
print("OK: every observed outcome is allowed by its model" if bad == 0 else f"{bad} violations")
sys.exit(1 if bad else 0)
