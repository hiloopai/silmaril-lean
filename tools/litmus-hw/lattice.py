#!/usr/bin/env python3
"""Compare lattice_hw outcome counts with the lattice's verdicts.

Usage: python3 -I lattice.py RUN.txt [RUN.txt ...]   (one file per placement/delay)
       python3 -I lattice.py --markdown RUN.txt ...

Every witness outcome (an outcome some model of the lattice forbids) has a candidate
execution and a verdict row proved in `Silmaril.X86.MemoryModel.Lattice.Witness.Thms`
(`<name>_row`). Every other outcome of these tests is sequentially consistent (an
interleaving), so every model allows it.

Checks (exit status 1 if one fails):
  * TSO soundness: no outcome x86-TSO forbids is observed on a test x86-TSO covers (aligned
    write-back accesses, locked instructions, fences);
  * XL soundness: no outcome XL forbids is observed on any test;
  * the rows respect the proved order (sc ⊑ tso ⊑ xl, tso ⊑ ra ⊑ cfPlain, tso ⊑ cf ⊑ cfPlain).
Reported: for each strict edge M ⊏ N of the lattice, whether its separating outcomes were
observed (hardware outside M) or not."""
import sys

MODELS = ("sc", "tso", "ra", "xl", "cf", "cfPlain")
EDGES = [("sc", "tso"), ("tso", "xl"), ("tso", "ra"), ("tso", "cf"), ("ra", "cfPlain"),
         ("cf", "cfPlain"), ("xl", "top"), ("cfPlain", "top")]
LE = {("sc", "tso"), ("tso", "xl"), ("tso", "ra"), ("tso", "cf"), ("ra", "cfPlain"),
      ("cf", "cfPlain")}


def row(bits):
    return dict(zip(MODELS, (c == "1" for c in bits)))


# test -> (coverage, {witness outcome: (execution, row sc tso ra xl cf cfPlain)})
TESTS = {
    "SB": ("tso", {"0:r0=0 1:r0=0": ("Sanity.sb", row("011111"))}),
    "SB+mfences": ("tso", {"0:r0=0 1:r0=0": ("Sanity.sbMfence", row("001011"))}),
    "SB+xchgs": ("tso", {"0:r0=0 1:r0=0": ("sbXchg", row("001011"))}),
    "MP": ("tso", {"1:r0=1 1:r1=0": ("Lattice.mp", row("000000"))}),
    "LB": ("tso", {"0:r0=1 1:r0=1": ("Lattice.lb", row("000000"))}),
    "IRIW": ("tso", {"2:r0=1 2:r1=0 3:r0=1 3:r1=0": ("Lattice.iriw", row("001011"))}),
    "2+2W": ("tso", {"x=1 y=1": ("Lattice.w22", row("001011"))}),
    "MP+movnti": ("xl", {"1:r0=1 1:r1=0": ("Sanity.mpNt", row("000100"))}),
    "MP+movnti+sfence": ("xl", {"1:r0=1 1:r1=0": ("Sanity.mpNtSfence", row("000000"))}),
    "SPLIT8": ("xl", {"1:r0=torn": ("Sanity.torn", row("000111"))}),
    "TORN2-inline": ("xl", {"1:r0=torn": ("Sanity.torn", row("000111"))}),
    "TORN2-cross": ("xl", {"1:r0=torn": ("Sanity.torn", row("000111"))}),
    "INC2": ("tso", {"x=1": ("inc2", row("111111"))}),
    "LOCKINC2": ("tso", {"x=1": ("Sanity.lockInc", row("000001"))}),
    "CoWR": ("tso", {"0:r0=0 x=1": ("coWR2", row("000011")), "0:r0=0 x=2": ("coWR2", row("000011")),
                     "0:r0=2 x=1": ("coWR2b", row("000011"))}),
}
ROW_THM = {"Sanity.sb": "sb_row", "Sanity.sbMfence": "sbMfence_row", "sbXchg": "sbXchg_row",
           "Lattice.mp": "mp_row", "Lattice.lb": "lb_row", "Lattice.iriw": "iriw_row",
           "Lattice.w22": "w22_row", "Sanity.mpNt": "mpNt_row", "Sanity.mpNtSfence": "mpNtSfence_row",
           "Sanity.torn": "torn_row", "inc2": "inc2_row", "Sanity.lockInc": "lockInc_row",
           "coWR2": "coWR2_row", "coWR2b": "coWR2b_row"}


def allowed(test, outcome, model):
    if model == "top":
        return True
    w = TESTS[test][1].get(outcome)
    return True if w is None else w[1][model]


def load(path):
    counts = {}
    for line in open(path):
        test, outcome, n = line.rstrip("\n").split("\t")
        counts.setdefault(test, {})
        counts[test][outcome] = counts[test].get(outcome, 0) + int(n)
    return counts


def main(argv):
    md = "--markdown" in argv
    paths = [a for a in argv if not a.startswith("--")]
    runs = {p: load(p) for p in paths}
    bad = 0
    # the rows respect the order
    for test, (_, ws) in TESTS.items():
        for o, (x, r) in ws.items():
            for lo, hi in LE:
                if r[lo] and not r[hi]:
                    print(f"ORDER VIOLATION: {x} allowed by {lo}, forbidden by {hi}")
                    bad += 1
    total = {}
    for counts in runs.values():
        for test, oc in counts.items():
            for o, n in oc.items():
                total.setdefault(test, {})
                total[test][o] = total[test].get(o, 0) + n
    # soundness
    for path, counts in runs.items():
        for test, oc in counts.items():
            cov, ws = TESTS[test]
            for o, n in oc.items():
                for m in (("tso", "xl") if cov == "tso" else ("xl",)):
                    if not allowed(test, o, m):
                        print(f"MODEL BUG ({path}): {test} {o} observed {n} times, {m} forbids it "
                              f"({ws[o][0]}, Witness.{ROW_THM[ws[o][0]]})")
                        bad += 1
    if md:
        names = [p.rsplit("/", 1)[-1].removesuffix(".txt") for p in paths]
        print("| test | covered by | witness outcome | execution (`Witness.*_row`) | sc | tso | ra | xl | cf | cfPlain | "
              + " | ".join(names) + " |")
        print("|---|---|---|---|---|---|---|---|---|---|" + "---|" * len(names))
        for test, (cov, ws) in TESTS.items():
            for o, (x, r) in ws.items():
                obs = [str(runs[p].get(test, {}).get(o, 0)) for p in paths]
                its = [str(sum(runs[p].get(test, {}).values())) for p in paths]
                cells = " | ".join(f"{a} / {b}" for a, b in zip(obs, its))
                v = " | ".join("✓" if r[m] else "✗" for m in MODELS)
                print(f"| {test} | {cov} | `{o}` | `{x}` | {v} | {cells} |")
        print()
        print("| edge | separating outcomes (allowed by the upper model, forbidden by the lower) | observed on hardware |")
        print("|---|---|---|")
    for lo, hi in EDGES:
        seps = [(t, o) for t, (cov, ws) in TESTS.items() for o in ws
                if allowed(t, o, hi) and not allowed(t, o, lo)]
        seen = [(t, o, total.get(t, {}).get(o, 0)) for t, o in seps]
        shown = ", ".join(f"{t}{'' if TESTS[t][0] == 'tso' else ' (XL-only)'} `{o}`: {n}"
                          for t, o, n in seen)
        hit = any(n for _, _, n in seen)
        hit_tso = any(n for t, _, n in seen if TESTS[t][0] == "tso")
        if md:
            verdict = ("yes, on TSO-covered tests" if hit_tso else
                       "only on XL-only tests (misaligned or non-temporal)" if hit else "no")
            print(f"| {lo} ⊏ {hi} | {shown} | {verdict} |")
        else:
            print(f"{lo} < {hi}: {shown} -> "
                  + ("observed on TSO-covered tests" if hit_tso else
                     "observed on XL-only tests only" if hit else "never observed"))
    if not md:
        for test in TESTS:
            oc = total.get(test, {})
            print(f"{test}: {sum(oc.values())} iterations, {len(oc)} outcomes: "
                  + ", ".join(f"{o}: {n}" for o, n in sorted(oc.items())))
    print("OK: every observed outcome is allowed by every model covering its test"
          if bad == 0 else f"{bad} violations")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main(sys.argv[1:])
