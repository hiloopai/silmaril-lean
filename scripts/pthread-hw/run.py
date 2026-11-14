#!/usr/bin/env python3
"""Run the pinned pthread binaries many times and check every observed outcome
against the outcome set the simple pthread model predicts
(Silmaril.Process.Mt.Pthread.Simple; the expected sets are below).

    python3 -I run.py BINDIR [RUNS] [SB_ITERS]

Exit status 0 iff every observed outcome is allowed. A run that never shows an
allowed outcome does not prove it impossible, and a run that shows only one
outcome does not prove the program deterministic: the harness only shows what
this machine produced."""
import collections, os, re, subprocess, sys

N = 100000
EXPECTED = {
    # program: (predicate on the output line, description of the predicted set)
    "p1_mutex_counter": (lambda o: o == str(2 * N), "{200000}"),
    "p2_prodcons_cond": (lambda o: o == str(20000 * 20001 // 2), "{200010000}"),
    "p3_once": (lambda o: o == "1 4", "{'1 4'}"),
    "p4_tls_keys": (lambda o: o == "4 4 0", "{'4 4 0'}"),
    "p5_racy_counter": (lambda o: o.isdigit() and 2 <= int(o) <= 2 * N, "[2, 200000]"),
    "p6_spin_counter": (lambda o: o == str(2 * N), "{200000}"),
    "p7_sem_barrier": (lambda o: o == "ab" * 10 + " 4 1", "{'abab...ab 4 1'}"),
    "p8_mutex_errors": (lambda o: o == "ec 0 35 1 0 rec 0 0 0 0 1 try 16 spin 0 16 sem -1 11 "
                        "rw 0 0 16 0 35 join 35", "{the POSIX/glibc codes}"),
}

def main():
    bindir = sys.argv[1]
    runs = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    sb = sys.argv[3] if len(sys.argv) > 3 else "2000000"
    ok = True
    for prog, (allowed, desc) in EXPECTED.items():
        hist = collections.Counter()
        for _ in range(runs):
            out = subprocess.run([os.path.join(bindir, prog)], capture_output=True, text=True,
                                 timeout=120).stdout.strip()
            hist[out] += 1
        bad = [o for o in hist if not allowed(o)]
        ok &= not bad
        if prog == "p5_racy_counter":
            vals = sorted(int(o) for o in hist if o.isdigit())
            shown = (f"{len(hist)} distinct outcomes, min {vals[0]}, max {vals[-1]}, "
                     f"{hist[str(2 * N)]} runs at 2N")
        else:
            shown = dict(hist)
        print(f"{prog}: {runs} runs, predicted {desc}, observed {shown}"
              + (f"  UNEXPECTED {bad}" if bad else ""))
    # x1: unlock as a barrier
    out = subprocess.run([os.path.join(bindir, "x1_unlock_fence"), sb], capture_output=True,
                         text=True, timeout=3600).stdout
    print(out, end="")
    weak = {m.group(1): int(m.group(2)) for m in re.finditer(r"SB\+(\S+):.*?00: (\d+)", out)}
    # TSO forbids the weak outcome when both threads run a barrier between store and load
    for v in ("mutex_unlock", "mfence"):
        if weak.get(v, 1) != 0:
            ok = False
            print(f"UNEXPECTED: SB+{v} weak outcome seen {weak.get(v)} times")
    print(f"spin_unlock is {'not ' if weak.get('spin_unlock', 0) > 0 else ''}observed to be a barrier "
          f"(weak outcome {weak.get('spin_unlock')} times; x86-TSO allows it for a plain store)")
    # x2: representations
    out = subprocess.run([os.path.join(bindir, "x2_lockword")], capture_output=True, text=True,
                         timeout=600).stdout.strip()
    print(out)
    f = dict(re.findall(r"(\w+(?:\(st\))?) (-?\d+(?:->-?\d+)?)", out.split(" spin ")[0]))
    checks = [f.get("single_threaded") == "1->0", f.get("free") == "0", f.get("held(st)") == "1",
              f.get("held") == "1", f.get("owner") == "1", f.get("waiters") == "2",
              f.get("after") == "0", f.get("owner_after") == "0"]
    sp = re.search(r"spin free (-?\d+) held (-?\d+) contended (-?\d+) min (-?\d+) end (-?\d+)", out)
    if sp:
        free_, held, cont, mn, end = map(int, sp.groups())
        checks += [free_ == 1, held == 0, cont <= 0, -4 <= mn <= 0, end == 1]
    else:
        checks.append(False)
    if not all(checks):
        ok = False
        print(f"UNEXPECTED representation: {checks}")
    print("OK: every observed outcome is allowed" if ok else "FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
