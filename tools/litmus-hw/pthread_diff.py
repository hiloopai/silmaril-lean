#!/usr/bin/env python3
"""Differential testing of the pthread programs against the simple pthread model.

For each program of scripts/pthread-hw/src, at its full size (the pinned binaries) and at
small loop bounds (rebuilt with -DN=…/-DK=…/-DR=…), run the binary many times under every
configuration of

  * libc:      the host's glibc, and the pinned glibc 2.39-0ubuntu8.9 (run through its own
               dynamic loader, `ld-linux-x86-64.so.2 --library-path DIR`);
  * placement: any CPU, one CPU (0), two SMT siblings (0,6 on the recording machine), two
               cores (0,1);
  * schedule:  unperturbed, or perturbed by perturb.so (random sched_yield, random spins
               and, with placement `any`, random migrations around every pthread call and
               at thread start; the binary's bytes are unchanged);

and compare the observed outputs with the model's outcome set: the exhaustive exploration of
simple_model.py for the explored sizes (p3, p7 and p8 are explored at full size), the
predicted sets of the expected outcomes for the others (p1, p6: {2N}; p2: {N(N+1)/2}; p5:
[2, 2N]; p4: {"4 4 0"}). Every observed output must be in the model's set; the report lists
the model outcomes that were never observed.

Usage: python3 -I pthread_diff.py OUTDIR [SMALL_RUNS] [FULL_RUNS]
  Environment: PINNED_LIBC_DIR (default: none; the pinned-libc configurations are skipped
  without it), SMT_PAIR (default 0,6), CORE_PAIR (default 0,1).
Writes OUTDIR/diff.json and prints a table."""
import collections
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "..", "scripts", "pthread-hw", "src")
sys.path.insert(0, HERE)
import simple_model  # noqa: E402

CFLAGS = ["-O2", "-Wall", "-Werror", "-pthread", "-fno-stack-protector", "-fcf-protection=none"]
SRCS = {"p1": "p1_mutex_counter", "p2": "p2_prodcons_cond", "p3": "p3_once", "p4": "p4_tls_keys",
        "p5": "p5_racy_counter", "p6": "p6_spin_counter", "p7": "p7_sem_barrier",
        "p8": "p8_mutex_errors"}
MACRO = {"p1": "N", "p2": "N", "p4": "K", "p5": "N", "p6": "N", "p7": "R"}
FULL = {"p1": 100000, "p2": 20000, "p3": None, "p4": 1000, "p5": 100000, "p6": 100000, "p7": 10,
        "p8": None}
# variants: (program, parameter) -- None = full size (the pinned binary)
SMALL = [("p1", 2), ("p1", 3), ("p2", 2), ("p2", 3), ("p4", 1), ("p4", 2), ("p5", 1), ("p5", 2),
         ("p5", 3), ("p5", 4), ("p6", 2), ("p6", 3), ("p7", 1), ("p7", 2)]
FULLV = [(p, None) for p in SRCS]
EXPLORE_FULL = {"p3", "p7", "p8"}


def model_output(prog, text):
    """The binary's output line as the model's output list (space-separated naturals)."""
    t = text.strip()
    if prog == "p7":
        log, a, b = t.split()
        return " ".join([str(ord(c)) for c in log] + [a, b])
    if prog == "p8":
        nums = [int(w) for w in t.split() if w.lstrip("-").isdigit()]
        return " ".join(str(n % 2**32) for n in nums)
    return t


def predicted(prog, param):
    n = FULL[prog] if param is None else param
    if param is not None or prog in EXPLORE_FULL:
        spec = prog if (param is None) else f"{prog}:{param}"
        r = simple_model.run(spec)
        return set(r["outcomes"]), f"explored ({r['configs']} configurations)"
    if prog in ("p1", "p6"):
        return {str(2 * n)}, "predicted {2N}"
    if prog == "p2":
        return {str(n * (n + 1) // 2)}, "predicted {N(N+1)/2}"
    if prog == "p5":
        return {str(v) for v in range(2, 2 * n + 1)}, "predicted [2, 2N]"
    if prog == "p4":
        return {"4 4 0"}, "predicted"
    raise ValueError(prog)


def build(out, prog, param):
    name = SRCS[prog] + ("" if param is None else f"_{MACRO[prog]}{param}")
    exe = os.path.join(out, "bin", name)
    os.makedirs(os.path.dirname(exe), exist_ok=True)
    defs = [] if param is None else [f"-D{MACRO[prog]}={param}"]
    subprocess.run(["gcc", *CFLAGS, *defs, os.path.join(SRC, SRCS[prog] + ".c"), "-o", exe], check=True)
    return exe


def configs(pinned_dir):
    smt = os.environ.get("SMT_PAIR", "0,6")
    core = os.environ.get("CORE_PAIR", "0,1")
    libcs = ["host"] + (["pinned"] if pinned_dir else [])
    for libc in libcs:
        for place, cpus in (("any", None), ("one", "0"), ("smt", smt), ("cores", core)):
            for pert in ("off", "on"):
                yield libc, place, cpus, pert


def command(exe, libc, cpus, pert, shim, pinned_dir, full):
    env = dict(os.environ)
    cmd = []
    if cpus:
        cmd += ["taskset", "-c", cpus]
    if libc == "pinned":
        cmd += [os.path.join(pinned_dir, "ld-linux-x86-64.so.2"), "--library-path", pinned_dir]
        if pert == "on":
            cmd += ["--preload", shim]
    elif pert == "on":
        env["LD_PRELOAD"] = shim
    if pert == "on":
        env["PERTURB_P"] = "20" if full else "300"
        env["PERTURB_SPIN"] = "2000" if full else "5000"
        env["PERTURB_MIGRATE"] = ("1" if full else "50") if cpus is None else "0"
    return cmd + [exe], env


def main():
    out = sys.argv[1]
    small_runs = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    full_runs = int(sys.argv[3]) if len(sys.argv) > 3 else 50
    pinned_dir = os.environ.get("PINNED_LIBC_DIR")
    os.makedirs(out, exist_ok=True)
    shim = os.path.join(out, "perturb.so")
    subprocess.run(["gcc", "-O2", "-Wall", "-Werror", "-shared", "-fPIC", os.path.join(HERE, "perturb.c"),
                    "-o", shim, "-ldl"], check=True)
    report = {"variants": {}, "ok": True}
    for prog, param in SMALL + FULLV:
        key = prog if param is None else f"{prog}:{param}"
        exe = build(out, prog, param)
        allowed, how = predicted(prog, param)
        runs = full_runs if param is None else small_runs
        v = {"allowed": sorted(allowed), "how": how, "configs": {}}
        union = collections.Counter()
        for libc, place, cpus, pert in configs(pinned_dir):
            cmd, env = command(exe, libc, cpus, pert, shim, pinned_dir, param is None)
            hist = collections.Counter()
            for _ in range(runs):
                try:
                    p = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=600)
                    o = model_output(prog, p.stdout) if p.returncode == 0 else f"exit {p.returncode}"
                except subprocess.TimeoutExpired:
                    o = "timeout"
                hist[o] += 1
            union.update(hist)
            bad = sorted(o for o in hist if o not in allowed)
            v["configs"][f"{libc}/{place}/{pert}"] = {"runs": runs, "observed": dict(hist), "unexpected": bad}
            if bad:
                report["ok"] = False
        v["observed"] = dict(union)
        v["unexpected"] = sorted(o for o in union if o not in allowed)
        v["unseen"] = sorted(o for o in allowed if o not in union)
        report["variants"][key] = v
        shown = (f"{len(union)} distinct, min {min(map(int, union))}, max {max(map(int, union))}"
                 if prog == "p5" and all(o.isdigit() for o in union) else dict(union))
        print(f"{key}: {sum(union.values())} runs, model {how}: {len(allowed)} outcomes; "
              f"observed {shown}; unexpected {v['unexpected']}; unseen {len(v['unseen'])}"
              + (f" {v['unseen']}" if len(v["unseen"]) <= 8 else ""), flush=True)
    with open(os.path.join(out, "diff.json"), "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("OK: every observed output is a model outcome" if report["ok"] else "FAIL: unexpected outputs")
    sys.exit(0 if report["ok"] else 1)


if __name__ == "__main__":
    main()
