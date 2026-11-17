#!/usr/bin/env python3
"""The GCC C torture suite through the C translation-validation pipeline (docs/projects/c-tv.md, stage 4).

    scripts/c-tv/torture.py --root GCC/gcc/testsuite/gcc.c-torture [--jobs N] [--limit N] [--filter RE]
                            [--out benchmarks/gcc-torture/tv-report.json]

The denominator is every case of benchmarks/gcc-torture/manifest.json (3,852 C files of GCC 14.3.0,
`c9cd41fb`). Every case gets exactly one status; nothing is dropped from the denominator:

  not-attempted        excluded by --limit/--filter (or the source's SHA-256 differs from the manifest)
  harness-needed       the case needs DejaGNU harness behaviour the runner does not interpret: a
                       `.x` script next to it, or execute/builtins (extra sources linked)
  frontend-rejected    neither frontend produced typed Ail (each route's reason is recorded)
  elaborator-rejected  typed Ail from some route, but the Lean elaborator rejected every route
  no-main              a compile/ case that elaborated but has no `main`: no whole-program behaviour
                       (its evidence is the frontend and elaborator acceptance only)
  gap                  some Core exploration reached a gap (`error`/`unsupported`) or a stuck state
  unknown              every elaborated route's exploration hit its bounds
  explored             one route elaborated and was explored exhaustively (no cross-validation)
  cross-validated      two routes elaborated, explored exhaustively, and validated both ways
  refuted              the two routes' Cores were found not to refine each other (a frontend disagreement)
  timeout / tool-error the pipeline did not finish / a tool failed unexpectedly

and, separately, facts that are not statuses:

  coreAllowsPass       for execute/ cases: `Spec.check` of the observation "exit 0, no output" (how a
                       torture test reports success) against each elaborated Core: admitted /
                       rejected / unknown. A semantic check of the test against the Core, not TV.
  profileIncoherent    the typed Ail mentions `float`, `long double` or `wchar_t`, at which the profile
                       linuxX86_64 is not coherent with the Core semantics (the result is about the
                       port's legacy model there)
  ubReached            some exploration reached undefined behaviour (the test depends on UB, or the
                       port's semantics differs from GCC's assumptions)
  native               gcc -O0 run of execute/ cases: exit status (sanity only, not validation)

Every verdict is compiled evidence (`ctv-pipeline`), not a kernel theorem. Execution comparisons
are sanity checks. The report records the tool versions and the manifest's SHA-256.
"""
import argparse, concurrent.futures as cf, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MANIFEST = os.path.join(ROOT, "benchmarks", "gcc-torture", "manifest.json")
RUNTIME = os.path.join(ROOT, "benchmarks", "cerberus-elaboration", "oracle", "constant-return", "core.sexp.gz")
TARGET = "x86_64-linux-gnu"


def run(cmd, cwd, timeout):
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return "timeout", b"", b""


def reason(out):
    t = out.decode(errors="replace")
    m = re.search(r'\(\$str "([^"]*)"\)\)?\s*$', t.strip().splitlines()[0] if t.strip() else "")
    return (m.group(1) if m else t.strip()[-300:])[:300]


def max_symbol(texts):
    best = 0
    for t in texts:
        for m in re.finditer(r'\(Symbol \(\$str "[0-9a-f]*"\) (\d+)', t):
            best = max(best, int(m.group(1)))
    return best + 1


def one(case, root, binary, sums, timeouts):
    row = {"case": case}
    src = os.path.join(root, case)
    data = open(src, "rb").read()
    if hashlib.sha256(data).hexdigest() != sums[case]:
        row["status"] = "not-attempted"; row["why"] = "SHA-256 differs from the manifest"; return row
    stem = os.path.splitext(src)[0]
    if os.path.exists(stem + ".x") or case.startswith("execute/builtins/"):
        row["status"] = "harness-needed"
        row["why"] = ".x script" if os.path.exists(stem + ".x") else "execute/builtins links extra sources"
        return row
    tmp = tempfile.mkdtemp(prefix="ctv-")
    try:
        shutil.copyfile(src, os.path.join(tmp, "t.c"))
        rc, _, err = run(["gcc", "-E", "-P", "-std=gnu11", "-w", "t.c", "-o", "t.i"], tmp, 60)
        if rc != 0:
            row["status"] = "frontend-rejected"; row["routes"] = {"preprocess": err.decode(errors="replace")[-300:]}; return row
        routes, why = [], {}
        rc, so, se = run([os.path.join(binary, "cerb-lean"), "parse", "--level", "tail", "t.i"], tmp, timeouts)
        if rc == 0:
            open(os.path.join(tmp, "cerberus.tail.sexp"), "wb").write(so); routes.append("cerberus")
        else:
            why["cerberus"] = "timeout" if rc == "timeout" else reason(so + se)
        rc, so, se = run(["clang", "-x", "c", "-std=gnu11", "-target", TARGET, "-w", "-Xclang", "-ast-dump=json", "-fsyntax-only", "t.i"], tmp, timeouts)
        if rc == 0:
            open(os.path.join(tmp, "ast.json"), "wb").write(so)
            rc, so, se = run([os.path.join(binary, "cfront"), "ail", "ast.json"], tmp, timeouts)
            if rc == 0:
                open(os.path.join(tmp, "clang.tail.sexp"), "wb").write(so); routes.append("clang")
            else:
                why["clang"] = "timeout" if rc == "timeout" else reason(so + se)
        else:
            why["clang"] = "clang: " + ("timeout" if rc == "timeout" else se.decode(errors="replace").strip().splitlines()[0][:300] if se.strip() else str(rc))
        row["routes"] = why
        if not routes:
            row["status"] = "frontend-rejected"; return row
        observes = []
        if case.startswith("execute/"):
            open(os.path.join(tmp, "empty.out"), "wb").close()
            observes += ["--observe", "pass", "0", "empty.out"]
            rc, _, _ = run(["gcc", "-O0", "-std=gnu11", "-w", "t.c", "-o", "t.exe", "-lm"], tmp, 60)
            if rc == 0:
                rc, so, _ = run([os.path.join(tmp, "t.exe")], tmp, 10)
                row["native"] = "timeout" if rc == "timeout" else (f"signal {-rc}" if rc < 0 else f"exit {rc}")
            else:
                row["native"] = "build failed"
        fresh = max_symbol([open(os.path.join(tmp, f"{r}.tail.sexp"), errors="replace").read() for r in routes])
        rc, so, se = run([os.path.join(binary, "ctv-pipeline"), "run", RUNTIME, str(fresh), ".", "--depth", "200000", "--budget", "2000000"]
                         + observes + [f"{r}={r}.tail.sexp" for r in routes], tmp, timeouts * 4)
        if rc == "timeout":
            row["status"] = "timeout"; return row
        if rc != 0:
            row["status"] = "tool-error"; row["why"] = se.decode(errors="replace")[-300:]; return row
        rep = json.loads(so)
        el = {k: v for k, v in rep["routes"].items() if v["status"] == "elaborated"}
        for k, v in rep["routes"].items():
            if v["status"] != "elaborated":
                why[k] = f'{v.get("stage", v["status"])}: {v.get("why", "")}'[:300]
        if not el:
            row["status"] = "elaborator-rejected"; return row
        ex = {k: v["explore"] for k, v in el.items()}
        row["endings"] = {k: sorted({json.dumps(e["outcome"], sort_keys=True) for e in x["sample"]})[:4] for k, x in ex.items()}
        # Types at which the profile (linuxX86_64) is not coherent with the Core semantics.
        tails = "".join(open(os.path.join(tmp, f"{r}.tail.sexp"), errors="replace").read() for r in el)
        inc = [n for n, pat in [("float", "(RealFloating (Float)"), ("long double", "(RealFloating (LongDouble)"), ("wchar_t", "(Wchar")] if pat in tails]
        if inc:
            row["profileIncoherent"] = inc
        row["ubReached"] = any(x["ub"] for x in ex.values())
        if observes:
            row["coreAllowsPass"] = {o["name"]: o["check"] for o in rep["observations"]}.get("pass", {})
        no_main = all(any('"error"' in e and "no startup function" in e for e in row["endings"][k]) for k in ex)
        if case.startswith("compile/") and no_main:
            row["status"] = "no-main"
        elif any(x["gap"] or x["stuck"] for x in ex.values()):
            row["status"] = "gap"
        elif all(x["limited"] for x in ex.values()):
            row["status"] = "unknown"
        else:
            verdicts = [p["verdict"] for p in rep["pairs"]]
            row["pairs"] = {f'{p["source"]}->{p["target"]}': p["verdict"] for p in rep["pairs"]}
            if len(el) == 2 and verdicts and all(v == "validated" for v in verdicts):
                row["status"] = "cross-validated"
            elif "refuted" in verdicts:
                row["status"] = "refuted"
            elif any(not x["limited"] for x in ex.values()):
                row["status"] = "explored"
            else:
                row["status"] = "unknown"
        return row
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def version(cmd):
    try:
        return subprocess.run(cmd, capture_output=True).stdout.decode().splitlines()[0]
    except Exception:
        return "unknown"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--bin", default=os.path.join(ROOT, ".lake", "build", "bin"))
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--limit", type=int)
    ap.add_argument("--filter")
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--out", default=os.path.join(ROOT, "benchmarks", "gcc-torture", "tv-report.json"))
    # (the stored report is gzip -n -9 of this file: benchmarks/gcc-torture/tv-report.json.gz)
    a = ap.parse_args()
    man = json.load(open(MANIFEST))
    sums = {i["path"]: i["sha256"] for i in man["inputs"]}
    cases = man["cases"]
    chosen = [c for c in cases if not a.filter or re.search(a.filter, c)]
    if a.limit is not None:
        chosen = chosen[:a.limit]
    rows = {c: {"case": c, "status": "not-attempted", "why": "excluded by --filter/--limit"} for c in cases if c not in set(chosen)}
    start = time.time()
    with cf.ThreadPoolExecutor(a.jobs) as pool:
        futs = {pool.submit(one, c, a.root, os.path.abspath(a.bin), sums, a.timeout): c for c in chosen}
        for i, f in enumerate(cf.as_completed(futs)):
            c = futs[f]
            try:
                rows[c] = f.result()
            except Exception as e:
                rows[c] = {"case": c, "status": "tool-error", "why": repr(e)[:300]}
            if i % 200 == 0:
                print(f"{i}/{len(chosen)} {time.time() - start:.0f}s", file=sys.stderr, flush=True)
    ordered = [rows[c] for c in cases]
    statuses = ["not-attempted", "harness-needed", "frontend-rejected", "elaborator-rejected", "no-main", "gap", "unknown",
                "explored", "cross-validated", "refuted", "timeout", "tool-error"]
    summary = {s: sum(1 for r in ordered if r["status"] == s) for s in statuses}
    assert sum(summary.values()) == len(cases)
    for part in ["compile/", "execute/"]:
        summary[part] = {s: sum(1 for r in ordered if r["status"] == s and r["case"].startswith(part)) for s in statuses}
    summary["profileIncoherent"] = sum(1 for r in ordered if r.get("profileIncoherent"))
    summary["ubReached"] = sum(1 for r in ordered if r.get("ubReached"))
    summary["coreAllowsPass"] = {v: sum(1 for r in ordered if v in (r.get("coreAllowsPass") or {}).values()) for v in ["admitted", "rejected", "unknown"]}
    rep = {"schema": "silmaril.c-tv.gcc-torture.v1",
           "manifest": {"path": "benchmarks/gcc-torture/manifest.json",
                        "sha256": hashlib.sha256(open(MANIFEST, "rb").read()).hexdigest(),
                        "revision": man["revision"], "repository": man["repository"]},
           "denominator": len(cases), "attempted": len(chosen),
           "tools": {"gcc": version(["gcc", "--version"]), "clang": version(["clang", "--version"]),
                     "cerb-lean": hashlib.sha256(open(os.path.join(a.bin, "cerb-lean"), "rb").read()).hexdigest(),
                     "cfront": hashlib.sha256(open(os.path.join(a.bin, "cfront"), "rb").read()).hexdigest(),
                     "ctv-pipeline": hashlib.sha256(open(os.path.join(a.bin, "ctv-pipeline"), "rb").read()).hexdigest()},
           "evidence": "compiled", "seconds": round(time.time() - start), "summary": summary, "cases": ordered}
    with open(a.out, "w") as f:
        json.dump(rep, f, indent=None, separators=(",", ":"), sort_keys=True)
        f.write("\n")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
