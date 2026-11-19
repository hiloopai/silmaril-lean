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
  cross-validated      two routes elaborated, explored exhaustively, and validated both ways, each
                       source exploration exhaustive without undefined behaviour (`validateUBFree`):
                       a frontend agreement (Core to Core), not a compiler-origin result
  cross-validated-ub   validated both ways, but some direction rests on source undefined behaviour:
                       counted separately, never as a cross-validation of defined behaviour
  cross-validated-blocked validated both ways, but a route accepted a construct it drops (an asm
                       label, an attribute it does not show it keeps): that route's Core does not
                       correspond to the source, so the agreement is not counted
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
  native               gcc -O0 run of execute/ cases under caps (NATIVE: wall and CPU time, address
                       space, file size, stdout bytes): how it ended (exit/signal/timeout/
                       stdout-limit), the code, and the stdout's size and SHA-256 (never parsed);
                       sanity only, not validation
  sourceVerified       the SHA-256 of the bytes actually run equals the manifest's (checked per case)
  compileOnly          a compile/ case: the test is about compiling; whole-program behaviour is incidental
  targetConditional    the source selects code with #if on a target macro (for example ia64 or HP-UX):
                       on x86-64 the test may preprocess to something trivial

Every verdict is compiled evidence (`ctv-pipeline`), not a kernel theorem. Execution comparisons
are sanity checks. The report records the tool versions and the manifest's SHA-256.
"""
import argparse, concurrent.futures as cf, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MANIFEST = os.path.join(ROOT, "benchmarks", "gcc-torture", "manifest.json")
RUNTIME = os.path.join(ROOT, "benchmarks", "cerberus-elaboration", "oracle", "constant-return", "core.sexp.gz")
TARGET = "x86_64-linux-gnu"


# Caps of a tool run (gcc, clang, cerb-lean, cfront, ctv-pipeline): output is buffered up to these
# sizes; beyond them the run stops and is reported as "output-limit".
TOOL_STDOUT_BYTES, TOOL_STDERR_BYTES = 512 << 20, 4 << 20


def run(cmd, cwd, timeout):
    """A tool run under `launch` (wall-clock deadline over the whole lifecycle, the process group
    killed at the end, outputs capped). Returns (returncode | "timeout" | "output-limit", stdout, stderr)."""
    res, out, err = launch(cmd, cwd, timeout, TOOL_STDOUT_BYTES, TOOL_STDERR_BYTES, limits=None)
    if res["ended"] == "timeout":
        return "timeout", b"", b""
    if res["ended"] in ("stdout-limit", "stderr-limit"):
        return "output-limit", b"", b""
    if res["ended"] == "launch-failed":
        return "launch-failed", b"", res["launchError"].encode()
    return (res["code"] if res["ended"] == "exit" else -res["code"]), out, err


# Caps of a native test run (torture programs may loop, allocate or print without bound).
NATIVE = {"timeoutSeconds": 10, "cpuSeconds": 10, "addressSpaceBytes": 1 << 30, "fileSizeBytes": 16 << 20,
          "stdoutBytes": 1 << 20, "stderrBytes": 64 << 10}

# The resource limits are applied by an exec wrapper, not by `preexec_fn` (which is unsafe from the
# runner's worker threads): a fresh interpreter sets them and replaces itself with the program.
# The interpreter ignores SIGPIPE and SIGXFSZ, and an exec keeps ignored signals ignored, so the
# wrapper restores their default actions first. The CPU limit's hard value is one second above the
# soft one, so that the soft limit's SIGXCPU arrives first.
_LIMIT_WRAPPER = (
    "import os, resource, signal, sys\n"
    "fd = int(sys.argv[1])\n"
    "os.set_inheritable(fd, False)\n"
    "try:\n"
    "    for s in (signal.SIGPIPE, signal.SIGXFSZ, signal.SIGXCPU):\n"
    "        signal.signal(s, signal.SIG_DFL)\n"
    "    cpu, asz, fsz = (int(x) for x in sys.argv[2:5])\n"
    "    resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 1))\n"
    "    for r, v in ((resource.RLIMIT_AS, asz), (resource.RLIMIT_FSIZE, fsz), (resource.RLIMIT_CORE, 0)):\n"
    "        resource.setrlimit(r, (v, v))\n"
    "    os.execv(sys.argv[5], sys.argv[5:])\n"
    "except BaseException as e:\n"
    "    os.write(fd, repr(e).encode()[:1000])\n"
    "    os._exit(127)\n")
# The wrapper reports a failure before the program starts (a limit it cannot set, an executable it
# cannot run) on a close-on-exec status pipe, which a successful exec closes empty: such a run is
# "launch-failed", never the program's own exit status.


def exited(pid):
    """Whether the process has ended, without reaping it (its pid stays reserved)."""
    info = os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
    return info is not None and info.si_pid == pid


def launch(cmd, cwd, timeout, out_cap, err_cap, limits=None):
    """Run `cmd` in a new session and process group (`start_new_session`, no `preexec_fn`), with
    stdin from /dev/null, reading stdout and stderr with `select` up to `out_cap`/`err_cap` bytes,
    under one wall-clock deadline covering the whole lifecycle (output, end of file, and the wait for
    the process). On a deadline or a cap the whole group is killed; after a normal end the group is
    killed too, so no child of the program outlives it (a descendant that starts its own session
    escapes; nothing here detects it). `limits` = (cpu seconds, address-space bytes, file-size bytes)
    are applied by the exec wrapper.

    Returns ({"ended": "exit" | "signal" | "cpu-limit" | "fsize-limit" | "timeout" | "stdout-limit"
              | "stderr-limit" | "launch-failed" (the program never started: "launchError"), "code" (exit status, or the signal number, also for a limit),
              "cpuSeconds", "groupKilledAfterEnd" (the group was signalled after the leader ended;
              this does not count live descendants), "groupGone" (no member left after the kill)}, stdout, stderr).
    A limit is recognised by its signal: SIGXCPU (or SIGKILL with the CPU time at the limit) is
    "cpu-limit", SIGXFSZ is "fsize-limit"; the signal stays in "code" as the evidence."""
    import select, signal
    status_r, status_w = os.pipe()
    argv = ([sys.executable, "-I", "-c", _LIMIT_WRAPPER, str(status_w), *(str(x) for x in limits), *cmd]
            if limits else cmd)
    try:
        p = subprocess.Popen(argv, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, start_new_session=True, pass_fds=(status_w,) if limits else ())
    except OSError as e:
        os.close(status_r); os.close(status_w)
        return ({"ended": "launch-failed", "code": None, "launchError": repr(e)[:1000], "cpuSeconds": 0.0,
                 "groupKilledAfterEnd": False, "groupGone": True}, b"", b"")
    os.close(status_w)
    deadline = time.monotonic() + timeout
    fo, fe = p.stdout.fileno(), p.stderr.fileno()
    bufs = {fo: bytearray(), fe: bytearray()}
    caps = {fo: (out_cap, "stdout-limit"), fe: (err_cap, "stderr-limit")}
    open_fds, ended, ended_seen = set(bufs), None, False
    while open_fds and ended is None:
        left = deadline - time.monotonic()
        if left <= 0:
            ended = "timeout"; break
        ready, _, _ = select.select(list(open_fds), [], [], min(left, 0.1))
        for fd in ready:
            chunk = os.read(fd, 65536)
            if not chunk:
                open_fds.discard(fd); continue
            bufs[fd] += chunk
            if len(bufs[fd]) > caps[fd][0]:
                ended = caps[fd][1]; break
        if not ready and not ended_seen:
            # The program may have ended while a descendant keeps its outputs open: once it has
            # ended, drain what is already in the pipes (it may have written just before ending)
            # and stop reading. It is not reaped yet (WNOWAIT), so its pid, which is the group's id,
            # cannot be reused before the group is killed below.
            if exited(p.pid):
                ended_seen = True
                while open_fds and ended is None:
                    ready, _, _ = select.select(list(open_fds), [], [], 0)
                    if not ready:
                        break
                    for fd in ready:
                        chunk = os.read(fd, 65536)
                        if not chunk:
                            open_fds.discard(fd); continue
                        bufs[fd] += chunk
                        if len(bufs[fd]) > caps[fd][0]:
                            ended = caps[fd][1]; break
                break
    # The process itself (its outputs closed or not) must also end before the deadline.
    while ended is None and not ended_seen:
        if exited(p.pid):
            ended_seen = True; break
        if time.monotonic() >= deadline:
            ended = "timeout"; break
        time.sleep(0.02)
    # Kill the group before reaping its leader, so that its id cannot have been reused.
    killed_after_end = False
    try:
        os.killpg(p.pid, signal.SIGKILL)
        killed_after_end = ended_seen
    except (ProcessLookupError, PermissionError):
        pass
    _, status, usage = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    p.stdout.close(); p.stderr.close()
    # Wait (briefly) until the killed group is gone, so that nothing of the run outlives it.
    group_gone = False
    for _ in range(100):
        try:
            os.killpg(p.pid, 0)
        except ProcessLookupError:
            group_gone = True; break
        time.sleep(0.02)
    cpu = round(usage.ru_utime + usage.ru_stime, 3)
    code = None
    if ended is None:
        # killed_after_end: the group was signalled after the leader had ended, so the leader's
        # own status is its own ending, not our kill.
        if os.WIFSIGNALED(status):
            sig = os.WTERMSIG(status)
            code = sig
            # A limit shows as a signal: SIGXCPU at the soft CPU limit, SIGKILL at the hard one (equal
            # here), SIGXFSZ at the file-size limit. They are reported as the limit, with the signal.
            if limits and (sig == signal.SIGXCPU or (sig == signal.SIGKILL and cpu >= limits[0])):
                ended = "cpu-limit"
            elif limits and sig == signal.SIGXFSZ:
                ended = "fsize-limit"
            else:
                ended = "signal"
        else:
            ended, code = "exit", os.WEXITSTATUS(status)
    launch_error = b""
    while True:
        chunk = os.read(status_r, 4096)
        if not chunk:
            break
        launch_error += chunk
    os.close(status_r)
    extra = {}
    if launch_error:
        ended, code, extra = "launch-failed", None, {"launchError": launch_error.decode(errors="replace")[:1000]}
    return ({"ended": ended, "code": code, "cpuSeconds": cpu, "groupKilledAfterEnd": killed_after_end,
             "groupGone": group_gone, **extra},
            bytes(bufs[fo]), bytes(bufs[fe]))


def run_native(exe, cwd):
    """Run a test binary under NATIVE's caps (`launch`). Returns how it ended, by size and SHA-256 of
    what it printed (stdout is never parsed), and the stdout itself (capped):
    ({"ended", "code", "cpuSeconds", "groupKilledAfterEnd", "stdoutBytes", "stdoutSha256"}, stdout).
    An address-space limit has no signal of its own: a program whose allocation fails does whatever
    it does then, and is reported by that ending."""
    res, out, _ = launch([exe], cwd, NATIVE["timeoutSeconds"], NATIVE["stdoutBytes"], NATIVE["stderrBytes"],
                         limits=(NATIVE["cpuSeconds"], NATIVE["addressSpaceBytes"], NATIVE["fileSizeBytes"]))
    out = out[:NATIVE["stdoutBytes"]]
    res.update(stdoutBytes=len(out), stdoutSha256=hashlib.sha256(out).hexdigest())
    return res, out


def failure(rc, so, se):
    """Why a tool run failed: its timeout or output cap, or its reject message."""
    if rc == "timeout":
        return f"timeout ({OPTIONS['toolTimeoutSeconds']} s)"
    if rc == "launch-failed":
        return "the tool could not be started: " + se.decode(errors="replace")[:300]
    if rc == "output-limit":
        return f"output beyond the tool output cap ({TOOL_STDOUT_BYTES >> 20} MiB stdout, {TOOL_STDERR_BYTES >> 20} MiB stderr)"
    return reason(so + se)


def reason(out):
    t = out.decode(errors="replace")
    m = re.search(r'\(\$str "([^"]*)"\)\)?\s*$', t.strip().splitlines()[0] if t.strip() else "")
    return (m.group(1) if m else t.strip()[-300:])[:300]


# Everything the statuses depend on, pinned in the report.
OPTIONS = {
    "preprocess": ["gcc", "-E", "-P", "-std=gnu11", "-w"],
    "cerberusRoute": ["cerb-lean", "parse", "--level", "tail"],
    "clangAst": ["clang", "-x", "c", "-std=gnu11", "-target", "x86_64-linux-gnu", "-w", "-Xclang", "-ast-dump=json", "-fsyntax-only"],
    "clangRoute": ["cfront", "ail"],
    "pipeline": {"tool": "ctv-pipeline run", "depth": 200000, "budget": 2000000, "profile": "linuxX86_64",
                 "elaborator": "TargetCoherence.linuxLP64", "runtime": "benchmarks/cerberus-elaboration/oracle/constant-return/core.sexp.gz"},
    "native": ["gcc", "-O0", "-std=gnu11", "-w", "-lm"],
    "toolTimeoutSeconds": 60,
    "target": "x86_64-linux-gnu",
}


def max_symbol(texts):
    best = 0
    for t in texts:
        for m in re.finditer(r'\(Symbol \(\$str "[0-9a-f]*"\) (\d+)', t):
            best = max(best, int(m.group(1)))
    return best + 1


def head(case, root, sums):
    """A row's facts about the source itself: the SHA-256 of the bytes actually run, checked against
    the manifest during the run, and the compileOnly / targetConditional flags."""
    row = {"case": case}
    data = open(os.path.join(root, case), "rb").read()
    row["sha256"] = hashlib.sha256(data).hexdigest()
    row["sourceVerified"] = row["sha256"] == sums[case]
    text = data.decode(errors="replace")
    if case.startswith("compile/"):
        row["compileOnly"] = True
    if re.search(r"^\s*#\s*(if|ifdef|ifndef|elif)\b.*\b__(ia64|hppa|hpux|i386|x86_64|aarch64|arm|mips|powerpc|sparc|s390|riscv|alpha|sh|vax|m68k|avr|msp430)\w*__", text, re.M):
        row["targetConditional"] = True
    return row


def one(case, root, binary, sums, timeouts):
    row = head(case, root, sums)
    src = os.path.join(root, case)
    if not row["sourceVerified"]:
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
            why["cerberus"] = failure(rc, so, se)
        rc, so, se = run(["clang", "-x", "c", "-std=gnu11", "-target", TARGET, "-w", "-Xclang", "-ast-dump=json", "-fsyntax-only", "t.i"], tmp, timeouts)
        if rc == 0:
            open(os.path.join(tmp, "ast.json"), "wb").write(so)
            rc, so, se = run([os.path.join(binary, "cfront"), "ail", "ast.json"], tmp, timeouts)
            if rc == 0:
                open(os.path.join(tmp, "clang.tail.sexp"), "wb").write(so); routes.append("clang")
            else:
                why["clang"] = failure(rc, so, se)
        else:
            why["clang"] = "clang: " + (failure(rc, so, se) if isinstance(rc, str) else se.decode(errors="replace").strip().splitlines()[0][:300] if se.strip() else str(rc))
        row["routes"] = why
        if not routes:
            row["status"] = "frontend-rejected"; return row
        # A route that accepted a construct it drops no longer corresponds to the source
        # (scripts/c-tv/corpus.py: blocking losses). Such a route's agreement never counts.
        pre = open(os.path.join(tmp, "t.i"), errors="replace").read()
        blocked = []
        if "cerberus" in routes and re.search(r"\b(__asm__|__asm|asm)\s*(volatile|__volatile__)?\s*\(", pre):
            blocked.append("cerberus: asm label or register dropped")
        attrs = {a.strip("_") for a in re.findall(r"__attribute__\s*\(\(\s*([A-Za-z_][A-Za-z0-9_]*)", pre)}
        if "cerberus" in routes and attrs:
            blocked.append("cerberus: attributes accepted without evidence they are kept")
        if "clang" in routes and attrs - {"used", "unused", "deprecated", "noinline", "always_inline", "aligned", "mode"}:
            blocked.append("clang: attributes accepted without evidence they are kept")
        if blocked:
            row["blocked"] = blocked
        observes = []
        if case.startswith("execute/"):
            open(os.path.join(tmp, "empty.out"), "wb").close()
            observes += ["--observe", "pass", "0", "empty.out"]
            rc, _, _ = run(["gcc", "-O0", "-std=gnu11", "-w", "t.c", "-o", "t.exe", "-lm"], tmp, 60)
            if rc == 0:
                row["native"], _ = run_native(os.path.join(tmp, "t.exe"), tmp)
            else:
                row["native"] = {"ended": "build-failed", "code": None}
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
            ubfree = [p["validatedUBFree"] for p in rep["pairs"]]
            if row.get("blocked") and len(el) == 2 and verdicts and all(v == "validated" for v in verdicts):
                row["status"] = "cross-validated-blocked"
            elif len(el) == 2 and verdicts and all(v == "validated" for v in verdicts) and all(ubfree):
                row["status"] = "cross-validated"
            elif len(el) == 2 and verdicts and all(v == "validated" for v in verdicts):
                row["status"] = "cross-validated-ub"
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
    OPTIONS["toolTimeoutSeconds"] = a.timeout
    OPTIONS["toolStdoutBytes"], OPTIONS["toolStderrBytes"] = TOOL_STDOUT_BYTES, TOOL_STDERR_BYTES
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
                rows[c] = {**head(c, a.root, sums), "status": "tool-error", "why": repr(e)[:300]}
            if i % 200 == 0:
                print(f"{i}/{len(chosen)} {time.time() - start:.0f}s", file=sys.stderr, flush=True)
    ordered = [rows[c] for c in cases]
    statuses = ["not-attempted", "harness-needed", "frontend-rejected", "elaborator-rejected", "no-main", "gap", "unknown",
                "explored", "cross-validated", "cross-validated-ub", "cross-validated-blocked", "refuted", "timeout", "tool-error"]
    summary = {s: sum(1 for r in ordered if r["status"] == s) for s in statuses}
    assert sum(summary.values()) == len(cases)
    for part in ["compile/", "execute/"]:
        summary[part] = {s: sum(1 for r in ordered if r["status"] == s and r["case"].startswith(part)) for s in statuses}
    summary["blocked"] = sum(1 for r in ordered if r.get("blocked"))
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
           "options": OPTIONS, "native": NATIVE,
           "evidence": "compiled", "seconds": round(time.time() - start), "summary": summary, "cases": ordered}
    with open(a.out, "w") as f:
        json.dump(rep, f, indent=None, separators=(",", ":"), sort_keys=True)
        f.write("\n")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
