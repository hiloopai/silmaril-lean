#!/usr/bin/env python3
"""Measure unchanged IO replay drivers; never a CI-budget or proof verdict.

Runs the original interpreted commands, builds optional native targets, runs the
native executables explicitly (twice), and compares complete stdout/stderr bytes.
The drivers retain all original assertions/negative cases. Their one-line PASS
output is an output digest, not a digest of every intermediate observation.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

DRIVERS = {
    "core": ("tests/cerberus/CjsonArrayItemContext.lean", "ci_corpus_cjson_array_item_core", 168),
    "machine": ("tests/cerberus/CjsonArrayItemMachine.lean", "ci_corpus_cjson_array_item_machine", 420),
}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--lake", default="lake")
    ap.add_argument("--audit", action="store_true", help="also compare separately instrumented per-case observation transcripts")
    ap.add_argument("--full-initialization", action="store_true", help="experimental external runtime bootstrap for the unchanged meta drivers")
    ap.add_argument("--cpus", type=int, default=8)
    ap.add_argument("--address-space-gib", type=int, default=32)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    allowed = sorted(os.sched_getaffinity(0))[:args.cpus]
    if len(allowed) != args.cpus:
        raise SystemExit("not enough available CPUs for requested affinity")
    def limits():
        os.sched_setaffinity(0, allowed)
        cap = args.address_space_gib * 1024**3
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    env = dict(os.environ, LEAN_NUM_THREADS=str(args.cpus))
    summary = {"native_full_initialization": args.full_initialization, "cpu_affinity": allowed, "address_space_gib": args.address_space_gib,
               "memory_limit_kind": "per-child RLIMIT_AS, not a physical/cgroup memory limit",
               "host_cpu_count": os.cpu_count(),
               "host_meminfo": Path("/proc/meminfo").read_text().splitlines()[:3],
               "cache": "published dependencies/builds may already be warm; no cache flush",
               "drivers": {k: {"path": p, "sha256": digest(Path(p)), "declared_cases": n}
                           for k, (p, _, n) in DRIVERS.items()}, "steps": []}
    def save():
        (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    def run(name, command):
        stdout, stderr = args.out / (name+".stdout"), args.out / (name+".stderr")
        start = time.monotonic()
        with stdout.open("wb") as out, stderr.open("wb") as err:
            p = subprocess.Popen(command, stdout=out, stderr=err, env=env, preexec_fn=limits)
            _, status, usage = os.wait4(p.pid, 0)
            p.returncode = os.waitstatus_to_exitcode(status)
        row = {"name": name, "argv": command, "wall_seconds": time.monotonic()-start,
               "exit": p.returncode, "stdout_sha256": digest(stdout),
               "stderr_sha256": digest(stderr), "stdout_bytes": stdout.stat().st_size,
               "stderr_bytes": stderr.stat().st_size, "resource": {
                   "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
                   "max_rss_kib": usage.ru_maxrss, "major_faults": usage.ru_majflt,
                   "minor_faults": usage.ru_minflt, "voluntary_switches": usage.ru_nvcsw,
                   "involuntary_switches": usage.ru_nivcsw,
                   "method": "Linux wait4 rusage; max RSS is not aggregate concurrent process-tree RSS"}}
        summary["steps"].append(row); save()
        print(json.dumps(row), flush=True)
        if p.returncode:
            raise SystemExit(f"{name} failed; retained output and partial measurements")
        return row
    def bootstrap(audit=False):
        directory=args.out/("audit-full-init" if audit else "full-init")
        run("audit-bootstrap-plan" if audit else "bootstrap-plan", [sys.executable,
            "tools/corpus/replay_native_bootstrap.py", "--out",str(directory),"--lake",args.lake,
            *(["--audit"] if audit else [])])
        plan=json.loads((directory/"plan.json").read_text())
        for step in plan["steps"]: run(step["name"],step["argv"])
        return {k.removeprefix("audit-"):v["executable"] for k,v in plan["targets"].items()}
    save()
    for kind,(source,_,_) in DRIVERS.items():
        run(kind+"-interpreted", [args.lake,"env","lean","-DwarningAsError=true","--run",source])
    # Build cost is timed separately and included in net-cost comparisons.
    run("native-build", [args.lake,"build","--wfail",*[v[1] for v in DRIVERS.values()]])
    native_paths=bootstrap() if args.full_initialization else {
        kind:str(Path(".lake/build/bin")/v[1]) for kind,v in DRIVERS.items()}
    for repeat in (1,2):
        for kind,(_,target,n) in DRIVERS.items():
            row = run(f"{kind}-native-{repeat}", [native_paths[kind]])
            for stream in ("stdout","stderr"):
                expected=(args.out/(kind+"-interpreted."+stream)).read_bytes()
                actual=(args.out/(f"{kind}-native-{repeat}."+stream)).read_bytes()
                if actual != expected:
                    raise SystemExit(f"{kind}: complete {stream} differs in native run{repeat}")
            if not (args.out/(f"{kind}-native-{repeat}.stdout")).read_text().startswith(f"PASS{n} "):
                raise SystemExit(f"{kind}: original observation-count summary missing")
    run("native-noop-build", [args.lake,"build","--wfail",*[v[1] for v in DRIVERS.values()]])
    if args.audit:
        from replay_observation_audit import generate
        generate()
        audit_targets = ["ci_corpus_replay_audit_core", "ci_corpus_replay_audit_machine"]
        run("audit-build", [args.lake,"build","--wfail",*audit_targets])
        audit_paths=bootstrap(audit=True) if args.full_initialization else {
            kind:str(Path(".lake/build/bin")/target) for kind,target in zip(DRIVERS,audit_targets)}
        for kind,target in zip(DRIVERS, audit_targets):
            source = f"build/corpus-replay-audit/ReplayAudit{kind.title()}.lean"
            run(kind+"-audit-interpreted", [args.lake,"env","lean","-DwarningAsError=true","--run",source])
            run(kind+"-audit-native", [audit_paths[kind]])
            a = args.out/(kind+"-audit-interpreted.stdout")
            b = args.out/(kind+"-audit-native.stdout")
            if (args.out/(kind+"-audit-interpreted.stderr")).read_bytes() != (args.out/(kind+"-audit-native.stderr")).read_bytes():
                raise SystemExit(f"{kind}: audit stderr differs")
            if a.read_bytes() != b.read_bytes():
                raise SystemExit(f"{kind}: per-case observation transcripts differ")
            lines = a.read_text().splitlines()
            cases = sum(l.startswith("OBS "+kind+"|") for l in lines)
            negative_entries = sum(l.startswith("NEG ") for l in lines)
            if negative_entries != (3 if kind == "core" else 0):
                raise SystemExit(f"{kind}: incomplete negative transcript")
            forged_pairs=sum(l.endswith("|forgeries=none:none") for l in lines)
            if kind == "core" and forged_pairs != cases:
                raise SystemExit("core: incomplete or non-rejected forged-provenance observations")
            if cases != DRIVERS[kind][2]:
                raise SystemExit(f"{kind}: incomplete observation transcript")
            summary["drivers"][kind]["observations"] = {
                "cases": cases, "negative_entries": sum(l.startswith("NEG ") for l in lines),
                "forged_projection_values": 2*forged_pairs,
                "transcript_bytes": a.stat().st_size, "sha256": digest(a),
                "interpretation": "all fields checked by the unchanged driver, not arbitrary continuation or full-record semantic adequacy"}
            save()
    summary["output_match"] = True
    summary["proof_claim"] = False
    save()
    print("PASS unchanged replay runtime outputs/count summaries match; not full-state digests, semantic proof or CI-budget acceptance", flush=True)
if __name__ == "__main__":
    main()
