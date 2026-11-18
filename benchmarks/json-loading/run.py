#!/usr/bin/env python3
"""Generate fixtures and run separate Lean processes for each measured phase."""

import argparse
import csv
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HARNESS = Path(__file__).with_name("Harness.lean")
RUNTIME = HARNESS.with_name("Runtime.lean")
HEADER = "module\nimport {module}\nopen Silmaril.Formats\n"
LIMITS = "set_option maxRecDepth 8192\nset_option maxHeartbeats 0\n"


def dump(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def fixtures(output):
    def wide(count):
        return {
            **{f"artifact/common-prefix/v1/entry/{i:06d}": f"receipt-{i:06d}-λ-🧪" for i in range(count)},
            "artifact/common-prefix/v1/entry/last": True,
        }, ["artifact/common-prefix/v1/entry/last"]

    def flat(count):
        return [f"package-{i:06d}/" + "0123456789abcdef" * 4 for i in range(count)] + [True], [count]

    def nested(count):
        result = [
            {"path": f"src/component/{i:06d}.wasm", "size": i, "flags": [False, True], "unicode": "é𝄞"}
            for i in range(count)
        ]
        path = [count - 1, "flags", 1]
        for layer in reversed(range(32)):
            result = {"meta": {"layer": layer}, "payload": result}
            path.insert(0, "payload")
        return result, path

    for name, (value, path) in {
        "small": wide(6), "medium": wide(540), "wide": wide(42000),
        "list": flat(40000), "nested": nested(33000),
    }.items():
        file = output / f"{name}.json"
        file.write_text(dump(value) + "\n", encoding="utf-8")
        yield name, file, path
    for name, relative in {
        "oci": "examples/containers/noop-oci/layout/manifest.json",
        "litmus": "tools/litmus-x86/export/c11-meta.json",
        "litmus-corpus": "tools/litmus-x86/export/corpus.json",
    }.items():
        yield name, ROOT / relative, None


def build_native():
    with tempfile.NamedTemporaryFile(mode="w", prefix=".json-loading-", suffix=".toml", dir=ROOT) as config:
        config.write((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
        config.write('\n[[lean_exe]]\nname = "json-loading-bench"\nroot = "Runtime"\n'
                     'srcDir = "benchmarks/json-loading"\n')
        config.flush()
        subprocess.run(["lake", "-f", config.name, "build", "--wfail", "json-loading-bench"],
                       cwd=ROOT, check=True)
    return ROOT / ".lake/build/bin/json-loading-bench"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--case", action="append", help="restrict to named fixtures (repeatable)")
    parser.add_argument("--runs", type=int, default=1)
    parser.add_argument("--seconds", type=int, default=20)
    parser.add_argument("--memory", type=int, default=4096, help="Lean memory limit in MiB")
    parser.add_argument("--native-only", action="store_true", help="benchmark all parsers in one native executable")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    lean = ["lean", "-j1", "-M", str(args.memory), "-s", "32768", "-E", "warning"]
    if args.native_only:
        runtime = [str(build_native())]
    else:
        subprocess.run(["lake", "build", "--wfail", "Silmaril.Formats.Json.Fast.Elab"], cwd=ROOT, check=True)
        env["LEAN_PATH"] = str(output) + ":" + subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True
        ).strip()
        (output / HARNESS.name).write_bytes(HARNESS.read_bytes())
        (output / RUNTIME.name).write_bytes(RUNTIME.read_bytes())
        subprocess.run(lean + ["-o", "Harness.olean", HARNESS.name], cwd=output, env=env, check=True)
        runtime = [*lean, "--run", RUNTIME.name]

    with (output / "results.csv").open("w", newline="") as csv_file:
        rows = csv.writer(csv_file)
        rows.writerow(["case", "bytes", "run", "phase", "variant", "status", "wall_s", "max_rss_kib", "olean_bytes", "parse_ms"])

        def run(case, size, repeat, phase, variant, arguments, artifact=None, command=lean):
            log = output / f"{case}.{repeat}.{phase}.{variant}.log"
            timing = log.with_suffix(".time")
            with log.open("w") as stream:
                proc = subprocess.run([
                    "/usr/bin/time", "-o", str(timing), "-f", "%e %M",
                    "timeout", "--kill-after=2", str(args.seconds), *command, *arguments,
                ], cwd=output, env=env, stdout=stream, stderr=subprocess.STDOUT, check=False)
            elapsed, rss = timing.read_text().splitlines()[-1].split()
            parse_time = re.search(r"parse_ns=(\d+)", log.read_text(errors="replace"))
            rows.writerow([case, size, repeat, phase, variant, proc.returncode, elapsed, rss,
                           artifact.stat().st_size if artifact and proc.returncode == 0 else "",
                           f"{int(parse_time[1]) / 1e6:.3f}" if parse_time else ""])
            csv_file.flush()
            print(case, repeat, phase, variant, proc.returncode, elapsed, rss, flush=True)
            return proc.returncode == 0

        for case, fixture, path in fixtures(output):
            if args.case and case not in args.case:
                continue
            size = fixture.stat().st_size
            for repeat in range(1, args.runs + 1):
                for variant in ("wire", "lean", "fast"):
                    run(case, size, repeat, "native" if args.native_only else "runtime", variant,
                        [variant, str(fixture)], command=runtime)
                if args.native_only or path is None:
                    continue
                steps = "[" + ", ".join(f".key {dump(s)}" if isinstance(s, str) else f".index {s}" for s in path) + "]"
                for variant, statement, goals in (
                    ("Wire", f'noncomputable def result := JsonWire.parse? ⟨(include_str "{fixture.name}").toUTF8⟩',
                     {"wire": f"wireSelect result {steps}"}),
                    ("Source", f'set_option silmaril.json.precompute false in\njson_file result from "{fixture.name}"',
                     {"source": f"fastSelect true result {steps}"}),
                    ("Prepared", f'json_file result from "{fixture.name}"',
                     {"indexed": f"fastSelect true result {steps}", "linear": f"fastSelect false result {steps}"}),
                ):
                    source = output / f"{variant}.lean"
                    artifact = source.with_suffix(".olean")
                    artifact.unlink(missing_ok=True)
                    source.write_text("module\npublic import Harness\nopen Silmaril.Formats\n@[expose] public section\n"
                                      "set_option profiler true\nset_option profiler.threshold 0\n"
                                      + statement + "\n", encoding="utf-8")
                    if not run(case, size, repeat, "declare", variant, ["-o", artifact.name, str(source)], artifact):
                        continue
                    probe = output / "Probe.lean"
                    header = HEADER.format(module=variant)
                    probe.write_text(header, encoding="utf-8")
                    run(case, size, repeat, "import", variant, [probe.name])
                    for label, goal in goals.items():
                        probe.write_text(header + LIMITS + f"example : {goal} = some true := by json_decide\n", encoding="utf-8")
                        run(case, size, repeat, "query", label, [probe.name])
                    if variant == "Prepared" and case in ("small", "medium"):
                        probe.write_text(header + LIMITS +
                            f'json_text source from "{fixture.name}"\n'
                            "example : Json.Fast.SourceMatches source.toUTF8 result := by json_source\n",
                            encoding="utf-8")
                        run(case, size, repeat, "agreement", variant, [probe.name])


if __name__ == "__main__":
    main()
