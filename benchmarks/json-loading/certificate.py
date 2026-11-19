#!/usr/bin/env python3
"""Measure a byte-exact, benchmark-only object certificate."""

import argparse
import csv
import os
from pathlib import Path
import subprocess
import time

from run import LIMITS, ROOT, fixtures


HERE = Path(__file__).resolve().parent
LAST = {"small": 6, "medium": 540, "wide": 42000}
SEMANTICS = (r'{"\u03BB":"\uD834\uDD1E","precise":9007199254740993,'
             '"λ":false,"decimal":-1.2300e+26,"nested":[{"ok":true}]}\n')
SEMANTIC_CHECKS = """
example : (result.member? "λ" >>= Value.string?) = some "𝄞" := rfl
example : (result.entries?.bind (·.get? 2) >>= fun entry => entry.2.bool?) = some false := rfl
example : (result.member? "precise" >>= Value.number?) = some ⟨false, 9007199254740993, 0⟩ := rfl
example : (result.member? "decimal" >>= Value.number?) = some ⟨true, 12300, 22⟩ := rfl
example : (result.at? [.key "nested", .index 0, .key "ok"] >>= Value.bool?) = some true := rfl
example : block.entries.WellSized := valid.sized.2
"""


def split_body(source, width):
    if not (source.startswith(b"{") and source.endswith(b"}\n")):
        raise ValueError("certificate profile requires an object with final LF")
    body = source[1:-2]
    start = count = depth = 0
    quoted = escaped = False
    for offset, byte in enumerate(body):
        if quoted:
            if escaped:
                escaped = False
            elif byte == ord("\\"):
                escaped = True
            elif byte == ord('"'):
                quoted = False
        elif byte == ord('"'):
            quoted = True
        elif byte in b"[{":
            depth += 1
        elif byte in b"]}":
            depth -= 1
        elif byte == ord(",") and depth == 0:
            count += 1
            if count % width == 0:
                yield body[start:offset]
                start = offset + 1
    yield body[start:]


def tree(head, names):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    return f"({head} {tree(head, names[:mid])} {tree(head, names[mid:])})"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--case", default="medium", choices=(*LAST, "semantics"))
    parser.add_argument("--width", type=int, default=4, choices=range(1, 33), metavar="1..32")
    parser.add_argument("--seconds", type=int, default=60)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "Certificate.lean").write_bytes((HERE / "Certificate.lean").read_bytes())
    subprocess.run(["lake", "build", "--wfail", "Silmaril.Formats.Json.Fast.Elab",
                    "Silmaril.Prelude.Bytes.Elab.Defs"], cwd=ROOT, check=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(output) + ":" + subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    lean = ["lean", "-j1", "-M", "4096", "-s", "32768", "-DautoImplicit=false", "-E", "warning"]
    if args.case == "semantics":
        fixture = output / "semantics.json"
        fixture.write_bytes(SEMANTICS.encode("utf-8"))
        args.width = 1
    else:
        fixture = next(path for name, path, _ in fixtures(output) if name == args.case)
    source = fixture.read_bytes()
    parts = output / "parts"
    parts.mkdir(exist_ok=True)

    with (output / "certificate.csv").open("w", newline="", encoding="utf-8") as stream:
        rows = csv.writer(stream)
        rows.writerow(["case", "bytes", "width", "phase", "exit", "wall_s", "rss_kib", "olean_bytes"])

        def record(phase, code, wall, rss="", size=""):
            row = [args.case, len(source), args.width, phase, code, wall, rss, size]
            rows.writerow(row)
            stream.flush()
            print(*row, flush=True)

        def run(phase, *command, artifact=None):
            timing = output / f"{phase}.time"
            if artifact:
                artifact.unlink(missing_ok=True)
            with (output / f"{phase}.log").open("w", encoding="utf-8") as log:
                proc = subprocess.run(["/usr/bin/time", "-f", "%e %M", "-o", str(timing),
                                       "timeout", "--kill-after=2", str(args.seconds), *command],
                                      cwd=output, env=env, stdout=log, stderr=subprocess.STDOUT)
            wall, rss = timing.read_text().splitlines()[-1].split()
            record(phase, proc.returncode, wall, rss,
                   artifact.stat().st_size if artifact and proc.returncode == 0 else "")
            return proc.returncode == 0

        if not run("support", *lean, "-o", "Certificate.olean", "Certificate.lean",
                   artifact=output / "Certificate.olean"):
            return 1
        start = time.perf_counter()
        names = []
        for index, part in enumerate(split_body(source, args.width)):
            names.append(f"block{index}")
            (parts / f"block{index}.json").write_bytes(part)
        (output / "Blocks.lean").write_text(
            "module\npublic import Certificate\nopen JsonCertificate\n@[expose] public section\n" + LIMITS +
            "\n".join(f'certificate_leaf {name} from "parts/{name}.json"' for name in names) + "\n" +
            f"noncomputable def block : Block := {tree('Block.join', names)}\n" +
            f"theorem valid : block.Valid := {tree('Block.Valid.join', [f'{name}.valid' for name in names])}\n" +
            "noncomputable def result := block.value\n", encoding="utf-8")
        (output / "Certified.lean").write_text(
            "module\npublic import Blocks\nopen JsonCertificate\n@[expose] public section\n" + LIMITS +
            f'kbytes_def original from_file "{fixture.name}"\n' +
            "theorem agreement : Spells original result :=\n"
            "  spells_of_check original block valid original.wf_true (by decide +kernel)\n", encoding="utf-8")
        record("generate", 0, f"{time.perf_counter() - start:.3f}")
        for module, phase in (("Blocks", "fragments"), ("Certified", "link")):
            artifact = output / f"{module}.olean"
            if not run(phase, *lean, "-o", artifact.name, str(artifact.with_suffix(".lean")), artifact=artifact):
                return 1
        probe = output / "Probe.lean"
        header = "module\nimport Certified\nopen JsonCertificate Silmaril.Formats.Json.Fast\n" + LIMITS
        probe.write_text(header, encoding="utf-8")
        if not run("import", *lean, probe.name):
            return 1
        if args.case == "semantics":
            checks = SEMANTIC_CHECKS
        else:
            position = LAST[args.case]
            checks = ("example : Spells original result ∧\n"
                      f"    (result.entries?.bind (·.get? {position}) >>= fun entry => entry.2.bool?) = some true :=\n"
                      "  ⟨agreement, by rfl⟩\n")
        probe.write_text(header + checks + "#print axioms agreement\n", encoding="utf-8")
        if not run("query", *lean, probe.name):
            return 1
        if args.case == "semantics":
            (output / "tampered.json").write_bytes(source.replace(b"e+26", b"E+26"))
            reject = output / "Reject.lean"
            reject.write_text(header + 'kbytes_def altered from_file "tampered.json"\n'
                              "example : altered.sameBytes 4096 block.render = false := by decide +kernel\n",
                              encoding="utf-8")
            if not run("reject", *lean, str(reject)):
                return 1
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
