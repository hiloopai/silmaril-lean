#!/usr/bin/env python3
"""Offline wrapper for recovered sha256sum-min inputs; not the historical recipe.

The unchanged scripts/build.sh records the original build. This wrapper uses
its literal flags with frozen local inputs instead of reading mutable origin/main.
It never regenerates the host-dependent GNU text/strerror tables.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
MANIFEST_SHA256 = "6a359d31443d28321ce4af6eca4460bea881c66beb88cf1bac9082c87eaa8e86"
CHECKER_SHA256 = "1da13674ceca27bd63b2e0e709d60f37b341e32ce35a0b82da0e7bb211ccd0da"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify():
    path = HERE / "historical-manifest.json"
    if digest(path) != MANIFEST_SHA256:
        raise ValueError("historical manifest identity changed")
    manifest = json.loads(path.read_text())
    records = [manifest["build"]["script"], *manifest["build"]["generators"],
               *manifest["build"]["sources"]]
    for record in records:
        path = HERE / record["path"]
        if path.stat().st_size != record["bytes"] or digest(path) != record["sha256"]:
            raise ValueError("historical input changed: " + record["path"])
    for historical, retained in [
            ("tests/x86/sha256_compress_clang_O2.hex", "src/sha256_compress_clang_O2.hex"),
            ("xcompile/wrappers/xc_sha256.c", "inputs/xc_sha256.c")]:
        if digest(HERE / retained) != manifest["silmaril"]["inputs"][historical]:
            raise ValueError("retained Silmaril input changed: " + retained)
    if digest(HERE / "scripts/check_pilot_bytes.py") != CHECKER_SHA256:
        raise ValueError("recovered byte checker identity changed")
    return manifest


def flags(name):
    recipe = (HERE / "scripts/build.sh").read_text()
    match = re.search(r"^" + name + r"=\((.*?)\)$", recipe, re.M | re.S)
    if match is None:
        raise ValueError("missing literal flag array: " + name)
    return shlex.split(match.group(1))


def build(args, manifest):
    if args.out.exists():
        raise ValueError("output directory must be fresh")
    cc = shutil.which(args.cc)
    if cc is None:
        raise ValueError("actual GCC 13.3.0 is required")
    cc = str(Path(cc).resolve())
    env = dict(os.environ, LC_ALL="C", SOURCE_DATE_EPOCH="0")
    log = []

    def run(command, cwd=HERE):
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                capture_output=True, timeout=60)
        log.append({"argv": command, "returncode": result.returncode,
                    "stdout": result.stdout, "stderr": result.stderr})
        if result.returncode:
            raise ValueError("build command failed: " + repr(command) + "\n" + result.stderr)
        return result.stdout.strip()

    version = run([cc, "--version"])
    if "clang" in version.lower() or run([cc, "-dumpfullversion"]) != "13.3.0":
        raise ValueError("historical build requires actual GCC 13.3.0")
    if "x86_64" not in run([cc, "-dumpmachine"]):
        raise ValueError("historical build requires an x86_64 compiler target")
    components = {}
    for name in ["cc1", "as", "ld"]:
        path = run([cc, "-print-prog-name=" + name])
        path = shutil.which(path)
        if path is None:
            raise ValueError("missing compiler component: " + name)
        path = str(Path(path).resolve())
        components[name] = {"path": path, "sha256": digest(path)}
    linker_version = run([components["ld"]["path"], "--version"])
    if "2.42" not in linker_version.splitlines()[0]:
        raise ValueError("historical build requires GNU binutils 2.42")
    started = time.perf_counter()
    args.out.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix="sha256sum-recovered-") as temporary:
        work = Path(temporary)
        shutil.copytree(HERE / "src", work / "src")
        generated = work / "compress_clang_O2.S"
        run([sys.executable, "-I", str(HERE / "scripts/gen_compress_S.py"),
             str(HERE / "src/sha256_compress_clang_O2.hex"), str(generated)], work)
        if generated.read_bytes() != (work / "src/compress_clang_O2.S").read_bytes():
            raise ValueError("regenerated compression assembly differs")
        wrapper = (HERE / "inputs/xc_sha256.c").read_text()
        marker = "void sha256_compress"
        position = wrapper.index(marker)
        if position > 0 and wrapper[position - 1] != "\n":
            raise ValueError("compression declaration must start at a line boundary")
        (work / "xc_sha256_compress.c").write_text("#include <stdint.h>\n" + wrapper[position:])
        cflags = flags("CFLAGS")
        for command in [
            [cc, *cflags, "-c", "src/sha256sum.c", "-o", "sha256sum.o"],
            [cc, "-c", "src/start.S", "-o", "start.o"],
            [cc, "-c", "compress_clang_O2.S", "-o", "compress_clang_O2.o"],
            [cc, *cflags, "-c", "xc_sha256_compress.c", "-o", "compress_gcc_O2.o"]]:
            run(command, work)
        outputs = {}
        for name, compression in [("sha256sum-min", "compress_clang_O2.o"),
                                  ("sha256sum-min-gcc", "compress_gcc_O2.o")]:
            run([cc, *flags("LDFLAGS"), "start.o", "sha256sum.o", compression,
                 "-o", name], work)
            path = work / name
            expected = manifest["outputs"][name]
            outputs[name] = {"sha256": digest(path), "bytes": path.stat().st_size,
                             "matches_historical": digest(path) == expected["sha256"]
                             and path.stat().st_size == expected["bytes"]}
            shutil.copyfile(path, args.out / name)
            (args.out / name).chmod(0o755)
        pilot = json.loads(run([sys.executable, "-I", str(HERE / "scripts/check_pilot_bytes.py"),
                               "sha256sum-min", str(HERE / "src/sha256_compress_clang_O2.hex")], work))
    receipt = {"scope": "new offline reproduction, not historical compiler provenance or a binary proof",
               "compiler": {"path": cc, "sha256": digest(cc), "version": version},
               "current_components": components, "current_linker_version": linker_version,
               "historical_manifest_sha256": MANIFEST_SHA256, "commands": log,
               "outputs": outputs, "pilot_bytes_check": pilot,
               "seconds": time.perf_counter() - started}
    (args.out / "reproduction.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if not all(output["matches_historical"] for output in outputs.values()):
        raise ValueError("new build differs from the historical bytes; see reproduction.json")
    print("both rebuilt executables match the historical hashes")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--cc", default="gcc")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    manifest = verify()
    if args.verify_only:
        print("recovered sources, scripts and Silmaril inputs match the historical manifest")
    elif args.out is None:
        parser.error("--out is required for a build")
    else:
        build(args, manifest)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        sys.exit(str(error))
