#!/usr/bin/env python3
"""Build the pinned SQLite matrix in a new work directory."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import zipfile

BASELINE = "gcc-O2"
BUILDS = [f"{cc}-O{level}" for cc in ("gcc", "clang") for level in range(4)]
ROOT = "sqlite-amalgamation-3540100"
SOURCE = {
    "version": "3.54.1",
    "url": f"https://sqlite.org/2026/{ROOT}.zip",
    "archive_sha256": "0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9",
    "archive_sha3_256": "92281c86e2957f9b9305890f9ac04204caa7b677cc868dc326d942689df28e30",
    "sqlite3.c": "0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52",
    "sqlite3.h": "d6c84557261893439b341d2e6c35187ae3ea24fbfd843ad94616f72d89242b8c",
}
DEFINES = {
    "SQLITE_THREADSAFE": "1",
    "SQLITE_OMIT_LOAD_EXTENSION": "1",
    "SQLITE_MAX_MMAP_SIZE": "0",
    "SQLITE_DEFAULT_MMAP_SIZE": "0",
}
FIXED_ENV = {"LC_ALL": "C", "TZ": "UTC", "SOURCE_DATE_EPOCH": "0"}
ENV = {"PATH": os.environ["PATH"], **FIXED_ENV}
STRIP = ["strip", "--strip-all", "-o", "stripped.so", "libsqlite3.so"]
PACKAGES = ["gcc-14", "clang-19", "binutils", "libc6", "libc6-dev", "libgcc-14-dev",
            "linux-libc-dev", "llvm-19", "python3", "rustc", "cargo"]


def run(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, env=ENV, stderr=subprocess.STDOUT,
                                   text=True, encoding="utf-8")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def fetch(archive, source_dir):
    if archive is None:
        archive = source_dir / "source.zip"
        run(["curl", "--fail", "--location", "--retry", "3", "--max-time", "120",
             "--output", str(archive), SOURCE["url"]])
    data = archive.read_bytes()
    require(hashlib.sha256(data).hexdigest() == SOURCE["archive_sha256"], "archive SHA-256")
    require(hashlib.sha3_256(data).hexdigest() == SOURCE["archive_sha3_256"], "archive SHA3-256")
    with zipfile.ZipFile(archive) as upstream:
        for name in ("sqlite3.c", "sqlite3.h"):
            data = upstream.read(f"{ROOT}/{name}")
            require(hashlib.sha256(data).hexdigest() == SOURCE[name], f"{name} SHA-256")
            (source_dir / name).write_bytes(data)
    header = (source_dir / "sqlite3.h").read_text()
    return re.search(r'^#define SQLITE_SOURCE_ID\s+"([^"]+)"', header, re.M)[1]


def compile_one(build, output):
    cc, opt = build.split("-")
    work = output / build
    work.mkdir()
    flags = [
        f"-{opt}", "-m64", "-march=x86-64", "-mtune=generic", "-fPIC", "-fno-builtin",
        "-fno-lto", "-pthread", "-g", "-gdwarf-4",
        f"-ffile-prefix-map={output}=.", f"-fdebug-prefix-map={output}=.",
        *[f"-D{key}={value}" for key, value in DEFINES.items()],
    ]
    compile_args = [cc, *flags, "-c", "../source/sqlite3.c", "-o", "sqlite3.o"]
    link_driver = [cc, "-m64", "-fno-lto", "-pthread", "-fuse-ld=bfd", "-shared"]
    link_options = "-Wl,--as-needed,--build-id=sha1,-soname,libsqlite3.so.0"
    link_inputs = ["sqlite3.o", "-lm"]
    link_args = [*link_driver, link_options, "-o", "libsqlite3.so", *link_inputs]
    relocs_args = [*link_driver, "-Wl,--emit-relocs", link_options, "-o", "relocs.so", *link_inputs]
    for args in (compile_args, link_args, relocs_args, STRIP):
        run(args, work)
    # Store the expanded driver commands for audit. They contain host paths.
    (work / "driver.txt").write_text(run([cc, "-###", *compile_args[1:]], work)
                                     + run([cc, "-###", *link_args[1:]], work)
                                     + run([cc, "-###", *relocs_args[1:]], work))
    macro_args = [cc, *flags, "-dM", "-E", "../source/sqlite3.c"]
    macros = sorted(run(macro_args, work).splitlines())
    (work / "macros.txt").write_text("\n".join(macros) + "\n")
    file_names = ("sqlite3.o", "libsqlite3.so", "stripped.so", "relocs.so", "macros.txt")
    return {
        "commands": [[arg.replace(str(output), "$WORK") for arg in args]
                     for args in (compile_args, link_args, relocs_args, STRIP, macro_args)],
        "files": {name: {"sha256": hashlib.sha256((work / name).read_bytes()).hexdigest(),
                         "size_bytes": (work / name).stat().st_size} for name in file_names},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("work", type=Path, help="new build directory")
    parser.add_argument("--archive", type=Path, help="already downloaded upstream zip")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    require(sys.platform == "linux" and platform.machine() == "x86_64", "requires Linux x86-64")
    require(run(["getconf", "GNU_LIBC_VERSION"]).startswith("glibc "), "requires glibc")
    work = args.work.resolve()
    work.mkdir()
    source_dir = work / "source"
    source_dir.mkdir()
    source_id = fetch(args.archive, source_dir)
    commands = {
        "gcc": ["gcc", "--version"], "clang": ["clang", "--version"],
        "gnu_ld": ["ld.bfd", "--version"], "gnu_as": ["as", "--version"],
        "strip": ["strip", "--version"], "readelf": ["readelf", "--version"],
        "objdump": ["objdump", "--version"], "llvm_objdump": ["llvm-objdump", "--version"],
        "glibc": ["getconf", "GNU_LIBC_VERSION"], "gcc_target": ["gcc", "-dumpmachine"],
        "clang_target": ["clang", "-dumpmachine"],
    }
    versions = {tool: run(command).splitlines()[0] for tool, command in commands.items()}
    versions["python"] = platform.python_version()
    try:
        packages = dict(line.split("\t", 1) for line in
                        run(["dpkg-query", "-W", "-f=${Package}\t${Version}\n",
                             *PACKAGES]).splitlines())
    except (FileNotFoundError, subprocess.CalledProcessError):
        packages = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = dict(zip(BUILDS, pool.map(lambda build: compile_one(build, work), BUILDS)))
    write_json(work / "build.json", {
        "source": {**SOURCE, "sqlite_source_id": source_id},
        "baseline": BASELINE,
        "target": "x86_64 Linux SysV ELF64 little-endian glibc",
        "defines": DEFINES,
        "build_environment": FIXED_ENV,
        "tools": versions,
        "debian_packages": packages,
        "builds": results,
    })


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.output)
