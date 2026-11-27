#!/usr/bin/env python3
"""Compare Brotli dictionary transforms with RFC 7932 and pinned libbrotli."""
import argparse
import ast
from hashlib import sha256
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
from urllib.request import urlopen
from zlib import crc32

HERE = Path(__file__).resolve().parent
PIN = "028fb5a23661f123017c060daa546b55cf4bde29"
RFC_URL = "https://www.rfc-editor.org/rfc/rfc7932.txt"
RFC_SHA256 = "394abd1879e016f4eac89512c2acaf92f7b2d67feb8ab58b6b118c213be07146"
WORD_COUNT = 13504
EDGE_WORDS = [
    b"abcd", b"Az-0", b"ab\x00z", b"abcdEFgh",
    bytes.fromhex("c3 a9 61 7a"), bytes.fromhex("e2 82 ac 7a"),
    bytes.fromhex("f0 9f 98 80 7a"), bytes.fromhex("80 bf 61 7a"),
    bytes.fromhex("61 62 63 c0"), bytes.fromhex("61 62 e0 80"),
    bytes.fromhex("61 62 63 e0"), bytes.fromhex("df 80 e0 80 80 7a"),
    b"abcdefghijklmnopqrstuvwxyz"[:24],
]


def check(condition, label):
    if not condition:
        raise ValueError(label)


def run(*args):
    return subprocess.run(args, stdout=subprocess.PIPE, check=True).stdout


def appendix(path):
    if path is None:
        with urlopen(RFC_URL, timeout=30) as response:
            raw = response.read()
    else:
        raw = path.read_bytes()
    check(sha256(raw).hexdigest() == RFC_SHA256, "RFC editor text pin")
    section = raw.decode("ascii").split("\nAppendix B.  List of Word Transformations\n", 1)[1]
    section = section.split("\nAppendix C.  Computing CRC-32 Check Values\n", 1)[0]
    quoted = r'"(?:[^"\\]|\\.)*"'
    pattern = rf"^\s+(\d+)\s+({quoted})\s+(\w+)\s+({quoted})\s*$"
    rows = []
    for ordinal, leading, operation, trailing in re.findall(pattern, section, re.M):
        check(int(ordinal) == len(rows), "Appendix B ordinal")
        rows.append((ast.literal_eval("b" + leading), operation, ast.literal_eval("b" + trailing)))
    codes = {"Identity": 0, "FermentFirst": 1, "FermentAll": 2}
    codes.update({f"OmitFirst{i}": 2 + i for i in range(1, 10)})
    codes.update({f"OmitLast{i}": 11 + i for i in range(1, 10)})
    serialized = b"".join(leading + bytes([0, codes[op]]) + trailing + b"\x00"
                          for leading, op, trailing in rows)
    check(len(rows) == 121 and len(serialized) == 648 and crc32(serialized) == 0x3d965f81,
          "Appendix B entry count, extent and CRC-32")
    return rows, serialized


def rfc_result(word, row):
    leading, operation, trailing = row
    if operation.startswith("OmitFirst"):
        word = word[int(operation[-1]):]
    elif operation.startswith("OmitLast"):
        word = word[:max(0, len(word) - int(operation[-1]))]
    elif operation in ("FermentFirst", "FermentAll"):
        word = bytearray(word)
        pos = 0
        while pos < len(word):
            lead = word[pos]
            width = 1 if lead < 192 else 2 if lead < 224 else 3
            if width == 1 and 97 <= lead <= 122:
                word[pos] ^= 32
            if width > 1 and pos + width <= len(word):
                word[pos + width - 1] ^= 32 if width == 2 else 5
            if operation == "FermentFirst":
                break
            pos += width
    return leading + word + trailing


def encoded(word):
    check(len(word) <= 37, "transformed word exceeds RFC bound")
    return bytes([len(word)]) + word


def native_oracle(source, work):
    if source is None:
        source = work / "brotli"
        run("git", "init", "-q", source)
        run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/google/brotli.git", PIN)
        run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
    check(run("git", "-C", source, "rev-parse", "HEAD").decode().strip() == PIN, "libbrotli revision")
    check(run("git", "-C", source, "diff", "HEAD", "--") == b"", "unmodified libbrotli checkout")
    exe = work / "oracle"
    run("cc", "-std=c99", "-O2", "-Wall", "-Wextra", "-Werror", "-I", source, "-I", source / "c/include",
        HERE / "oracle.c", source / "c/common/dictionary.c", source / "c/common/transform.c", "-o", exe)
    return exe


def compare(lean, native, serialized, rows):
    start = len(serialized)
    check(lean[:start] == serialized and native[:start] == serialized, "all Appendix B rows")
    count = WORD_COUNT * len(rows)
    offset = start
    for pair in range(count):
        check(offset < len(lean) and offset < len(native), f"missing transform record {pair}")
        end = offset + 1 + lean[offset]
        check(lean[offset] <= 37 and end <= len(lean) and lean[offset:end] == native[offset:end],
              f"base word {pair // len(rows)}, transform {pair % len(rows)}")
        offset = end
    edges = b"".join(encoded(rfc_result(word, row)) for word in EDGE_WORDS for row in rows)
    check(lean[offset:] == edges and native[offset:] == edges, "authored edge words vs RFC byte interpreter")
    print(f"Matched all {len(rows)} Appendix B rows (CRC-32 {crc32(serialized):08x})")
    print(f"Matched all {count} dictionary-word/transform pairs against libbrotli {PIN}")
    print(f"Matched {len(EDGE_WORDS) * len(rows)} authored edge cases against libbrotli and RFC §8")
    print(f"SHA-256 of length-prefixed canonical outputs: {sha256(lean[start:offset]).hexdigest()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rfc", type=Path)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    rows, serialized = appendix(args.rfc)
    with TemporaryDirectory(prefix="silmaril-brotli-transform-") as directory:
        work = Path(directory)
        edges, lean = work / "edges.bin", work / "lean.bin"
        edges.write_bytes(b"".join(encoded(word) for word in EDGE_WORDS))
        exe = native_oracle(args.brotli_source.resolve() if args.brotli_source else None, work)
        native = run(exe, edges)
        run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
            "--run", HERE / "Interop.lean", edges, lean)
        compare(lean.read_bytes(), native, serialized, rows)


if __name__ == "__main__":
    main()
