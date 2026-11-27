#!/usr/bin/env python3
"""Compare the checked Brotli dictionary with RFC Appendix A and pinned libbrotli."""
import argparse
import ctypes as C
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
from urllib.request import urlopen
from zlib import crc32

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "data/brotli-static-dictionary"
PIN = "028fb5a23661f123017c060daa546b55cf4bde29"
RFC_URL = "https://www.rfc-editor.org/rfc/rfc7932.txt"
RFC_SHA256 = "394abd1879e016f4eac89512c2acaf92f7b2d67feb8ab58b6b118c213be07146"
DICT_SHA256 = "20e42eb1b511c21806d4d227d07e5dd06877d8ce7b3a817f378f313653f35c70"


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
    text = raw.decode("ascii")
    section = text.split("\nAppendix A.  Static Dictionary Data\n", 1)[1]
    section = section.split("\nAppendix B.  List of Word Transformations\n", 1)[0]
    payload = bytes.fromhex("".join(re.findall(r"^      ([0-9a-f]{2,})$", section, re.M)))
    depth_text = section.split("NDBITS :=", 1)[1]
    depths = [int(value) for value in re.findall(r"\d+", depth_text)]
    check(len(depths) == 25 and len(payload) == 122784 and crc32(payload) == 0x5136cb04,
          "RFC Appendix A size, depth table and CRC-32")
    check(sha256(payload).hexdigest() == DICT_SHA256, "RFC dictionary SHA-256")
    counts = [1 << depths[n] if 4 <= n <= 24 else 0 for n in range(26)]
    offsets = [0]
    for length, count in enumerate(counts[:-1]):
        offsets.append(offsets[-1] + length * count)
    check(offsets[-1] == len(payload), "RFC §8 exact dictionary extent")
    return payload, depths, counts, offsets


class BrotliDictionary(C.Structure):
    _fields_ = [("depths", C.c_uint8 * 32), ("offsets", C.c_uint32 * 32),
                ("size", C.c_size_t), ("data", C.POINTER(C.c_uint8))]


def verify_native(source, work, canonical, depths, offsets):
    if source is None:
        source = work / "brotli"
        run("git", "init", "-q", source)
        run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/google/brotli.git", PIN)
        run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
    check(run("git", "-C", source, "rev-parse", "HEAD").decode().strip() == PIN, "libbrotli revision")
    check(run("git", "-C", source, "diff", "HEAD", "--") == b"", "unmodified libbrotli checkout")
    check((source / "c/common/dictionary.bin").read_bytes() == canonical, "libbrotli source dictionary")
    check((DATA / "LICENSE").read_bytes() == (source / "LICENSE").read_bytes(), "upstream MIT license")
    library = work / "dictionary.so"
    run("cc", "-shared", "-fPIC", "-I", source / "c/include", source / "c/common/dictionary.c", "-o", library)
    module = C.CDLL(str(library))
    module.BrotliGetDictionary.argtypes = []
    module.BrotliGetDictionary.restype = C.POINTER(BrotliDictionary)
    table = module.BrotliGetDictionary().contents
    check(list(table.depths)[:25] == depths and list(table.offsets)[:26] == offsets,
          "compiled libbrotli depths and offsets")
    check(table.size == len(canonical) and C.string_at(table.data, table.size) == canonical,
          "compiled libbrotli dictionary bytes")


def requests(canonical, counts, offsets):
    for length in range(4, 25):
        count = counts[length]
        for word_id in (0, count - 1, count, 120 * count, 121 * count - 1, 121 * count):
            transform, index = divmod(word_id, count)
            yield f"split {length} {word_id}", [length, index, transform] if transform < 121 else "wordId"
        for index in (0, count - 1, count):
            start = offsets[length] + index * length
            yield f"lookup {length} {index}", list(canonical[start:start + length]) if index < count else "wordIndex"
    for length in (0, 3, 25, 256):
        yield f"split {length} 0", "wordLength"
        yield f"lookup {length} 0", "wordLength"


def verify_lean(work, canonical, counts, offsets):
    embedded, words, queries = (work / name for name in ("embedded.bin", "words.bin", "queries.txt"))
    cases, expected = zip(*requests(canonical, counts, offsets))
    queries.write_text("\n".join(cases) + "\n", encoding="ascii")
    result = json.loads(run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                            ROOT / "scripts/brotli-static-dictionary/Interop.lean", embedded, words, queries))
    check(embedded.read_bytes() == canonical, "Lean embedded dictionary")
    check(words.read_bytes() == canonical, "exhaustive checked base-word lookup")
    check(result["offsets"] == offsets and result["counts"] == counts, "Lean dictionary layout")
    check(len(result["queries"]) == len(expected), "Lean boundary request count")
    for case, found, expected_value in zip(cases, result["queries"], expected):
        check(found == expected_value, f"{case}: {found} != {expected_value}")
    print(f"Matched {sum(counts)} checked words across 21 buckets and {len(cases)} address/lookup controls")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rfc", type=Path, help="use the pinned RFC 7932 text from disk")
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    canonical, depths, counts, offsets = appendix(args.rfc)
    check((DATA / "dictionary.bin").read_bytes() == canonical, "bundled dictionary equals Appendix A")
    with TemporaryDirectory(prefix="silmaril-brotli-dictionary-") as directory:
        work = Path(directory)
        verify_native(args.brotli_source.resolve() if args.brotli_source else None, work, canonical, depths, offsets)
        verify_lean(work, canonical, counts, offsets)
    print(f"RFC 7932 and libbrotli {PIN} match all {len(canonical)} bytes")
    print(f"SHA-256 {DICT_SHA256}; RFC CRC-32 {crc32(canonical):08x}")


if __name__ == "__main__":
    main()
