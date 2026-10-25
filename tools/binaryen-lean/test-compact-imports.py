#!/usr/bin/env python3
"""Independent compact-import bytes, exact expansion and real optimization.

Node checks emitted ordinary Core binaries against independently authored flat
references; Node need not support the compact-import proposal. An optional
upstream Binaryen validates original encodings and independently expands them.
"""

import argparse
import shutil
import subprocess
import tempfile
from pathlib import Path


def uleb(value):
    result = bytearray()
    while value >= 128:
        result.append((value & 127) | 128)
        value >>= 7
    result.append(value)
    return bytes(result)


def name(value):
    raw = value.encode("utf-8")
    return uleb(len(raw)) + raw


def vector(items):
    return uleb(len(items)) + b"".join(items)


def section(tag, payload):
    return bytes([tag]) + uleb(len(payload)) + payload


FUNC = bytes([0, 0])
GLOBAL = bytes([3, 0x7F, 0])
MUT_GLOBAL = bytes([3, 0x7F, 1])
MEMORY = bytes([2, 0, 1])
TABLE = bytes([1, 0x70, 0, 1])
TAG = bytes([4, 0, 1])


def ordinary(module, field, descriptor):
    return name(module) + name(field) + descriptor


def compact1(module, entries, *, empty=b"\0", marker=b"\x7f"):
    return name(module) + empty + marker + vector([name(n) + d for n, d in entries])


def compact2(module, descriptor, fields, *, empty=b"\0", marker=b"\x7e"):
    return name(module) + empty + marker + descriptor + vector([name(n) for n in fields])


def module(groups, *, mixed=False, nop=True, empty_names=False):
    types = bytes([2, 0x60, 0, 1, 0x7F, 0x60, 0, 0])
    imported_functions = 4 if mixed else 2
    instructions = bytes([0x10, 0, 0x10, 1, 0x6B])  # a - b: order matters
    if mixed:
        instructions += bytes([0x10, 2, 0x6A, 0x10, 3, 0x6A,
                               0x23, 0, 0x6A, 0x23, 1, 0x6A, 0x23, 2, 0x6A])
    body = bytes([0]) + (b"\x01" if nop else b"") + instructions + b"\x0b"
    exports = [name("run") + bytes([0, imported_functions])]
    if mixed:
        exports += [name("memory") + bytes([2, 0]), name("table") + bytes([1, 0]),
                    name("tag") + bytes([4, 0]), name("counter") + bytes([3, 1])]
    return (b"\0asm\1\0\0\0" + section(1, types) + section(2, vector(groups))
            + section(3, bytes([1, 0])) + section(7, vector(exports))
            + section(10, vector([uleb(len(body)) + body])))


def fixtures():
    entries = [("a", FUNC), ("b", FUNC)]
    flat = [ordinary("env", field, descriptor) for field, descriptor in entries]
    for kind in [1, 2]:
        for padded in [False, True]:
            empty = b"\x80\x80\x80\0" if padded else b"\0"
            group = (compact1("env", entries, empty=empty) if kind == 1 else
                     compact2("env", FUNC, ["a", "b"], empty=empty))
            yield f"compact{kind}-padded-{padded}", [group], flat, False, True
        empty_group = compact1("unused", []) if kind == 1 else compact2("unused", FUNC, [])
        group = compact1("env", entries) if kind == 1 else compact2("env", FUNC, ["a", "b"])
        yield f"compact{kind}-empty-group", [empty_group, group], flat, False, True

    # The proposal/reference interpreter flatten before unchanged validation.
    # This unused descriptor contributes no import; Binaryen eagerly resolves
    # it and is stricter than that expansion semantics.
    yield "empty-unused-descriptor", [compact2("unused", bytes([0, 99]), []),
                                     compact1("env", entries)], flat, False, False

    empty_flat = [ordinary("", "", FUNC), ordinary("env", "b", FUNC)]
    yield "ordinary-empty-names", [empty_flat[0], compact2("env", FUNC, ["b"])], empty_flat, False, True

    # Interleave external kinds: flattening must preserve each index space.
    groups = [ordinary("env", "a", FUNC),
              compact1("env", [("b", FUNC), ("g", GLOBAL), ("memory", MEMORY),
                               ("table", TABLE), ("tag", TAG)]),
              compact2("env", FUNC, ["c", "d"]),
              compact2("env", MUT_GLOBAL, ["ga", "gb"])]
    flat = [ordinary("env", field, descriptor) for field, descriptor in
            [("a", FUNC), ("b", FUNC), ("g", GLOBAL), ("memory", MEMORY),
             ("table", TABLE), ("tag", TAG), ("c", FUNC), ("d", FUNC),
             ("ga", MUT_GLOBAL), ("gb", MUT_GLOBAL)]]
    yield "mixed-kinds-and-groups", groups, flat, True, True


def malformed():
    entries = [("a", FUNC), ("b", FUNC)]
    for kind in [1, 2]:
        build = (lambda **kw: compact1("env", entries, **kw)) if kind == 1 else (
            lambda **kw: compact2("env", FUNC, ["a", "b"], **kw))
        yield f"nonempty-marker-{kind}", [build(empty=name("x"))]
        yield f"leb-marker-{kind}", [build(marker=bytes([0xFF if kind == 1 else 0xFE, 0]))]
        yield f"truncated-group-{kind}", [build()[:-1]]
    yield "unknown-descriptor", [compact1("env", [("a", b"\x05")])]
    yield "nested-group-descriptor", [compact1("env", [("", b"\x7f\0")])]
    yield "invalid-type-index", [compact2("env", bytes([0, 99]), ["a", "b"])]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-opt")
    parser.add_argument("driver", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    driver = args.driver or [".lake/build/bin/wasm-opt"]
    if driver[0] == "--":
        driver = driver[1:]
    node = shutil.which("node")
    if node is None:
        raise SystemExit("Node is required to validate and execute ordinary Core outputs")

    with tempfile.TemporaryDirectory(prefix="wasm-compact-imports-") as directory:
        root = Path(directory)
        observations = []
        for label, groups, flat, mixed, upstream_accepts in fixtures():
            source = root / f"{label}.wasm"
            source.write_bytes(module(groups, mixed=mixed))
            reference = root / f"{label}-reference.wasm"
            reference.write_bytes(module(flat, mixed=mixed))
            paths = [reference]
            if args.upstream_opt:
                expanded = root / f"{label}-upstream.wasm"
                text = root / f"{label}-upstream.wat"
                # Reading needs the feature enabled; ordinary WAT then permits
                # encoding it without compact groups in a separate invocation.
                checked = subprocess.run([args.upstream_opt, str(source), "-all", "-S", "-o", str(text)],
                                         capture_output=True, text=True, timeout=30)
                if upstream_accepts:
                    assert checked.returncode == 0, (label, checked.stderr)
                    checked = subprocess.run([args.upstream_opt, str(text), "-all",
                                              "--disable-compact-imports", "-o", str(expanded)],
                                             capture_output=True, text=True, timeout=30)
                    assert checked.returncode == 0, (label, checked.stderr)
                    paths.append(expanded)
                else:
                    assert checked.returncode != 0, (label, "expected documented Binaryen eager-check divergence")
            for label_pass, flags in [("empty", []), ("vacuum", ["--vacuum"]), ("O2", ["-O2"])]:
                output = root / f"{label}-{label_pass}.wasm"
                checked = subprocess.run([*driver, str(source), *flags, "-o", str(output)],
                                         capture_output=True, text=True, timeout=90)
                assert checked.returncode == 0, (label, flags, checked.stdout, checked.stderr)
                if label_pass in ["empty", "vacuum"]:
                    expected = module(flat, mixed=mixed, nop=label_pass == "empty")
                    assert output.read_bytes() == expected, (label, label_pass, "wrong expansion or missing nop removal")
                else:
                    assert len(output.read_bytes()) < len(reference.read_bytes()), (label, "no O2 reduction")
                paths.append(output)
            observations += [(str(path), mixed) for path in paths]

        for label, groups in malformed():
            source = root / f"bad-{label}.wasm"
            output = root / f"bad-{label}-out.wasm"
            source.write_bytes(module(groups))
            checked = subprocess.run([*driver, str(source), "--vacuum", "-o", str(output)],
                                     capture_output=True, text=True, timeout=90)
            assert checked.returncode != 0 and not output.exists(), (label, checked.stderr)
            if args.upstream_opt:
                checked = subprocess.run([args.upstream_opt, str(source), "-all", "-o", str(output)],
                                         capture_output=True, text=True, timeout=30)
                assert checked.returncode != 0, (label, "upstream accepted invalid fixture")

        import json
        checked = subprocess.run([node, "-e", """
const fs = require('fs');
for (const [path, mixed] of JSON.parse(process.argv[1])) {
  const bytes = fs.readFileSync(path);
  if (!WebAssembly.validate(bytes)) throw Error('invalid ordinary Core: ' + path);
  const env = { a: () => 15, b: () => 240, c: () => 3, d: () => 5, g: 11,
    ga: new WebAssembly.Global({value:'i32', mutable:true}, 19),
    gb: new WebAssembly.Global({value:'i32', mutable:true}, 23),
    memory: new WebAssembly.Memory({initial:1}),
    table: new WebAssembly.Table({element:'anyfunc', initial:1}),
    tag: new WebAssembly.Tag({parameters:[]}) };
  const instance = new WebAssembly.Instance(new WebAssembly.Module(bytes), {env, '': {'': () => 15}});
  const expected = mixed ? -164 : -225;
  for (let i = 0; i < 3; i++) if (instance.exports.run() !== expected) throw Error('import order: ' + path);
  if (mixed) {
    for (const key of ['memory', 'table', 'tag'])
      if (instance.exports[key] !== env[key]) throw Error('changed imported state: ' + key);
    if (instance.exports.counter !== env.ga) throw Error('changed imported global');
    env.ga.value = 29;
    if (instance.exports.run() !== expected + 10) throw Error('lost shared global');
  }
}
""", json.dumps(observations)], capture_output=True, text=True, timeout=30)
        assert checked.returncode == 0, (checked.stdout, checked.stderr)
    print("Compact imports: both layouts, padding, empty groups/names and mixed external kinds passed")
    print("Exact expansion, actual nop removal, O2 reduction, malformed rejection and Node state observations passed")
    if args.upstream_opt:
        print("Upstream Binaryen validated/expanded common fixtures and rejected malformed cases; empty-unused descriptor divergence confirmed")


if __name__ == "__main__":
    main()
