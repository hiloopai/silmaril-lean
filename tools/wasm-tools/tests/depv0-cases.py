#!/usr/bin/env python3
"""Write WAT files with `.dep-v0` custom sections (cargo-auditable dependency lists) for the
`metadata show` differential test (python3 -I; standard library only).

  depv0-cases.py OUTDIR

Each case is OUTDIR/dep-<name>.wat: a module (or a component holding one) whose `.dep-v0`
section is a zlib stream of a JSON text, valid or not, compressed at several levels, or a
malformed stream.
"""
import json, os, sys, zlib

def esc(b):
    return "".join("\\%02x" % x for x in b)

def module(data, extra=""):
    return '(module (@custom ".dep-v0" "%s")%s)\n' % (esc(data), extra)

def pkgs(n, **kw):
    out = []
    for i in range(n):
        p = {"name": "crate%d" % i, "version": "1.%d.0" % i, "source": "crates.io"}
        if i + 1 < n: p["dependencies"] = [i + 1]
        out.append(p)
    out[0]["root"] = True
    return out

def main():
    d = sys.argv[1]
    cases = {}
    simple = {"packages": [
        {"name": "adler", "version": "1.0.2", "source": "crates.io", "kind": "build"},
        {"name": "my-app", "version": "0.1.0-alpha.1+build.5", "source": "local", "dependencies": [0, 2], "root": True},
        {"name": "serde\"xé☃", "version": "1.0.188", "source": "git"},
    ]}
    for lvl in (0, 1, 6, 9):
        cases["simple-l%d" % lvl] = module(zlib.compress(json.dumps(simple).encode(), lvl))
    cases["many"] = module(zlib.compress(json.dumps({"packages": pkgs(300)}).encode(), 9))
    cases["format"] = module(zlib.compress(b'{"format": 7, "packages": []}'))
    cases["unknown-field"] = module(zlib.compress(b'{"packages": [{"name":"a","version":"1.0.0","source":"registry","extra":[1,{"x":null}]}], "x": 1}'))
    cases["array-form"] = module(zlib.compress(b'[[["a","1.0.0","crates.io","build",[],true]]]'))
    cases["kind-map"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"crates.io","kind":{"build":null}}]}'))
    cases["escaped-name"] = module(zlib.compress(b'{"packages":[{"name":"a\\u00e9\\ud83d\\ude00\\n","version":"1.0.0","source":"crates.io"}]}'))
    cases["ws"] = module(zlib.compress(b' \n\t{ "packages" : [ ] } \r\n'))
    cases["out-of-range-dep"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"crates.io","dependencies":[5]}]}'))
    cases["dup-dep"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"x"},{"name":"b","version":"1.0.0","source":"y","dependencies":[0,0]}]}'))
    cases["in-component"] = '(component (core module (@custom ".dep-v0" "%s")) (@custom ".dep-v0" "%s"))\n' % (
        esc(zlib.compress(json.dumps(simple).encode())), esc(zlib.compress(b'{"packages":[]}')))
    cases["trailing-garbage-after-stream"] = module(zlib.compress(b'{"packages":[]}') + b"garbage")
    # errors
    cases["err-not-zlib"] = module(b"not zlib at all")
    cases["err-empty"] = module(b"")
    good = zlib.compress(json.dumps(simple).encode(), 6)
    cases["err-truncated"] = module(good[:len(good) // 2])
    cases["err-adler"] = module(good[:-1] + bytes([good[-1] ^ 1]))
    cases["err-no-adler"] = module(good[:-4])
    cases["err-dict"] = module(bytes([0x78, 0xbb]) + good[2:])
    cases["err-big"] = module(zlib.compress(b"0" * (2 * 1024 * 1024 + 1), 9))
    cases["ok-limit"] = module(zlib.compress(b'{"packages":[]}' + b" " * (2 * 1024 * 1024 - 15), 9))
    cases["err-utf8"] = module(zlib.compress(b'{"packages":[{"name":"\xff","version":"1.0.0","source":"x"}]}'))
    cases["err-json"] = module(zlib.compress(b'{"packages":[}'))
    cases["err-trailing-comma"] = module(zlib.compress(b'{"packages":[],}'))
    cases["err-trailing-chars"] = module(zlib.compress(b'{"packages":[]} x'))
    cases["err-missing"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0"}]}'))
    cases["err-semver"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0","source":"x"}]}'))
    cases["err-semver-zero"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"01.0.0","source":"x"}]}'))
    cases["err-source-escape"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"crates\\u002eio"}]}'))
    cases["err-roots"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"x","root":true},{"name":"b","version":"1.0.0","source":"x","root":true}]}'))
    cases["err-cycle"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"x","dependencies":[1]},{"name":"b","version":"1.0.0","source":"x","dependencies":[0]}]}'))
    cases["err-self"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"x","dependencies":[0]}]}'))
    cases["err-dup-field"] = module(zlib.compress(b'{"packages":[],"packages":[]}'))
    cases["err-kind"] = module(zlib.compress(b'{"packages":[{"name":"a","version":"1.0.0","source":"x","kind":"dev"}]}'))
    cases["err-format-float"] = module(zlib.compress(b'{"packages":[],"format":1.0}'))
    cases["err-control"] = module(zlib.compress(b'{"packages":[{"name":"a\x01","version":"1.0.0","source":"x"}]}'))
    for name, wat in cases.items():
        with open(os.path.join(d, "dep-%s.wat" % name), "w") as f:
            f.write(wat)

main()
