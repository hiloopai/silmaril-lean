#!/usr/bin/env python3
"""Sample Berkeley TestFloat vectors (SoftFloat's RISC-V specialization) into a Lean table.

Usage: testfloat-vectors.py <testfloat_gen> <per-group> <out.lean>

`testfloat_gen` must be TestFloat 3e built against SoftFloat 3 with
SPECIALIZE_TYPE=RISCV. The pinned inputs used for the committed table are:

* TestFloat-3e.zip (http://www.jhauser.us/arithmetic/TestFloat-3e.zip),
  sha256 6d4bdf0096b48a653aa59fc203a9e5fe18b5a58d7a1b715107c7146776a0aad6;
* berkeley-softfloat-3 master tarball at commit 497c81c1f5016dc6ef5b3219ece2f3c261d4d8f1
  (https://github.com/ucb-bar/berkeley-softfloat-3/archive/refs/heads/master.tar.gz),
  sha256 cd1513b603dec003bb8e125b39494c66e59332eae6c627b666f81eeae9db19c4.

Build: `make SPECIALIZE_TYPE=RISCV` in SoftFloat's build/Linux-x86_64-GCC, then
`make SOFTFLOAT_DIR=<softfloat> testfloat_gen` in TestFloat's build/Linux-x86_64-GCC.

Every group (function, rounding mode) is generated at TestFloat level 1 with seed 1
(the defaults) and sampled at an even stride, so the table is deterministic. Each line
of the table is `<op> <fmt...> <mode> <operands...> <result> <flags>` in hex, the flags
in RISC-V `fflags` order (TestFloat's order: NX=1, UF=2, OF=4, DZ=8, NV=16).
"""

import subprocess
import sys

MODES = [("rne", "-rnear_even"), ("rtz", "-rminMag"), ("rdn", "-rmin"),
         ("rup", "-rmax"), ("rmm", "-rnear_maxMag")]

def groups():
    for fmt in ("f32", "f64"):
        for op in ("add", "sub", "mul", "div"):
            for md, flag in MODES:
                yield (f"{fmt}_{op}", md, flag, f"{op} {fmt}")
        for md, flag in MODES:
            yield (f"{fmt}_sqrt", md, flag, f"sqrt {fmt}")
        for md, flag in MODES:
            yield (f"{fmt}_mulAdd", md, flag, f"fma {fmt}")
        for op in ("eq", "lt", "le"):
            yield (f"{fmt}_{op}", "rne", "-rnear_even", f"{op} {fmt}")
        for it in ("i32", "ui32", "i64", "ui64"):
            for md, flag in MODES:
                yield (f"{it}_to_{fmt}", md, flag, f"ofInt {fmt} {it}")
                yield (f"{fmt}_to_{it}", md, flag, f"toInt {fmt} {it}")
    yield ("f32_to_f64", "rne", "-rnear_even", "convert f32 f64")
    for md, flag in MODES:
        yield ("f64_to_f32", md, flag, "convert f64 f32")

def main():
    gen, per, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    lines = []
    for fn, md, flag, head in groups():
        res = subprocess.run([gen, "-tininessafter", "-exact", flag, fn],
                             check=True, capture_output=True, text=True)
        cases = res.stdout.split("\n")
        cases = [c for c in cases if c.strip()]
        stride = max(1, len(cases) // per)
        for c in cases[::stride][:per]:
            lines.append(f"{head} {md} {c.strip()}")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"{len(lines)} vectors")

if __name__ == "__main__":
    main()
