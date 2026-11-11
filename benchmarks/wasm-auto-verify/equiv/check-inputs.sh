#!/usr/bin/env bash
# Check that the Lean copies of the pinned inputs (tests/wasm/auto/EquivXBench/Defs.lean and the
# requant kernel of tests/wasm/auto/FrontBench/Defs.lean) equal the files of this directory.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
python3 -I - "$repo" "$here" <<'PY'
import sys
repo, here = sys.argv[1], sys.argv[2]
def lean_block(path, name):
    s = open(path).read()
    a = s.index('def %s := wat3! r#"' % name)
    a = s.index('r#"', a) + 3
    b = s.index('"#', a)
    return s[a:b].strip()
bench = repo + '/tests/wasm/auto/EquivXBench/Defs.lean'
front = repo + '/tests/wasm/auto/FrontBench/Defs.lean'
pairs = [(front, 'requantFixed', 'requant.wat'), (bench, 'requantO2', 'requant.binaryen-O2.wat'),
         (bench, 'adler8', 'adler8.wat'), (bench, 'adler8O2', 'adler8.binaryen-O2.wat'),
         (bench, 'adler1x8', 'adler1x8.wat'), (bench, 'adler1x8O2', 'adler1x8.binaryen-O2.wat')]
bad = 0
for path, name, f in pairs:
    if lean_block(path, name) != open(here + '/' + f).read().strip():
        print('check-inputs: %s differs from %s' % (name, f)); bad = 1
if open(here + '/requant.binaryen-O2.wat').read() != open(here + '/requant.binaryen-O3.wat').read():
    print('check-inputs: requant -O2 and -O3 outputs differ (the benchmark uses -O2)')
sys.exit(bad)
PY
echo "check-inputs: ok"
