"""Mutants of C++ symbol lists, for the demangler differential (meta-differential.sh).

symbols-mutate.py COUNT SEED LIST... : COUNT distinct mutants of the `_Z` symbols of the
lists (truncation, deletion, insertion or replacement of one character), sorted, one per
line. Deterministic for a given seed and input.
"""
import random
import sys

def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    random.seed(seed)
    src = [l.strip() for f in sys.argv[3:] for l in open(f) if l.strip().startswith("_Z")]
    alpha = "0123456789_ESTIJLXDpfdtrlsvnwaicKRPOVZNEFAM"
    out = set()
    while len(out) < count:
        s = random.choice(src)
        k = random.randrange(4)
        i = random.randrange(2, len(s) + 1)
        if k == 0:
            t = s[:i]
        elif k == 1:
            t = s[:i - 1] + s[i:]
        elif k == 2:
            t = s[:i] + random.choice(alpha) + s[i:]
        else:
            t = s[:i - 1] + random.choice(alpha) + s[i:]
        if len(t) > 2:
            out.add(t)
    for t in sorted(out):
        print(t)

main()
