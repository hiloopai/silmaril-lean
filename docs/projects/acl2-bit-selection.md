# ACL2 8.7 logical bit selection

Import `Silmaril.Logic.ACL2.Standard.BitSelection.Thms` for the definitions and
correspondence theorems on the standard ACL2 `Object` carrier.
`Object.partSelectLowHigh_source` equates the generic implementation and the
lowering of the translated logical body of
`BITOPS::PART-SELECT-LOW-HIGH$INLINE` for all payloads and bounds.
[Theorem header](../../Silmaril/Logic/ACL2/Standard/BitSelection/Thms.lean) ·
[Standard objects](acl2-standard-objects.md)

The translated body calls `PART-SELECT-WIDTH-LOW$INLINE` with width
`1 + (high - low)` and the original low bound. The width uses ACL2 object
arithmetic. Nonnumbers contribute zero to that arithmetic, and fractional or
complex bounds can cancel to an integer width. Width/low applies `LOGTAIL` and
then `LOGHEAD`. The translated `IFLOOR`, `IMOD`, and `EXPT2` equations yield
the floor quotient by `2 ^ nfix(low)` and the nonnegative remainder modulo
`2 ^ nfix(width)`, on the `ifix` of the payload. A bound fixed to zero uses
divisor or modulus one. At position zero the tail is `ifix(x)`, and at width
zero the head is zero. An integer high bound below the integer low bound gives
width zero after the fix. `logtail_ash` connects the floor quotient to the
shared signed shift, and `loghead_range` proves the remainder bound.
[Part-select definitions](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/bitops/part-select.lisp#L63-L78) ·
[`IFLOOR`, `IMOD` and `EXPT2`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/ihs/basic-definitions.lisp#L156-L197) ·
[LOGHEAD and LOGTAIL](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/ihs/basic-definitions.lisp#L394-L434)

## Source and proof boundary

The exporter loads the certified `centaur/bitops/part-select` book at ACL2 8.7
commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`. It takes seven
`unnormalized-body` properties through ACL2's `remove-guard-holders` and
records their fully qualified formals and calls. The source checker resolves
those identities and arities and restricts `EXPT` to base two with an
`NFIX` exponent and `FLOOR`/`MOD` to `IFIX` operands. Arithmetic leaves
use the standard object operations and the existing rational quotient model.
Lean proves the equations for the lowered bodies and checks the 31 native
observations against the generic functions. The projection and Python lowering
are part of the source trust boundary. Coverage is local to those seven bodies
and the stated arithmetic interpretations.
[Fixture](../../corpus/acl2/bit-selection/acl2-8.7.json) ·
[Generated Lean](../../Silmaril/Logic/ACL2/Standard/BitSelection/Source.lean) ·
[ACL2 FLOOR](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L7134-L7169) ·
[ACL2 MOD](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L7266-L7270)

## Checks

From the Silmaril root, with Git, SBCL and GNU Make, run the following. The two
fresh ACL2 processes use guard checking `:none` for the observations. The
fixture SHA-256 is
`8f04b8d63eabca0824215f09ea488dfbf90cdc921986a54950c9d3d85c83a561`.

```sh
work=$(mktemp -d)
git clone --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$work/acl2"
test "$(git -C "$work/acl2" rev-parse HEAD)" = bc6f4f49e81a0711214a8d91f0d06e0e084d2204
make -C "$work/acl2" LISP=sbcl
(
  cd "$work/acl2"
  export ACL2_CUSTOMIZATION=NONE X86ISA_EXEC=nil
  books/build/cert.pl --acl2 "$work/acl2/saved_acl2" --acl2-books "$work/acl2/books" \
    -j 4 books/centaur/bitops/part-select
)
python3 -I tests/logic/acl2/export_bit_selection.py "$work/acl2" "$work/first.json"
python3 -I tests/logic/acl2/export_bit_selection.py "$work/acl2" "$work/second.json"
cmp "$work/first.json" "$work/second.json"
python3 -I tests/logic/acl2/check_bit_selection.py "$work/first.json"
python3 -I tests/logic/acl2/test_bit_selection.py
lake build --wfail +Silmaril.Logic.ACL2.Standard.BitSelection.Tests
```

The Lean target checks native observations and two off-guard counterexamples
with kernel reduction. It audits transitive axioms of the public definitions,
source lowering and theorems against `propext`, `Classical.choice` and
`Quot.sound`. The Python suite exercises changed call packages, arities,
formal references, power base, inclusive width, and native sample output.
