# ACL2 8.7 logical PREFIXES projections

Import `Silmaril.Logic.ACL2.Standard.FixedWidth.Thms` for the fixed-width
projection laws and the source equations for the four unary logical functions
in package `X86ISA`. The equations hold for every standard ACL2 `Object`.
[Lean theorem header](../../Silmaril/Logic/ACL2/Standard/FixedWidth/Thms.lean) ·
[Pinned PREFIXES bitstruct](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/utils/structures.lisp#L85-L96)

| Translated ACL2 name | Logical body |
| --- | --- |
| `PREFIXES-FIX$INLINE` | `LOGHEAD$INLINE` at width 52 |
| `PREFIXES->ADR$INLINE` | fix, then select width 8 at offset 36 |
| `PREFIXES->NUM$INLINE` | fix, then select width 4 at offset 0 |
| `PREFIXES->NXT$INLINE` | fix, then select width 8 at offset 44 |

The reusable projection applies `LOGHEAD` at the container width and then
`PART-SELECT-WIDTH-LOW`. Using the existing ACL2 bit-selection proofs, Lean
proves that the result is an integer in the range from zero through
`2 ^ width - 1`. Nonintegers give zero. Negative and oversized integers
follow the same Euclidean quotient and remainder equations as in-range
inputs. For fields with `offset + width ≤ container`, Lean proves that the
field is unchanged by the fix. A kernel-checked counterexample exercises a
field crossing the container boundary.
[Bit-selection equations](acl2-bit-selection.md)

## Evidence and reproduction

The exporter includes the certified `projects/x86isa/utils/structures` book
with `X86ISA_EXEC=nil` at ACL2 8.7 commit
`bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`. It reads fully qualified names,
arities, formals, and `unnormalized-body` after ACL2's `remove-guard-holders`.
The checker compares the two shared translated callee rows against the
bit-selection pin. It checks the projection lambda's binding and lowers it
to a Lean `let`. ACL2's world projection, the pinned fixture, and the
Python lowering are the source trust boundary. Lean checks the resulting
equations and compares all four functions with 20 native observations
collected using `set-guard-checking :none`. Coverage includes signed and
oversized integers, field boundaries, and noninteger objects. This library
provides object-level equations. Step bindings and byte decoding are outside
its scope.
[Fixture](../../corpus/acl2/prefixes-projections/acl2-8.7.json) ·
[Generated Lean](../../Silmaril/Logic/ACL2/Standard/FixedWidth/Source.lean)

From the repository root, set `acl2_checkout` to the absolute path of a clean checkout of the
pinned ACL2 commit. Build `saved_acl2` with `make LISP=sbcl`, following the
[bit-selection setup](acl2-bit-selection.md#checks), then certify and export.

```sh
(
  cd "$acl2_checkout"
  export ACL2_CUSTOMIZATION=NONE X86ISA_EXEC=nil
  books/build/cert.pl --acl2 "$acl2_checkout/saved_acl2" --acl2-books "$acl2_checkout/books" \
    -j 4 books/projects/x86isa/utils/structures
)
work=$(mktemp -d)
python3 -I tests/logic/acl2/export_prefixes.py "$acl2_checkout" "$work/prefixes.json"
cmp "$work/prefixes.json" corpus/acl2/prefixes-projections/acl2-8.7.json
python3 -I tests/logic/acl2/check_prefixes.py "$work/prefixes.json"
python3 -I tests/logic/acl2/test_prefixes.py
lake build --wfail +Silmaril.Logic.ACL2.Standard.FixedWidth.Tests
```

The fixture SHA-256 is
`737cb12e2409b39cbab6fe0d755a37bf3bb5a597778c08affe5d529602188fda`.
The Python mutations cover package and arity, lambda scope, shared callee
body, fixer width, field width and offset, and an off-guard observation.
The Lean target audits the definitions and theorems against the permitted
`propext`, `Classical.choice` and `Quot.sound` axiom set.
