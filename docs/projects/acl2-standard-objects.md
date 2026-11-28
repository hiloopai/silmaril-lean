# Standard ACL2 8.7 logical objects (C2)

Import `Silmaril.Logic.ACL2.Standard.Objects.Thms` for `Object`, `objectPrimitives` and
`objectModel`. The existing single-sort `Term` and `Signature` supply the finite contexts and
arity-checked calls. `objectModel` takes the denotation of each declared call from its caller.
The `Objects.CdrSize` module separately supplies `objectCdrSize` for the recursive certificate
interface using the stock `acl2-count`. [Core interpretation](../../Silmaril/Logic/ACL2/Defs.lean) ·
[Recursive certificate](../../Silmaril/Logic/ACL2/Recursive/Certificate.lean)

## Symbol identity and construction

Pass the resolved, case-sensitive home-package `Name` to `Symbol.ofName?`, then wrap its result
in `Object.symbol`. The constructor checks that the package is nonempty and that both strings
contain only character codes below 256. `Symbol.toName` returns the same `Name` on success and
is injective. Package environments determine whether an identity occurs in their world. In
stock ACL2, a written `ACL2::CAR` has home identity `COMMON-LISP::CAR` because of imports.
The `COMMON-LISP` names `NIL` and `T` are the distinguished symbol values. Only `NIL` is false
in `if`. [ACL2 package and symbol rules](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L5665-L5854)

`Character` is `Fin 256` and `ByteString` is a list of those codes. `ByteString.ofString?`
converts by Unicode scalar value with a range check. Lean's UTF-8 encoding is irrelevant to ACL2
character counts. `Object.ofList` constructs a proper list, and `Object.cons` accepts any cdr.
`Rat` gives reduced exact rationals with a positive denominator. `Object.ofParts` collapses zero
imaginary parts to rationals, and the `complexRational` constructor requires a nonzero imaginary
part. `Object.equal` returns `T` exactly when the objects are equal. [ACL2 complex-number rules](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L4386-L4448) ·
[ACL2 character codes](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L9139-L9161)

## Primitive behavior

| Operations | Logical equations exercised |
| --- | --- |
| `cons`, `car`, `cdr`, `consp`, `equal`, `if` | Both projections return NIL on atoms. Structural equality returns a distinguished Boolean symbol. Any non-NIL object selects the then branch. |
| `true-listp`, `binary-append`, `true-list-fix` | Proper lists end in NIL. Append retains the first argument's cons spine and replaces its atomic tail with the second argument. Appending NIL gives `true-list-fix`. |
| `symbol-name`, `symbol-package-name` | Either projection of a nonsymbol yields the empty string. |
| `char-code`, `code-char`, `coerce` | Noncharacters have code zero. Noninteger and out-of-range inputs to `code-char` yield the null character. `coerce` to the symbol `COMMON-LISP::LIST` yields NIL for a nonstring. Other targets produce a string after replacing noncharacters in the cons spine with null characters and discarding the atomic tail. |
| `binary-+`, `binary-*`, unary `-` and `/`, `<` | Nonnumbers contribute zero. Unary division returns zero on zero. `<` uses lexicographic real/imaginary comparison, including for complex inputs. |
| `complex`, `realpart`, `imagpart`, `numerator`, `denominator` | Each nonrational input to `complex` contributes zero. Both components of a nonnumber are zero. Numerator and denominator of a nonrational are zero and one respectively. |
| Recognizers, `fix`, `ifix`, `nfix`, `zp`, `acl2-count` | The definitions use one object sort. Lean-level recognizers return `Bool`; `Object.ofBool` gives their ACL2 result. `zp` yields NIL exactly on positive integers. `Object.natRank_decrement_lt` proves that `(+ x -1)` decreases the `nfix` rank on that branch. `Object.acl2Count_cdr_lt` proves the cons cdr decrease. |

The authority is ACL2 8.7 commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`. [Source tree](https://github.com/acl2/acl2/tree/bc6f4f49e81a0711214a8d91f0d06e0e084d2204) ·
[Arithmetic, projection and conversion completion](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L25290-L25691) ·
[Symbol completion](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L16819-L16843) ·
[`zp`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L3798-L3804) ·
[`acl2-count`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L2355-L2381) ·
[`binary-append`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L3315-L3335)

## Reproduce

```sh
lake build --wfail +Silmaril.Logic.ACL2.Standard.Objects.Tests
make check CHECK_TARGETS=+Silmaril.Logic.ACL2.Standard.Objects.Tests

acl2_source=$(mktemp -d)/acl2
git clone --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$acl2_source"
test "$(git -C "$acl2_source" rev-parse HEAD)" = bc6f4f49e81a0711214a8d91f0d06e0e084d2204
make -C "$acl2_source" LISP=sbcl
python3 -I tests/logic/acl2/check-standard-objects.py "$acl2_source"
```

The Lean regression checks concrete equations, an arity-checked core application, the `if`
truth convention and the cdr measure. Its axiom audit checks declarations from the three public
modules and their transitive proof dependencies against `propext`, `Classical.choice` and
`Quot.sound`. The separate native sample compares 33 labeled observations. It uses
`:set-guard-checking :none` to evaluate logical completion cases in stock ACL2. Lean receives
resolved package identities for the sample. [Guard checking manual](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____SET-GUARD-CHECKING) ·
[Native sample and runner](../../tests/logic/acl2/)

This profile covers pure object operations. Package resolution and interning, new translated
term syntax, ACL2(r), runtime state, event admission, and general native correspondence remain
outside this deliverable. Additional arithmetic such as floor, remainder and bit operations
also remains outside the profile.
