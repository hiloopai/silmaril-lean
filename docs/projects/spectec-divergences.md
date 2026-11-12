# SpecTec: our patches and divergences

This page lists every place where our Lean development of SpecTec departs from
the upstream sources: the patches we apply to the printed IL of the WebAssembly
specification and of the SpecTec IL meta-theory, our patches to SpecTec's
work-in-progress Lean 4 backend, and the places where our reading of the IL
differs from SpecTec's own tools. For each one we say what we changed, why, and
what upstream looks like now.

The reasons are our understanding of the specification. We may be mistaken
about any of them, and an item listed as "present" may be intended upstream, or
already addressed in a way we have not recognised. Corrections are welcome.

The numbers in the first column are local identifiers of our patches (the
`spectec_erratum` numbers in the Lean sources). They are not upstream issue
numbers. The Lean sources use the same numbers, and a few more for findings
that are not patched (for example `#803`, the signed LEB128 narrowing below, and
`#881`, built-in functions declared without clauses).

## Versions

| What | Revision |
| --- | --- |
| Base of the patches and of all results | `WebAssembly/spec@608711107b7f1edb13efd57b7d79b49477462d36` (2026-09-22) |
| Later snapshot, compared below as "snapshot" | `WebAssembly/spec@e7a9df7cdd351df9d8d8546a53248669d51c1aa8` (2026-11-03) |
| Upstream main, compared below as "main" | `WebAssembly/spec@943c5df07e84f11d2b83078964df5812530afbd2` (2026-11-10), sources read only |
| SpecTec IL meta-theory | `Wasm-DSL/spectec@3a10283c5b56989689ca4d36a6cc559e3783246f` (head of `meta-theory`); compared with `main@acc6e834ff` and `rocq-backend@68feb11fa0` |
| Lean 4 backend | `Wasm-DSL/spectec` `lean4-wip@16b70bde87` (printer), `rocq-backend@d3e64d0a4a` (frontend and middle end) |

For the specification, "snapshot" was checked mechanically: the patch status
rows are computed by `tools/spectec-gen errata-status` from the printed
streams. "main" was checked by reading the `.spectec` sources only; the three
specification commits after the snapshot (`c4a1a336c`, `859d3232a`,
`f3268fa9d`) do not touch any definition below, so every row has the same
status at both. Status words: **fixed** (upstream now has an equivalent
correction; the commit is given), **present** (the upstream definition is
unchanged in the respects that matter), **changed** (upstream changed the
definition differently; see the note).

## Patches to the Wasm 3.0 specification

| # | Definition | What we changed | Why (as we understand it) | Upstream |
| --- | --- | --- | --- | --- |
| 654 | `Bi32`, `Bi64` (`5.1-binary.values`) | `BuN(N)` → `BiN(N)` | The prose says uninterpreted integers are encoded as signed LEB128; `BiN` is defined and otherwise unused. With `BuN`, `41 7F` reads as `i32.const 127`. | fixed in `b0ec1f3f4` (2026-10-22), identical |
| 655 | `$cont` | `0x80 < b` → `0x80 <= b` | UTF-8 continuation bytes are `0x80`–`0xBF`. | fixed in `b0ec1f3f4`, identical |
| 656 | `$utf8` | upper bound `U+11000` → `U+110000` | The largest scalar value is `U+10FFFF`. | fixed in `7e9fb78c6` (WebAssembly/spec#2274); the function was also split (`acebe270b`) |
| 661 | `Tstringchar` | `\u{n}` escape: `0xE800 <= n` → `0xE000 <= n` | Surrogates end at `U+DFFF`; `Tchar` uses `U+E000`. | fixed in `2b34c7311` (WebAssembly/spec#2295), identical |
| 662 | `Tfloat`, `Thexfloat` | add the forms without an exponent (`p:Tmant`, `"0x" p:Thexmant`) | As written, the exponent is mandatory, so `1.5` or `0x1.8` is not a float literal; the 1.0 and 2.0 grammars have these forms. | present |
| 663 | `Talign_` | default alignment `N` → `n` with `N = 2^n` | Callers pass a byte count, while validation reads the field as an exponent. | fixed in `0148af713` (WebAssembly/spec#2314), same shape |
| 664 | `Ttypeuse_` | `SUB FINAL (FUNC …)` → `SUB FINAL? tu* (FUNC …)` | As written, an explicit `(type x)` cannot name a non-final function type or one with supertypes. | present |
| 665 | `Tblockcomment`, `Tblockchar` | allow runs of `;` before `;)` and around nested comments | As written, no comment body can end in `;`, so `(;a;;)` and `(;;)` are not comments; the test suite has such comments. | present |
| 692 | `Texporttabledots_` | the inline element list is a list of expressions or a list of function indices | As written, `(elem $f)` has no derivation. The bare folded-instruction form is still not derivable after the patch. | present |
| 694 | `Treserved` | `,` `;` `[` `]` `{` `}` become single-character reserved tokens | By longest match, `func;;bla` is then one reserved token, so a line comment directly after a keyword is not one (the test suite has such cases); the reference lexer treats these characters singly. | present |

## Patches to the Wasm 1.0 and 2.0 specifications

| # | Spec | Definition | What we changed | Why (as we understand it) | Upstream |
| --- | --- | --- | --- | --- | --- |
| 680 | 1.0 | `Module_ok` | bound `\|C.TABLES\|` and `\|C.MEMS\|` by 1, instead of the defined tables and memories only | Imported tables and memories also count towards the limit of one. | present (the rule was changed in `25134ead3`, the bounds were not) |
| 684 | 1.0 | `$utf8` | upper bound `U+11000` → `U+110000` | As 656. | fixed in `7e9fb78c6`, identical |
| 685 | 1.0 | `$utf8` | require `b < 0xC0` for every continuation byte | Without it `C2 C0` also encodes `U+00C0`, so `$utf8` is not a function. The lower bound `0x80` comes from the partial conversion in `b - 0x80`. | present |
| 686 | 1.0 | `Binstr` | `0xBB`: `CVTOP F32 F64 PROMOTE` → `CVTOP F64 F32 PROMOTE` | The first type of `CVTOP` is the result type elsewhere in this spec and in 3.0. | present |
| 687 | 1.0 | `Bmodule` | the version field `1:Bu32` → the bytes `0x01 0x00 0x00 0x00` | The version is a fixed four-byte word, not LEB128. | present |
| 688 | 1.0 | `Bfunc` | add `\|locals\| < 2^32` | The binary format bounds the total number of locals. | present |
| 690 | 1.0 | `Belem`, `Bdata` | the index byte `0x00` → `0:Bu32` | The field is a LEB128 index, so `80 00` is also allowed (the test suite uses it). | present |
| 670 | 2.0 | `Binstr` | the second `0xFD 92` (`ZERO 64`) → `0xFD 93` | `v128.load64_zero` is opcode 93. | present |
| 671 | 2.0 | `Belem` | element kind 6 reads a reference type | Kinds 5 and 7 read a `reftype` here, and so does the 3.0 grammar for kind 6. | present |
| 672 | 2.0 | `Bmodule` | as 687 | As 687. | present |
| 673 | 2.0 | `$dataidx_instrs` | look into `block`, `loop` and `if` bodies | A `memory.init` nested in a block is otherwise missed by the data count check. This relies on first-match clause order, as the definition already does. | present |

Our 2.0 variant does not carry the 2.0 counterparts of 680, 684, 685, 686 and
688. They are present upstream except 684, which `7e9fb78c6` fixed in 2.0 too.

## Patches to the SpecTec IL meta-theory

The meta-theory import is not part of the current public release (its source
tree has no licence file); this section documents it for reference.

| # | Definition | What we changed | Why (as we understand it) | Upstream |
| --- | --- | --- | --- | --- |
| 1 | `Step_exp` (`5-reduction`) | (a) the `BIN-ctx2`/`CMP-ctx2` conclusions reduce the right operand; (b) `CMP-EQ`/`CMP-NE` compare values only, and the missing unequal cases are added | (a) as written the right operand never steps; (b) the Rocq development's rules have this form | (a) present on every branch; (b) fixed on `main` and `rocq-backend` (`20aba52e2`, `44801dd58`, `8cb8dc91b`), not on `meta-theory` |
| 2 | `$numbin` (`3-primitives`) | `MOD` uses `mod`; `int` `DIV` converts the quotient; the zero guards convert the literal | `MOD` was defined as division; the guards elaborate to a conversion of a possibly negative value to `nat`. The `real` `DIV` guard has the same shape and is not patched. | source present on every branch; whether a newer frontend elaborates the guards differently is not checked |

## Patches to the Lean 4 backend

Our Wasm 3.0 Lean model is generated by SpecTec's work-in-progress Lean 4
printer (`lean4-wip`, unmerged), which we ported onto the newer `rocq-backend`
frontend and middle end. The model and the patch are not part of the current
public release (the printer's source tree has no licence file); this section
documents them for reference. Upstream has
not changed the `lean4-wip` printer since `16b70bde87`. A separate Lean backend
appeared on the branch `lean-backend-proof` (`spectec/src/backend-lean`, head
`1fc6de2ee`, 2026-11-11); we have not used or compared it, except where noted.

| # | What we changed | Why | Effect on meaning (as we understand it) |
| --- | --- | --- | --- |
| S | Spec edit (`spec-mech-aliases.patch`): `Inn`, `Vnn`, `Lnn` become aliases of `addrtype`, `vectype`, `lanetype` | Without it the middle end's type-family removal fails IL validation on our pin. `rocq-backend` carries the same edit (since `26d354ca7`), and it is the whole spec delta of `lean4-wip`. | None expected: at our pin the three types have exactly the same cases. Not in `WebAssembly/spec` (pin, snapshot, main). |
| 1 | Print the valid members of a mutually recursive group instead of dropping the whole group when one member is a hint | The well-formedness relations of every recursive type group were missing. | None. |
| 2 | Add a catch-all `\| _ => default` clause to partial functions | Lean requires total `def`s. | Changes meaning outside a function's domain: it returns a default value where SpecTec has none. A premise `$f(x) = y` can then hold where SpecTec's cannot, and through the negations of `otherwise` a rule can also lose a derivation. |
| 3 | Lean record update and projection syntax | The printer emitted Rocq syntax. | None. |
| 4 | Render `mod` (`\`) as `%` | No rendering existed. | On `Int`, Lean's `%` is Euclidean while SpecTec's is truncated, and `x % 0 = x` where SpecTec has no value. The uses in this file have non-negative operands on well-formed inputs. |
| 5 | Read a slice `e[i : n]` as start and length (`List.take n (List.drop i e)`) | The printer read the second argument as a stop index. | Total: out of range it gives a shorter list where SpecTec has no value. |
| 6 | Index a literal list with `List.getD` | Avoids an `Inhabited` requirement. | Only the out-of-range value differs. |
| 7 | Define the helpers the printer refers to (`list_update_func`, `list_slice_update`, `list_map3`, `option_zipWith`, `option_map3`) | They were missing. | Total versions: unequal lengths are truncated, mixed `some`/`none` gives `none`, where SpecTec has no value. |
| 8, 9 | Fix the tuple projection chain; use `Prod.fst`/`Prod.snd` | Component 0 was projected with `snd`. | Restores the intended meaning. |
| 10 | Ascribe literal lists of constructors | Elaboration only. | None. |
| 11 | Drop the well-formedness premises that the middle end attaches to function clauses | With them no guarded function could be rendered (`$iadd_` was `opaque`). | On ill-formed inputs a clause can fire, a result is not range-checked, and a guarded chain of clauses can pick a different clause. Relations keep their premises. |
| 12 | Render `int` as `Int` (with `Int.ofNat`/`Int.toNat`), and `rat`, `real` as `Int` | Every number was rendered as `Nat`, so `0 - x` truncated. | `Int.toNat` maps negative values to 0 where SpecTec has no value. Rationals as `Int` make `/` integer division before `$truncz` sees it, so the signed `$idiv_` and `$irem_` of this file are wrong for some negative operands whatever `truncz` is. The `lean-backend-proof` printer uses `Rat`/`Real`. |

Not one of our patches, but visible in the generated file: the middle end
rewrites an optional atom such as `NULL?` in a rule's conclusion to `some NULL`,
so `Reftype_ok`, `Fieldtype_ok` and `Globaltype_ok` only hold for the nullable or
mutable form. We have not investigated this further.

## Where our reading of the IL differs

| Reading | Ours | SpecTec | Upstream |
| --- | --- | --- | --- |
| List slices `e[i : n]` | defined when `i + n <= \|e\|` (`Value.slice?`) | `eval.ml` at our pin required `i + n < \|e\|`, so a slice ending at the end of the list was undefined; we keep that as `Broken.sliceEvalMl?` for comparison | fixed in `WebAssembly/spec` `f4f22691f` (2026-10-20), now the same as ours; `Wasm-DSL/spectec` `rocq-backend` still has `<` |
| `otherwise` premises | the rule applies when no earlier rule of the relation applies to the same left-hand side; the earlier rules' own relation premises are read without `otherwise` | the middle end's `Else` pass builds the same negation, and also omits earlier rules whose left-hand side cannot match | same for the relations we use (`Step_pure`, `Step_read`) |
| Optional atoms in conclusions (`NULL?`) | an extra reading (`DDerivesB`) lets such an atom be `none` or `some` | the evaluator does not reduce such an iteration, so the rule cannot conclude; as a pattern it matches both, as in our reading | unchanged |
| Built-in functions (`hint(builtin)`, `$ieee_`, `$s33_to_u32`, the relaxed choices) | supplied as parameters, or by our numeric primitives, stated in each theorem | defined by prose or by the interpreter | — |

## Observations we prove but do not patch

| Observation | Upstream |
| --- | --- |
| Signed LEB128 (`BsN`, all three versions): `2^7 * i` elaborates with a conversion of `i` to `nat`, so multi-byte encodings of negative numbers (for example `FF 7E`, −129) have no derivation. | present |
| `$sx` (3.0) has no clause for reference storage types. | fixed in `6057acdb1` (WebAssembly/spec#2306) |
| `$s33_to_u32` (3.0) has no clauses; we treat it as a built-in. | present (it appears to be meant as a built-in) |
| `$ieee_` (3.0 text) has no clauses (an upstream TODO); float literals therefore have no value without a built-in. | present |
| Disjoint export names (1.0, 2.0): a TODO in `Module_ok`. | addressed in `25134ead3` (WebAssembly/spec#2248) |
| 3.0 `$utf8`: its first clause also matches one-element lists, so first-match evaluation of a single character does not terminate. | changed in `acebe270b` (split into `$utf8single`) |
| Other TODOs we noted and did not patch: 2.0 `ref.func` references, 2.0 `VCVTOP` constraints, the type index of `Bexterntype` (1.0, 2.0). | present |

## How to reproduce

The vendored streams and sources are under `specs/spectec/` with their SHA-256
sums; `specs/spectec/README.md` gives the frontend build and command.

```sh
# the vendored sources and streams match their manifests
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- check-sources
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- check
# the status of every patch at the later snapshot
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- errata-status
# the patches apply, and the stated observations hold
lake build Silmaril.Wasm.SpecTec.Scripts.Thms Silmaril.Wasm.SpecTec.Broken.Thms \
  Silmaril.Wasm.SpecTec.Versions.Thms
```

Each patch is a `spectec_erratum` command in
`Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata/`, with the quoted
source line, the reason, and the exact text it replaces. The upstream commits
can be inspected with, for example,
`git -C <WebAssembly/spec clone> log 608711107b..943c5df07 -- specification/wasm-3.0`.
