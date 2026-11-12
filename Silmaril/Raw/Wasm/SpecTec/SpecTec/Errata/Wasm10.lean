module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The wasm-1.0 errata

The verified errata of `#679`, as patches on
`Silmaril.SpecTec.Specs.wasm10`.  Each is a textual edit of one definition's
own `--ast` rendering, written out by `spectec_erratum`
(`Silmaril/SpecTec/Errata.lean`), so that a reader sees exactly what changed.
`Silmaril/SpecTec/Errata/Binary51.lean` is the worked example this file
follows; its preamble explains the two `import all` lines, which are what make
`applyErrata_wasm10errata` below a `rfl` the kernel can do.

`#679` has eleven sub-issues.  Seven of them become the eight patches here;
four get none.

| issue | upstream line | definition patched |
| --- | --- | --- |
| #680 | `6-typing.spectec:455-456` | `Module_ok` |
| #684 | `A-binary.spectec:55` | `utf8` |
| #685 | `A-binary.spectec:53-55` | `utf8` |
| #686 | `A-binary.spectec:382` | `Binstr` |
| #687 | `A-binary.spectec:527` | `Bmodule` |
| #688 | `A-binary.spectec:506` | `Bfunc` |
| #690 | `A-binary.spectec:492`, `:518` | `Belem`, `Bdata` |

Bare file names are in `specification/wasm-1.0/` at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`; `wasm-2.0/…` and `wasm-3.0/…` are
the sibling directories and `interpreter/…` is the reference interpreter, at
that same pin.  The 1.0 stream is `specs/spectec/wasm-1.0.ast`, 315 top-level
definitions, SHA-256
`8cdad0daf9b1f5a6380233c00dfa52b1fb3b639962dee1377dddb3c1b5b6f16f`, which
`specs/spectec/manifest.json` records.

## Seven issues, eight patches

`#690` is one defect reported once and spelled twice in the source — `Belem`
at `A-binary.spectec:492` and `Bdata` at `:518` — and an `IL.Erratum` carries
exactly one corrected definition, so it becomes two patches with the same
`issue` number, told apart by the `as` clause of `spectec_erratum`.

`#684` and `#685` are the converse: two issues against *one* definition,
`$utf8`.  Since an `IL.Erratum` replaces a whole definition, the two cannot
both be spliced into the pinned script — the second would undo the first — so
`erratum685` below carries both corrections and `erratum684` carries only its
own.  Both are kept, in that order, because
`IL.replaceDefs` is absorbing on a fixed target: patching with `#684` and then
with `#685` is patching with `#685`, which is what
`applyErrata_utf8_absorbing` records.  That absorption is a fact about
`applyErrata` and says nothing about the two corrections agreeing; what says
`#685` really carries `#684`'s bound is
`erratum685_carries_erratum684_bound`, which reads the corrected definition.
`erratum684` is therefore the one-token edit a reader can check at a glance,
and `erratum685` is the one that ends up in `wasm10corrected`.

## Four sub-issues get no patch

**#683 is not a SpecTec erratum at all.**  It is a gap on our side: SpecTec
1.0 has an embedder entry point `$invoke` (`9-module.spectec:169-172`,
`def $invoke(s, fa, val^n) = s; f; val^n (CALL_ADDR fa)` with
`-- if f = { MODULE {} }` and an arity premise) and `Silmaril/Wasm/V1/Execution`
has no counterpart, so there is nothing to correct in the pinned stream and
the fix belongs in `Silmaril/Wasm/V1/Execution/Instantiation.lean`.

**#681, `6-typing.spectec:457` `;; -- TODO: disjoint export names`.**  The
premise wanted is `wasm-3.0/2.4-validation.modules.spectec:161`'s
`-- if $disjoint_(name, nm*)`, and `$disjoint_` is itself a recursive function
(`wasm-3.0/0.3-aux.seq.spectec:35-37`).  wasm-1.0's `0-aux.spectec` declares
`$min`, `$sum`, `$opt_`, `$list_` and `$concat_` and no `$disjoint_`; and its
`Export_ok` (`6-typing.spectec:414-416`) is `C |- EXPORT name externidx : xt`,
which unlike 3.0's `C |- export : nm xt_E` does not carry the name out, so
`Module_ok` would first have to destructure `export*` to reach `name*`.
Adding those clauses to the pinned 1.0 sources and re-running the frontend
confirms the shape of the fix: the stream gains one top-level definition,
`$disjoint_`, besides the edit to `Module_ok`.  `IL.Erratum` replaces a
definition and cannot add one — `applyErratum` demands
`countDefs e.target s = 1` — so this is not a patch this form can express.

**#682, `$instantiate` evaluates element and data offsets in the
imports-only init instance.**  `9-module.spectec:149-158` builds
`moduleinst_init` out of the imported globals alone, sets `z = s; f_init`, and
evaluates `expr_G`, `expr_E` and `expr_D` all under that `z`, while
`Module_ok` checks `Elem_ok` and `Data_ok` under the full `C`
(`6-typing.spectec:450-451`, `:459`), whose `GLOBALS` is `igt* gt*`.  So a
module that `Module_ok` accepts can have no `$instantiate` derivation at all:
`$global((s; f_init), 0)` is `s.GLOBALS[f_init.MODULE.GLOBALS[0]]`
(`5-runtime-aux.spectec:77`) and `f_init.MODULE.GLOBALS` is empty, so
`Step_read/global.get` (`8-reduction.spectec:222-223`) has no instance.

The issue offers two repairs and this file applies neither.  Restricting
`Elem_ok`/`Data_ok` to `C'` — what wasm-2.0 does — resolves the inconsistency
*against* the 2019 Recommendation and against `Silmaril/Wasm/V1`, which
evaluate offsets in the full, post-allocation instance.  The faithful repair
moves `$allocmodule` and `f` above the two offset premises and evaluates them
under a new `z' = s_1; f`; applying exactly that to the pinned sources and
re-running the frontend shows why it is not an erratum patch.  `--ast` prints
a clause as its binder list first and its premises last, and the repair
changes both: `s_1` and `moduleinst` move ahead of `i_E*` and `i_D*` in the
binders, and a binder for `z'` appears.  Every formulation has that property,
because the offset premises must mention a variable that today is first bound
below them.  The single contiguous edit is therefore 4175 of `$instantiate`'s
5395 printed characters — a rewrite, not an edit.  Upstream did not make
either repair: wasm-3.0 turns active offsets into instructions
(`$runelem_`, `$rundata_`, `wasm-3.0/4.4-execution.modules.spectec:148`,
`:153`) run after allocation, which is a redesign of
`wasm-3.0/4.4-execution.modules.spectec:183-209`.

**#689, `A-binary.spectec:123` `;; TODO: typeidx`.**  `Bexterntype` reads
`| 0x00 ft:Bfunctype => FUNC ft` where the format encodes a type index
(`interpreter/binary/decode.ml:306-308` reads `ExternFuncT (typeuse idx s)`,
and `idx` is `u32` at `:151`).  The grammar cannot simply read a `Btypeidx`:
`syntax externtype` (`1-syntax.spectec:131-132`) is
`FUNC functype | GLOBAL globaltype | …`, so the abstract syntax stores a
*resolved* function type and a SpecTec grammar has no module context to
resolve an index against.  Writing `| 0x00 x:Btypeidx => FUNC x` into the
pinned sources and re-running the frontend fails with
`cannot parse expression as functype`, as it must.  wasm-3.0 fixes it by
changing the abstract syntax so that `externtype` carries a `typeuse`, which
is what lets `wasm-3.0/5.2-binary.types.spectec:103` read
`| 0x00 x:Btypeidx => FUNC (_IDX x)`.  In wasm-1.0 that is an edit to
`syntax externtype` and then to `syntax import` (`1-syntax.spectec:286-287`)
and to every rule that matches `FUNC ft` — a redesign, not an erratum patch.
wasm-2.0 carries the same defect, and `Errata/Wasm20.lean` declines it on the
same grounds (`#678`).

## How each edit was checked

The `replacing`/`with` pairs below are not hand-written against the printed
form.  The official frontend was built at the pin and run over
`specification/wasm-1.0/` with the same `--ast-width 80` and the same file
order as `specs/spectec/manifest.json`; it reproduces
`specs/spectec/wasm-1.0.ast` byte for byte, so the comparison is sound.  Each
correction was then made in a copy of the `.spectec` sources, the frontend was
re-run, and the `replacing`/`with` pair was read off the two printed
definitions as the text between their common prefix and common suffix,
widened to the nearest token boundary and to uniqueness.  The combined run —
all seven source corrections at once — changes exactly the seven definitions
patched here and no others.

Every line number quoted in a `because` string was read out of the pinned file
with `sed -n 'Np'` before it was written down, and so was every
`interpreter/…` and `test/core/…` line.  The sub-issues of `#679` quote line
numbers from a scratch copy of the sources, and every one of them agrees with
the pin — including the two corrections `#682` folded in from its verifiers,
`5-runtime-aux.spectec:77` for `$global` and `6-typing.spectec:459` for `C`,
and the one `#689` folded in, `interpreter/binary/decode.ml:151` for `idx`.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL.Wasm10

set_option maxRecDepth 100000

/-! ## #680 — `Module_ok` bounds the *defined* tables and memories only

`6-typing.spectec:455-456` reads

```
  -- if |tt*| <= 1
  -- if |mt*| <= 1
```

`tt*` and `mt*` are bound by the `Table_ok` and `Mem_ok` premises (`:447-448`)
over the defined `table*` and `mem*`; the imported ones are the separate
`itt*` and `imt*` of `:465-466`, and `:459` puts both into the context as
`TABLES itt* tt*, MEMS imt* mt*`.  The constraint as written is therefore on
the defined tables and memories alone, where the 2019 Recommendation bounds
the whole index space, `|C.TABLES| <= 1` and `|C.MEMS| <= 1`.  So SpecTec 1.0
accepts `(module (import "" "" (table 10 funcref)) (table 10 funcref))`, which
the 1.0 Recommendation, the 1.0 reference interpreter and the 1.0-era test
suite all reject as "multiple tables".  Those three are read at the `wg-1.0`
tag rather than at the pin — multiple tables are legal in 3.0, so the
assertion is gone from `test/core/imports.wast` here — and so are cited by
`#680` rather than by file and line below.  The same defect
survives into wasm-2.0 for memories (`wasm-2.0/6-typing.spectec:698`, the
identical `-- if |mt*| <= 1`).

The patch spells the bound `|C.TABLES| <= 1` rather than the issue's
`|itt* tt*| <= 1`.  They say the same thing — `:459` defines `C.TABLES` to be
`itt* tt*` — but the latter does not elaborate at this position: `itt` gets
its type from `:459` and `:465`, both below, and the frontend rejects
`-- if |itt* tt*| <= 1` at `6-typing.spectec:455` with "cannot infer type of
variable".  `C` is declared at `6-typing.spectec:10`, so `|C.TABLES|` does
elaborate, and it is also how the Recommendation words the condition. -/

spectec_erratum 680 in Specs.wasm10 on "Module_ok"
  because "6-typing.spectec:455-456 read `-- if |tt*| <= 1` and `-- if |mt*| <= 1`, over the "
          "tables and memories the module defines (:447-448); the bound is on the whole index "
          "space, `|C.TABLES| <= 1` and `|C.MEMS| <= 1`, imports (:465-466) included"
  replacing "(if (cmp le nat (len (iter (var \"tt\") list (dom \"tt\" (var \"tt*\")))) (num (nat 1)"
            "))) (if (cmp le nat (len (iter (var \"mt\") list (dom \"mt\" (var \"mt*\")))) (num (na"
            "t 1))))"
  with      "(if (cmp le nat (len (dot (var \"C\") \"TABLES\")) (num (nat 1)))) (if (cmp le nat (le"
            "n (dot (var \"C\") \"MEMS\")) (num (nat 1))))"

/-! ## #684 — the four-byte UTF-8 range ends at U+11000

`A-binary.spectec:55` reads

```
def $utf8(ch) = b_1 b_2 b_3 b_4  -- if (U+10000 <= ch < U+11000) /\ ch = …
```

The bound is missing a hex digit: it should be `U+110000`, which is what the
1.0 Recommendation, the reference interpreter
(`interpreter/binary/utf8.ml:19`, `:27`, where the only upper bound is
`0x110000`) and the test suite all use.  Read literally, every scalar value
from U+11000 to U+10FFFF — 93.9% of Unicode, all emoji among them — has no
encoding, so `Bname` (`A-binary.spectec:58-59`) cannot derive the four bytes
`f0 9f bf be` that `test/core/names.wast:212` exports and `:725` invokes.  This is the 1.0 spelling
of the wasm-3.0 defect `Errata/Binary51.lean` patches as `#656`, and wasm-2.0
has it too (`wasm-2.0/A-binary.spectec:57`).

`0x11000` is `69632` and `0x110000` is `1114112`; `69632` occurs once in the
printed `utf8`, in exactly that premise.

This erratum is subsumed by `erratum685`, which corrects the same definition;
see the preamble. -/

spectec_erratum 684 in Specs.wasm10 on "utf8"
  because "A-binary.spectec:55 reads `-- if (U+10000 <= ch < U+11000)` in the four-byte clause "
          "of $utf8; the bound is one hex digit short and should be U+110000, as "
          "interpreter/binary/utf8.ml:27 has it"
  replacing "(num (nat 69632))"
  with      "(num (nat 1114112))"

/-! ## #685 — `$utf8` puts no upper bound on continuation bytes

`A-binary.spectec:52-55` defines `$utf8` by four clauses, of which the
multi-byte three read

```
def $utf8(ch) = b_1 b_2  -- if U+0080 <= ch < U+0800 /\ ch = $(2^6*(b_1 - 0xC0) + (b_2 - 0x80))
```

and its three- and four-byte companions.  The only constraints on `b_2`, `b_3`
and `b_4` are that the subtractions `b_i - 0x80` be defined and that the
arithmetic identity hold; nothing says `b_i < 0xC0`.  The 1.0 Recommendation
ends the same definition with `where b_2, b_3, b_4 < 0xC0`, and wasm-3.0
restores it as `$cont` (`wasm-3.0/5.1-binary.values.spectec:48-49`,
`def $cont(b) = $(b - 0x80) -- if (0x80 < b < 0xC0)`).  Without it `$utf8` is
not even a function: U+00C0 maps both to `c3 80` and to `c2 c0`, because
`2^6*(0xC2 - 0xC0) + (0xC0 - 0x80) = 192`.  `Bname` therefore accepts the name
`02 c2 c0`, which `interpreter/binary/utf8.ml:25` rejects
(`if b land 0xc0 = 0x80 then … else raise Utf8`) and which
`test/core/utf8-import-field.wast:234-247` asserts malformed.  wasm-2.0 has
it too (`wasm-2.0/A-binary.spectec:55-57`).

The correction adds `b_2 < 0xC0`, `b_3 < 0xC0` and `b_4 < 0xC0` to the clauses
that bind them, as a conjunct of each clause's range condition; six new
premises over three of `$utf8`'s five clauses.  The fragment below is long for
that reason and not because much is replaced: the three edited clauses are
consecutive, so the one contiguous span that covers all six insertions also
carries the two clauses between them through unchanged.  It is 1829 of the
definition's 3223 printed characters, and the corrected definition is 3693.

The 1.0 way of writing this would be 3.0's — a `$cont` function, used in place
of each `b_i - 0x80` — and that is a definition the pinned script does not
declare, so it is not available here; the inline bound derives the same byte
strings.  The span also contains the `#684` bound, which is why this erratum
carries `(num (nat 1114112))` as well. -/

spectec_erratum 685 in Specs.wasm10 on "utf8"
  because "A-binary.spectec:53-55 constrain the continuation bytes of $utf8 only through "
          "`b_i - 0x80` being defined, dropping the Recommendation's `where b_2, b_3, b_4 < "
          "0xC0`; so `02 c2 c0` is a well-formed name, which interpreter/binary/utf8.ml:25 "
          "rejects.  Restores the bound, and with it A-binary.spectec:55's U+110000 (#684)"
  replacing "(cmp le nat (num (nat 128)) (proj (uncase (var \"ch\") \"%\") 0)) (cmp lt nat (proj (u"
            "ncase (var \"ch\") \"%\") 0) (num (nat 2048)))) (cmp eq bool (proj (uncase (var \"ch\""
            ") \"%\") 0) (bin add nat (bin mul nat (bin pow nat (num (nat 2)) (num (nat 6))) (cvt i"
            "nt nat (bin sub int (cvt nat int (proj (uncase (var \"b_1\") \"%\") 0)) (cvt nat int ("
            "num (nat 192)))))) (cvt int nat (bin sub int (cvt nat int (proj (uncase (var \"b_2\") "
            "\"%\") 0)) (cvt nat int (num (nat 128)))))))))) (clause (exp \"ch\" (var \"char\")) (e"
            "xp \"b_1\" (var \"byte\")) (exp \"b_2\" (var \"byte\")) (exp \"b_3\" (var \"byte\")) ("
            "exp (list (var \"ch\"))) (list (var \"b_1\") (var \"b_2\") (var \"b_3\")) (if (bin and"
            " bool (bin or bool (bin and bool (cmp le nat (num (nat 2048)) (proj (uncase (var \"ch"
            "\") \"%\") 0)) (cmp lt nat (proj (uncase (var \"ch\") \"%\") 0) (num (nat 55296)))) (b"
            "in and bool (cmp le nat (num (nat 57344)) (proj (uncase (var \"ch\") \"%\") 0)) (cmp l"
            "t nat (proj (uncase (var \"ch\") \"%\") 0) (num (nat 65536))))) (cmp eq bool (proj (un"
            "case (var \"ch\") \"%\") 0) (bin add nat (bin add nat (bin mul nat (bin pow nat (num ("
            "nat 2)) (num (nat 12))) (cvt int nat (bin sub int (cvt nat int (proj (uncase (var \"b_"
            "1\") \"%\") 0)) (cvt nat int (num (nat 224)))))) (bin mul nat (bin pow nat (num (nat 2"
            ")) (num (nat 6))) (cvt int nat (bin sub int (cvt nat int (proj (uncase (var \"b_2\") "
            "\"%\") 0)) (cvt nat int (num (nat 128))))))) (cvt int nat (bin sub int (cvt nat int (p"
            "roj (uncase (var \"b_3\") \"%\") 0)) (cvt nat int (num (nat 128)))))))))) (clause (exp"
            " \"ch\" (var \"char\")) (exp \"b_1\" (var \"byte\")) (exp \"b_2\" (var \"byte\")) (exp"
            " \"b_3\" (var \"byte\")) (exp \"b_4\" (var \"byte\")) (exp (list (var \"ch\"))) (list "
            "(var \"b_1\") (var \"b_2\") (var \"b_3\") (var \"b_4\")) (if (bin and bool (bin and bo"
            "ol (cmp le nat (num (nat 65536)) (proj (uncase (var \"ch\") \"%\") 0)) (cmp lt nat (pr"
            "oj (uncase (var \"ch\") \"%\") 0) (num (nat 69632))))"
  with      "(bin and bool (cmp le nat (num (nat 128)) (proj (uncase (var \"ch\") \"%\") 0)) (cmp l"
            "t nat (proj (uncase (var \"ch\") \"%\") 0) (num (nat 2048)))) (cmp lt nat (proj (uncas"
            "e (var \"b_2\") \"%\") 0) (num (nat 192)))) (cmp eq bool (proj (uncase (var \"ch\") \""
            "%\") 0) (bin add nat (bin mul nat (bin pow nat (num (nat 2)) (num (nat 6))) (cvt int n"
            "at (bin sub int (cvt nat int (proj (uncase (var \"b_1\") \"%\") 0)) (cvt nat int (num "
            "(nat 192)))))) (cvt int nat (bin sub int (cvt nat int (proj (uncase (var \"b_2\") \"%"
            "\") 0)) (cvt nat int (num (nat 128)))))))))) (clause (exp \"ch\" (var \"char\")) (exp "
            "\"b_1\" (var \"byte\")) (exp \"b_2\" (var \"byte\")) (exp \"b_3\" (var \"byte\")) (exp"
            " (list (var \"ch\"))) (list (var \"b_1\") (var \"b_2\") (var \"b_3\")) (if (bin and bo"
            "ol (bin and bool (bin and bool (bin or bool (bin and bool (cmp le nat (num (nat 2048))"
            " (proj (uncase (var \"ch\") \"%\") 0)) (cmp lt nat (proj (uncase (var \"ch\") \"%\") 0"
            ") (num (nat 55296)))) (bin and bool (cmp le nat (num (nat 57344)) (proj (uncase (var "
            "\"ch\") \"%\") 0)) (cmp lt nat (proj (uncase (var \"ch\") \"%\") 0) (num (nat 65536)))"
            ")) (cmp lt nat (proj (uncase (var \"b_2\") \"%\") 0) (num (nat 192)))) (cmp lt nat (pr"
            "oj (uncase (var \"b_3\") \"%\") 0) (num (nat 192)))) (cmp eq bool (proj (uncase (var "
            "\"ch\") \"%\") 0) (bin add nat (bin add nat (bin mul nat (bin pow nat (num (nat 2)) (n"
            "um (nat 12))) (cvt int nat (bin sub int (cvt nat int (proj (uncase (var \"b_1\") \"%\""
            ") 0)) (cvt nat int (num (nat 224)))))) (bin mul nat (bin pow nat (num (nat 2)) (num (n"
            "at 6))) (cvt int nat (bin sub int (cvt nat int (proj (uncase (var \"b_2\") \"%\") 0)) "
            "(cvt nat int (num (nat 128))))))) (cvt int nat (bin sub int (cvt nat int (proj (uncase"
            " (var \"b_3\") \"%\") 0)) (cvt nat int (num (nat 128)))))))))) (clause (exp \"ch\" (va"
            "r \"char\")) (exp \"b_1\" (var \"byte\")) (exp \"b_2\" (var \"byte\")) (exp \"b_3\" (v"
            "ar \"byte\")) (exp \"b_4\" (var \"byte\")) (exp (list (var \"ch\"))) (list (var \"b_1"
            "\") (var \"b_2\") (var \"b_3\") (var \"b_4\")) (if (bin and bool (bin and bool (bin an"
            "d bool (bin and bool (bin and bool (cmp le nat (num (nat 65536)) (proj (uncase (var \""
            "ch\") \"%\") 0)) (cmp lt nat (proj (uncase (var \"ch\") \"%\") 0) (num (nat 1114112)))"
            ") (cmp lt nat (proj (uncase (var \"b_2\") \"%\") 0) (num (nat 192)))) (cmp lt nat (pro"
            "j (uncase (var \"b_3\") \"%\") 0) (num (nat 192)))) (cmp lt nat (proj (uncase (var \"b"
            "_4\") \"%\") 0) (num (nat 192))))"

/-! ## #686 — opcode `0xBB` decodes to an `f32.promote_f64`

`A-binary.spectec:382` reads

```
  | 0xBB => CVTOP F32 F64 PROMOTE
```

`Instr_ok/cvtop-convert` (`6-typing.spectec:242-243`) is
`C |- CVTOP nt_1 nt_2 cvtop : nt_2 -> nt_1`, so the first argument is the
*result* type and the second the operand: this says `[f64] -> [f32]`, an
"f32.promote_f64" that does not exist.  Every other `cvtop` line obeys the
convention, `:377` `0xB6 => CVTOP F32 F64 DEMOTE` among them.  The reading is
also stuck: `Step_pure/cvtop-val` (`8-reduction.spectec:199-201`) would need
`$cvtop__(F64, F32, PROMOTE, fN)` and the only equation is
`3-numerics.spectec:239`, `def $cvtop__(F32, F64, PROMOTE, fN) = …`.
`interpreter/binary/decode.ml:588` maps `0xbb` to `f64_promote_f32`, which
`interpreter/syntax/mnemonics.ml:341` defines as `Convert (F64
F64Op.PromoteF32)`.  wasm-2.0 has it too (`wasm-2.0/A-binary.spectec:427`).

`Binstr` is one 18709-character grammar; the fragment is anchored on the
production's own opcode, which occurs once. -/

spectec_erratum 686 in Specs.wasm10 on "Binstr"
  because "A-binary.spectec:382 reads `| 0xBB => CVTOP F32 F64 PROMOTE`; by the argument order "
          "of 6-typing.spectec:243 that is `[f64] -> [f32]` and it has no $cvtop__ equation "
          "(3-numerics.spectec:239).  It should be `CVTOP F64 F32 PROMOTE`, the f64.promote_f32 "
          "of interpreter/binary/decode.ml:588"
  replacing "(prod (num 0xBB) (case \"CVTOP\" (tup (case \"F32\" (tup)) (case \"F64\" (tup))"
  with      "(prod (num 0xBB) (case \"CVTOP\" (tup (case \"F64\" (tup)) (case \"F32\" (tup))"

/-! ## #687 — the module version is a LEB128 numeral, not four bytes

`A-binary.spectec:526-527` reads

```
grammar Bmodule : module =
  | 0x00 0x61 0x73 0x6D 1:Bu32
```

`Bu32` is `BuN(32)` (`:37`, `:20-22`), the LEB128 grammar, so `1:Bu32` derives
the single byte `0x01` — or one of its non-minimal spellings — where every
`.wasm` file has the four bytes `0x01 0x00 0x00 0x00`.
`interpreter/binary/decode.ml:1262-1266` reads both the magic and the version
with `word32` (`:75`), four raw little-endian bytes, against
`Encode.version = 1l` (`interpreter/binary/encode.ml:3`), and
`wasm-3.0/5.4-binary.modules.spectec:173-174` splits the header into
`grammar Bmagic : () = 0x00 0x61 0x73 0x6D => ()` and
`grammar Bversion : () = 0x01 0x00 0x00 0x00 => ()` precisely to say this.  As
written SpecTec 1.0 calls the five bytes `00 61 73 6D 01` a complete module,
which `test/core/binary.wast:38` asserts malformed for "unexpected end", and
has no derivation for the canonical empty module.

The patch form edits one definition, so the four bytes go inline into
`Bmodule` rather than into a new `Bversion` grammar; the derived byte strings
are the same.  `1:Bu32` binds nothing, so the production's parameter list is
unchanged.  The fragment is the only `Bu32` in `Bmodule`.  wasm-2.0 has the
same defect (`wasm-2.0/A-binary.spectec:924`) and `Errata/Wasm20.lean` patches
it the same way as `#672`. -/

spectec_erratum 687 in Specs.wasm10 on "Bmodule"
  because "A-binary.spectec:527 writes the module version as `1:Bu32`; `Bu32` is `BuN(32)` "
          "(:37, :20-22), a LEB128 numeral, so this derives the single byte 0x01 where the "
          "format has the four bytes 0x01 0x00 0x00 0x00 that "
          "interpreter/binary/decode.ml:1265-1266 requires"
  replacing "(seq (attr (case \"%\" (tup (num (nat 1)))) (var \"Bu32\")))"
  with      "(seq (num 0x01)) (seq (num 0x00)) (seq (num 0x00)) (seq (num 0x00))"

/-! ## #688 — `Bfunc` drops the bound on the total number of locals

`A-binary.spectec:505-506` reads

```
grammar Bfunc : code =
  | local**:Blist(Blocals) expr:Bexpr => ($concat_(local, local**), expr)
```

with no side condition, while `Blocals` (`:502-503`) is
`| n:Bu32 t:Bvaltype => (LOCAL t)^n` and `n` may be up to `2^32-1`.  The
Recommendation bounds the *concatenation*, `|concat((t*)*)| < 2^32`, and
`interpreter/binary/decode.ml:346-351` enforces it at decode time with
`require (I64.lt_u (List.fold_left I64.add 0L ns) 0x1_0000_0000L) s pos "too
many locals"` — `test/core/binary.wast:158-173` is that assertion.  The bound
is not implied by anything else in the production: `Blist` bounds the number
of *runs*, not the expanded total.  wasm-2.0 omits
it too (`wasm-2.0/A-binary.spectec:889-890`).

The edit appends `-- if $(|$concat_(local, local**)| < 2^32)` to the
production, which `--ast` prints as one more `(if …)` at the end of the
`prod`; the fragment is the production's trailing result expression. -/

spectec_erratum 688 in Specs.wasm10 on "Bfunc"
  because "A-binary.spectec:506 carries no side condition, so a code section whose Blocals runs "
          "(:502-503) sum to 2^32 or more is well formed; the Recommendation bounds the "
          "concatenation by 2^32, which interpreter/binary/decode.ml:350-351 reports as `too "
          "many locals`"
  replacing "(var \"expr\"))))"
  with      "(var \"expr\")) (if (cmp lt nat (len (call \"concat_\" (typ (var \"local\")) (exp (ite"
            "r (iter (var \"local\") list (dom \"local\" (var \"local*\"))) list (dom \"local*\" (v"
            "ar \"local**\")))))) (bin pow nat (num (nat 2)) (num (nat 32)))))))"

/-! ## #690 — `Belem` and `Bdata` begin with a byte where 1.0 has an index

`A-binary.spectec:491-492` and `:517-518` read

```
grammar Belem : elem =
  | 0x00 e:Bexpr x*:Blist(Bfuncidx) => ELEM e x*

grammar Bdata : data =
  | 0x00 e:Bexpr b*:Blist(Bbyte) => DATA e b*
```

`0x00` there is a byte terminal — `A-binary.spectec:18` is
`grammar Bbyte : byte = 0x00 | … | 0xFF`, and this file writes LEB128 fields
as `v:BuN` throughout — whereas the Recommendation has `x:tableidx` and
`x:memidx`, that is a `u32`.  A `u32` admits non-minimal spellings up to the
width bound, so the two-byte `80 00` is a legal table index 0:
`test/core/binary-leb128.wast:1029-1037` is a positive module that spells the
element segment's field that way, and `:24-31` does the same for a data
segment.  SpecTec 1.0 calls both malformed.  wasm-2.0 writes the field `0:Bu32`
(`wasm-2.0/A-binary.spectec:861`, `:902`), which is a `Bu32` whose value is 0,
and keeps a genuine byte terminal next to it in `Belemkind`, so the two
notations are deliberately distinguished upstream.

The patch writes `0:Bu32`, not the Recommendation's `x:Btableidx`/`x:Bmemidx`,
because wasm-1.0's `syntax elem` and `syntax data` (`1-syntax.spectec:275-278`)
are `ELEM expr funcidx*` and `DATA expr byte*` with no index field to store it
in; `0:Bu32` is the strongest statement the abstract syntax can carry, and it
is what the index must be anyway, 1.0 having at most one table and one memory.
Two patches, one issue: the two grammars are independent definitions. -/

spectec_erratum 690 in Specs.wasm10 on "Belem"
  because "A-binary.spectec:492 begins the production with the byte terminal `0x00` "
          "(A-binary.spectec:18) where Wasm 1.0 has a LEB128 tableidx, so the legal non-minimal "
          "index `80 00` is rejected; wasm-2.0/A-binary.spectec:861 writes `0:Bu32`"
  replacing "(seq (seq (num 0x00)) (seq (attr (var \"e\")"
  with      "(seq (seq (attr (case \"%\" (tup (num (nat 0)))) (var \"Bu32\"))) (seq (attr (var \"e"
            "\")"
  as erratum690Belem

spectec_erratum 690 in Specs.wasm10 on "Bdata"
  because "A-binary.spectec:518 begins the production with the byte terminal `0x00` "
          "(A-binary.spectec:18) where Wasm 1.0 has a LEB128 memidx, so the legal non-minimal "
          "index `80 00` is rejected; wasm-2.0/A-binary.spectec:902 writes `0:Bu32`"
  replacing "(seq (seq (num 0x00)) (seq (attr (var \"e\")"
  with      "(seq (seq (attr (case \"%\" (tup (num (nat 0)))) (var \"Bu32\"))) (seq (attr (var \"e"
            "\")"
  as erratum690Bdata

/-! ## The corrected script

`noncomputable` for the reason `Binary51.lean` gives: building the closed term
for a list of reflected `IL.Def`s this large makes Lean v4.35's LCNF boxing
pass panic.  Nothing here is run; the kernel *reduces* these values when it
checks `applyErrata_wasm10errata`, which `noncomputable` does not affect. -/

/-- The seven errata of `#679` that are expressible as AST
patches, in issue order, as the eight patches they spell out.  Only the order
of `erratum684` before `erratum685` matters: the other targets are pairwise
distinct, so `IL.applyErratum_comm` lets any two adjacent entries among them
be swapped. -/
noncomputable def wasm10errata : List Erratum :=
  [wasm10.erratum680, wasm10.erratum684, wasm10.erratum685, wasm10.erratum686,
    wasm10.erratum687, wasm10.erratum688, wasm10.erratum690Belem, wasm10.erratum690Bdata]

/-- `Specs.wasm10` with `#680`, `#684`, `#685`, `#686`, `#687`, `#688` and
`#690` applied: the corrected wasm-1.0 specification.  Written out as the
chain of `IL.replaceDefs` that `applyErrata wasm10errata` reduces to, which
`applyErrata_wasm10errata` certifies. -/
noncomputable def wasm10corrected : Script :=
  replaceDefs wasm10.erratum690Bdata.corrected
    (replaceDefs wasm10.erratum690Belem.corrected
      (replaceDefs wasm10.erratum688.corrected
        (replaceDefs wasm10.erratum687.corrected
          (replaceDefs wasm10.erratum686.corrected
            (replaceDefs wasm10.erratum685.corrected
              (replaceDefs wasm10.erratum684.corrected
                (replaceDefs wasm10.erratum680.corrected Specs.wasm10)))))))

/-- All eight patches apply, and `wasm10corrected` is their result.

This is the statement that carries the content: `IL.Erratum.applies` holds for
each patch in turn, which says that its target is declared exactly once in the
script it is applied to, that its corrected definition declares that target,
and — through `IL.defEq`, hence through `IL.defS` — that the corrected
definition really differs from the one it replaces.  "Exactly these seven
definitions change" is that last conjunct, eight times; "and nowhere else" is
`wasm10Patch_eq_self` below. -/
theorem applyErrata_wasm10errata :
    applyErrata wasm10errata Specs.wasm10 = some wasm10corrected := by
  rfl

/-! ## What changed, and what did not -/

/-- The eight patches, as the single function they apply to each top-level
definition of the pinned script. -/
noncomputable def wasm10Patch (d : Def) : Def :=
  replaceDef wasm10.erratum690Bdata.corrected
    (replaceDef wasm10.erratum690Belem.corrected
      (replaceDef wasm10.erratum688.corrected
        (replaceDef wasm10.erratum687.corrected
          (replaceDef wasm10.erratum686.corrected
            (replaceDef wasm10.erratum685.corrected
              (replaceDef wasm10.erratum684.corrected
                (replaceDef wasm10.erratum680.corrected d)))))))

/-- The corrected script is the pinned one with `wasm10Patch` mapped over it:
the patches act on each top-level definition independently and in place. -/
theorem wasm10corrected_eq_map : wasm10corrected = Specs.wasm10.map wasm10Patch := by
  simp [wasm10corrected, wasm10Patch, replaceDefs_eq_map, List.map_map, Function.comp_def]

/-- **Nowhere else.**  A definition that declares none of `Module_ok`, `utf8`,
`Binstr`, `Bmodule`, `Bfunc`, `Belem` and `Bdata` — in any of `free.ml`'s
namespaces, and at any depth inside a `recD` group — comes through all eight
patches untouched.  With `wasm10corrected_eq_map`, that is "the corrected
script differs from the pinned one only in those seven definitions". -/
theorem wasm10Patch_eq_self {d : Def} (h₁ : countDef "Module_ok" d = 0)
    (h₂ : countDef "utf8" d = 0) (h₃ : countDef "Binstr" d = 0)
    (h₄ : countDef "Bmodule" d = 0) (h₅ : countDef "Bfunc" d = 0)
    (h₆ : countDef "Belem" d = 0) (h₇ : countDef "Bdata" d = 0) : wasm10Patch d = d := by
  have e₁ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum680.corrected) (x := "Module_ok") rfl d h₁
  have e₂ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum684.corrected) (x := "utf8") rfl d h₂
  have e₃ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum685.corrected) (x := "utf8") rfl d h₂
  have e₄ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum686.corrected) (x := "Binstr") rfl d h₃
  have e₅ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum687.corrected) (x := "Bmodule") rfl d h₄
  have e₆ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum688.corrected) (x := "Bfunc") rfl d h₅
  have e₇ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum690Belem.corrected) (x := "Belem") rfl d h₆
  have e₈ := replaceDef_of_countDef_eq_zero
    (new := wasm10.erratum690Bdata.corrected) (x := "Bdata") rfl d h₇
  rw [wasm10Patch, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈]

/-- The corrected script has the same 315 top-level definitions as the pinned
one. -/
theorem length_wasm10corrected : wasm10corrected.length = Specs.wasm10.length := by
  simp [wasm10corrected]

/-- The corrected script declares exactly the identifiers the pinned one
declares, in exactly the same namespaces (`spectec/src/il/free.ml:205-212`). -/
theorem boundDefs_wasm10corrected : boundDefs wasm10corrected = boundDefs Specs.wasm10 := by
  rw [wasm10corrected, boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs,
    boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs,
    boundDefs_replaceDefs]

/-! ## The patches, read back off the `Erratum` values -/

/-- Seven issues, eight patches: `#690` is spelled twice in the source and
`#684` and `#685` share a target. -/
example : wasm10errata.map Erratum.issue = [680, 684, 685, 686, 687, 688, 690, 690] := by rfl

/-- The seven definitions these errata correct. -/
example : wasm10errata.map Erratum.target =
    ["Module_ok", "utf8", "utf8", "Binstr", "Bmodule", "Bfunc", "Belem", "Bdata"] := by
  rfl

/-- Each corrected definition declares its target: one relation, one function
twice over, and five grammars.  `utf8` and `Binstr` sit inside a `recD` group
in the pinned script, and `IL.replaceDefs` reaches into one. -/
example : wasm10errata.map (fun e => declKind? e.corrected) =
    [some (.rel, "Module_ok"), some (.dec, "utf8"), some (.dec, "utf8"),
      some (.gram, "Binstr"), some (.gram, "Bmodule"), some (.gram, "Bfunc"),
      some (.gram, "Belem"), some (.gram, "Bdata")] := by
  rfl

/-- Two patches with distinct targets commute, so the order in `wasm10errata`
is not load-bearing except between `#684` and `#685`. -/
example : applyErrata [wasm10.erratum687, wasm10.erratum686] Specs.wasm10 =
    applyErrata [wasm10.erratum686, wasm10.erratum687] Specs.wasm10 :=
  (applyErrata_pair_comm (by decide) Specs.wasm10).symm

/-! ## Two errata with the same target

`#684` and `#685` are the one place in this tree where two patches name the
same definition, and that composition is **last one wins**: `IL.replaceDefs`
keyed on `utf8` is absorbing, so whatever `erratum685.corrected` says is what
`wasm10corrected` contains, and `erratum684` contributes nothing to the result
but its entry in the audit trail.

Nothing in `Silmaril/SpecTec/Errata.lean` checks that the later erratum
*preserves* the earlier one, and `applyErrata_utf8_absorbing` below does not
either: it is a fact about `applyErrata` keyed on a target, true whatever
`erratum685.corrected` contains, and it stays `rfl` if `#685`'s `with` clause
is edited to put `U+11000` back.  The statement with content is
`erratum685_carries_erratum684_bound`, which looks *inside* the corrected
definition and says that `#684`'s `U+110000` is there and
`A-binary.spectec:55`'s `U+11000` is not.  The two have to be read together.
The hazard is general — two errata with the same target compose last-one-wins
and nothing checks that the later preserves the earlier — and
`docs/projects/spectec-divergences.md` records it. -/

mutual

/-- How often the S-expression `t` occurs as a subterm of an S-expression,
counting `t` itself.  Equality is `SExp`'s own `DecidableEq`, so this is
exact.  Nothing in `print.ml` corresponds to it; it exists to state what a
corrected definition *contains*, which `IL.Erratum` otherwise only records as
a textual diff. -/
def countSubSExp (t : SExp) : SExp → Nat
  | .atom v => if t == SExp.atom v then 1 else 0
  | .node g cs => (if t == SExp.node g cs then 1 else 0) + countSubSExps t cs

/-- `countSubSExp` summed over a list of S-expressions. -/
def countSubSExps (t : SExp) : List SExp → Nat
  | [] => 0
  | c :: cs => countSubSExp t c + countSubSExps t cs

end

/-- How often `t` occurs in the `--ast` rendering of a top-level definition. -/
def countSubDef (t : SExp) (d : Def) : Nat := countSubSExp t (defS d)

/-- `(num (nat 69632))`: `U+11000`, the bound `A-binary.spectec:55` writes and
`#684` corrects.  `IL.numS` prints `NumE (NatN n)` this way
(`Silmaril/SpecTec/IL/Print.lean`, from `print.ml:16-19`). -/
def natSExpU11000 : SExp := .node "num" [.node "nat" [.atom "69632"]]

/-- `(num (nat 1114112))`: `U+110000`, the bound `#684` puts in its place. -/
def natSExpU110000 : SExp := .node "num" [.node "nat" [.atom "1114112"]]

/-- **The defect `#684` reports, located.**  The pinned `utf8` — the one
definition of that name in `Specs.wasm10` — writes `U+11000` once and
`U+110000` nowhere. -/
theorem countSubDef_utf8_pinned :
    (namedDefs "utf8" Specs.wasm10).map (countSubDef natSExpU11000) = [1] ∧
      (namedDefs "utf8" Specs.wasm10).map (countSubDef natSExpU110000) = [0] := by
  constructor <;> rfl

/-- **`#684`'s own correction.**  Its corrected `utf8` has `U+110000` where
the pinned one had `U+11000`, and no occurrence of the old bound is left. -/
theorem countSubDef_erratum684 :
    countSubDef natSExpU11000 wasm10.erratum684.corrected = 0 ∧
      countSubDef natSExpU110000 wasm10.erratum684.corrected = 1 := by
  constructor <;> rfl

/-- **`#685`'s corrected `utf8` carries `#684`'s bound.**  This is the content
`applyErrata_utf8_absorbing` does not state: the definition that actually ends
up in `wasm10corrected` has `U+110000` exactly once and `U+11000` not at all,
so composing the two errata last-one-wins does not lose `#684`.  Replace
`1114112` by `69632` in `#685`'s `with` clause and this fails, where the
absorption fact would not. -/
theorem erratum685_carries_erratum684_bound :
    countSubDef natSExpU11000 wasm10.erratum685.corrected = 0 ∧
      countSubDef natSExpU110000 wasm10.erratum685.corrected = 1 := by
  constructor <;> rfl

/-- **`applyErrata` is absorbing on a fixed target.**  Applying `#684` and
then `#685` is applying `#685`, because `IL.replaceDefs` keyed on `utf8`
overwrites whatever is there.  This is a statement about `applyErrata` and
nothing else: it says the order in `wasm10errata` is harmless, *not* that
`#685` preserves `#684` — for that, see
`erratum685_carries_erratum684_bound`. -/
theorem applyErrata_utf8_absorbing :
    applyErrata [wasm10.erratum684, wasm10.erratum685] Specs.wasm10 =
      applyErrata [wasm10.erratum685] Specs.wasm10 := by
  rfl

end Silmaril.SpecTec.IL.Wasm10
