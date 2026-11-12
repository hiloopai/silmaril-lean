module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The wasm-3.0 text format §6.x errata

The verified errata of `#677`, as patches on
`Silmaril.SpecTec.Specs.wasm30`.  As in
`Silmaril/SpecTec/Errata/Binary51.lean`, each patch is a minimal textual edit
of one definition's own `--ast` rendering, written out by `spectec_erratum`
(`Silmaril/SpecTec/Errata.lean`).

`#677` has eleven sub-issues.  Seven of them become nine patches; the other
four cannot be an AST edit at all, for three different reasons.  The triage is
the content of this file, so it is spelled out first.

## Patched — seven issues, nine definitions

| issue | upstream line | definitions patched |
| --- | --- | --- |
| #661 | `6.1-text.values.spectec:98` | `Tstringchar` |
| #662 | `6.1-text.values.spectec:59-63` | `Tfloat`, `Thexfloat` |
| #663 | `6.3-text.instructions.spectec:184-186` | `Talign_` |
| #664 | `6.2-text.types.spectec:164`, `:169` | `Ttypeuse_` |
| #665 | `6.0-text.lexical.spectec:56-64` | `Tblockcomment`, `Tblockchar` |
| #692 | `6.4-text.modules.spectec:187` | `Texporttabledots_` (half of it) |
| #694 | `6.0-text.lexical.spectec:26-27` | `Treserved` |

## Not patchable — the `==` equations are erased before the IL

**#666, #693, and the other half of #692 have nothing to patch.**  All three
report a defect in an *abbreviation* production, written `lhs == rhs` in the
`.spectec` source.  SpecTec's elaborator does not translate those: `EquivP` is
the EL constructor for `==` (`spectec/src/el/ast.ml:149`), and `elab_prod`'s
`EquivP` branch type-checks both sides and then returns the empty list of IL
productions, with the comment `TODO(4, rossberg): translate equiv grammars
properly` (`spectec/src/frontend/elab.ml:2297-2309`).

The consequence is visible in the pinned stream.  The five inline-export
abbreviations of `#666` are the *whole* content of their grammars, so what
`spectec --ast` emits for each of them is a definition with no productions at
all — for instance

```
(gram "Texportfunc_" (exp "I" (var "I")) (tup))
```

and the same for `Texporttag_`, `Texportglobal_`, `Texportmem_`,
`Texporttable_`, `Telemtable_` and `Tdatamem_`.  `Telem_`, whose `/abbrev`
fragment is `#693`, keeps exactly the three `/plain` productions of
`6.4-text.modules.spectec:90-97` and none of the abbreviation at `:99-101`.

This was checked the same way the edits below were: the five swaps `#666` asks
for (`6.4-text.modules.spectec:198-231`) and the `Tid?` `#693` asks for
(`:99-101`) were applied to a copy of `specification/wasm-3.0/`, the official
frontend was re-run at the pin, and the resulting stream is **byte-identical**
to `specs/spectec/wasm-3.0.ast`.  An `IL.Erratum` has to change the definition
it names (`spectec_erratum` rejects a no-op), so neither issue can be written
as one, and `#692` can only be written for its `Texporttabledots_` half.

Fixing them in the IL would mean fixing `elab_prod` first, upstream; until
then the defects live in the EL and in the rendered prose, which the SpecTec
splicer generates from the EL directly.  `#666`'s own text records that
`6.4-text.modules.spectec:195-196` already carries
`TODO(5, rossberg): These abbreviations are currently not formally reachable`,
which is the same fact seen from the other side.

## Not an edit — #695

`#695` is four *ambiguities*: a bare `select`, block types that are a value
form, a table with no initializer, and empty `(param)`/`(result)` clauses
after `(type x)`.  In each one SpecTec derives the intended reading **and** a
second one with a different AST; nothing in the stream is wrong, so there is
no definition to correct.  Resolving one means *adding* a premise or narrowing
an iteration — for `Tblocktype_`, a premise on the type-use alternative
excluding inline parameter-free, at-most-one-result uses; for `Ttable_/plain`,
a non-empty `Texpr_`.  Those are new content rather than a correction, and
`#695` itself asks for them as clarification requests at lower priority, so
they are left out.

## Out of scope — #696

`#696` is the converse direction: two places where **SpecTec is right and the
reference interpreter differs**.  The interpreter's lexer encodes a surrogate
`\u{D800}` escape with `Utf8.encode` instead of rejecting it, although its own
decoder uses `0xd800 <= n && n < 0xe000` as the surrogate test
(`interpreter/binary/utf8.ml:26-28`); and its *standalone* `externtype` import
rule takes `(type x)` alone or inline parameters alone, never both, where
SpecTec's `Ttypeuse_` allows `(type x) param* result*`.

The second half is a statement about the `externtype` nonterminal, not about
`typeuse`: `interpreter/text/parser.mly:1235-1237` is
`LPAR FUNC bindidx_opt typeuse RPAR`, which takes a type use and nothing else,
and the alternative that takes inline parameters is the separate `/* Sugar */`
rule `LPAR FUNC bindidx_opt functype RPAR` at `:1253-1255`.  (The `typeuse`
nonterminal itself, `parser.mly:470-471`, is just `LPAR TYPE idx RPAR`; it
says nothing about what may follow.)  "Never both" is true only of that
standalone form: the *inline*-import sugar
`inline_import typeuse func_fields_import` (`parser.mly:977-981`) does accept
`(type x)` and inline parameters together, and reconciles the two with
`inline_functype_explicit` (`parser.mly:237`).  Neither is a defect in the
specification, so neither gets a patch here.

## How each edit was checked

The patches are written against the printed form, which is a derived artifact,
so every one of them was produced from the *source* rather than guessed.  Each
edit of `#677` was applied to a copy of `specification/wasm-3.0/`, the official
frontend was re-run over it at the pin with the same `--ast-width 80` and the
same file order as `specs/spectec/manifest.json`, and the resulting stream was
diffed against the pinned one.  The combined run changes exactly the nine
definitions named above and nothing else; the unpatched run reproduces
`specs/spectec/wasm-3.0.ast` byte for byte (SHA-256
`7ae4c5806b39775969ddf8a757697f315395a50a187e27b253023292a670e095`, the value
`specs/spectec/manifest.json` and `specs/wasm/core-3.0.json` both record), so
the comparison is sound.  The `replacing`/`with` pairs below are the minimal
spans of those diffs.

As in `Binary51.lean`, the two `import all` lines above are what makes
`applyErrata_text6x` a `rfl` the kernel can do: `spectec_import` adds
`Specs.wasm30` with `Lean.addDecl`, which bypasses the `@[expose]` of the
section it sits in.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL.Text6x

set_option maxRecDepth 100000

/-! ## #661 — the `\u{n}` escape excludes 2048 valid scalar values

`6.1-text.values.spectec:98` reads

```
  | "\\u{" n:Thexnum "}" => n  -- if n < 0xD800 \/ 0xE800 <= n < 0x110000
```

The block the condition means to exclude is the UTF-16 surrogate range
U+D800..U+DFFF, whose upper bound is U+E000; `6.0-text.lexical.spectec:8`
defines `Tchar` with exactly that boundary.  Read literally, the 2048 escapes
`\u{E000}` to `\u{E7FF}` have no derivation, while the same characters written
directly do.  The reference interpreter's own UTF-8 decoder uses the same
boundary, `0xd800 <= n && n < 0xe000` (`interpreter/binary/utf8.ml:26-28`).

`0xE800` is `59392` and `0xE000` is `57344`; `59392` occurs once in the printed
`Tstringchar`, in exactly that premise. -/

spectec_erratum 661 in Specs.wasm30 on "Tstringchar"
  because "6.1-text.values.spectec:98 reads `-- if n < 0xD800 \\/ 0xE800 <= n < 0x110000` "
          "for the \\u{n} escape; the surrogate block it excludes is U+D800..U+DFFF, which "
          "ends at U+E000, so the second bound must read 0xE000"
  replacing "(num (nat 59392))"
  with      "(num (nat 57344))"

/-! ## #662 — every float literal needs an exponent

`6.1-text.values.spectec:59-63` reads

```
grammar Tfloat : rat =
  | p:Tmant ("E" | "e") s:Tsign ee:Tnum => $(p * 10^(s * ee))

grammar Thexfloat : rat =
  | "0x" p:Thexmant ("P" | "p") s:Tsign ee:Tnum => $(p * 2^(s * ee))
```

A SpecTec production is a plain sequence; optional parts are written with `?`
or `eps`, and the same source file does so for `"."?` in `Tmant` (`:46-48`).  So each
of the two grammars has exactly one production and that production requires an
exponent, which leaves `(f32.const 1.5)`, `(f64.const 0.0)`, `(f64.const
12345)` and `(f64.const 0x1.8)` without a derivation — most of the test suite.
The reference lexer's `float` rule has the exponent-free forms
(`interpreter/text/lexer.mll:99-106`), and so do the 1.0 and 2.0 RECs.

The fix restores the REC's bare alternative in each grammar.  It is an
insertion, so the `replacing` fragment is the head of the production that
follows, which fixes where the new one goes. -/

spectec_erratum 662 in Specs.wasm30 on "Tfloat"
  because "6.1-text.values.spectec:59-60 gives Tfloat the single production "
          "`p:Tmant (\"E\" | \"e\") s:Tsign ee:Tnum`, which makes the exponent mandatory, "
          "so 1.5 and 12345 are not float literals; the 1.0 and 2.0 RECs also have the "
          "exponent-free alternative `p:Tmant => p`"
  replacing "(gram \"Tfloat\" rat (prod (exp \"p\" rat) (exp \"s\" int)"
  with      "(gram \"Tfloat\" rat (prod (exp \"p\" rat) (attr (var \"p\") (var \"Tmant\")"
            ") (var \"p\")) (prod (exp \"p\" rat) (exp \"s\" int)"
  as erratum662Tfloat

spectec_erratum 662 in Specs.wasm30 on "Thexfloat"
  because "6.1-text.values.spectec:62-63 gives Thexfloat the single production "
          "`\"0x\" p:Thexmant (\"P\" | \"p\") s:Tsign ee:Tnum`, which makes the exponent "
          "mandatory, so 0x1.8 is not a float literal; the 1.0 and 2.0 RECs also have the "
          "exponent-free alternative `\"0x\" p:Thexmant => p`"
  replacing "(gram \"Thexfloat\" rat (prod (exp \"p\" rat) (exp \"s\" int)"
  with      "(gram \"Thexfloat\" rat (prod (exp \"p\" rat) (seq (seq (text \"0x\")) (seq "
            "(attr (var \"p\") (var \"Thexmant\")))) (var \"p\")) (prod (exp \"p\" rat) ("
            "exp \"s\" int)"
  as erratum662Thexfloat

/-! ## #663 — the default alignment is a byte count where an exponent is meant

`6.3-text.instructions.spectec:184-186` reads

```
grammar Talign_(N) : u32 =
  | "align=" m:Tu64 => n  -- if $(m = 2^n)
  | eps => N
```

The explicit branch returns the exponent `n`; the default branch returns the
byte count `N`.  The callers pass the access size in bytes — `Tmemarg_(4)` for
`i32.load`, `(8)` for `i64.load` — and validation asks for
`2^(memarg.ALIGN) <= $size(nt)/8` (`2.3-validation.instructions.spectec:446`),
so a bare `i32.load` gets `ALIGN 4`, that is sixteen bytes, and never
validates.  The reference parser stores `log2_unsigned n` for the explicit
case and `None`, meaning natural alignment, for the default
(`interpreter/text/parser.mly:532-541`).

The corrected default binds the same `n` and carries the same `2^n` premise as
the explicit branch, with `N` on the left of the equation instead of `m`. -/

spectec_erratum 663 in Specs.wasm30 on "Talign_"
  because "6.3-text.instructions.spectec:186 reads `| eps => N`, a byte count, while the "
          "explicit branch at :185 and memarg.ALIGN everywhere else are exponents, so a bare "
          "i32.load would get ALIGN 4 and fail validation; the default must be the n with "
          "N = 2^n"
  replacing "(prod eps (case \"%\" (tup (var \"N\"))))"
  with      "(prod (exp \"n\" (var \"n\")) eps (case \"%\" (tup (var \"n\"))) (if (cmp eq"
            " bool (var \"N\") (bin pow nat (num (nat 2)) (var \"n\")))))"

/-! ## #664 — an explicit `(type x)` must name a final type with no supertypes

`6.2-text.types.spectec:160-171` gives `Ttypeuse_/base` two productions, and
both carry

```
    -- if st*[i] = SUB FINAL (FUNC t_1* -> t_2*)
```

A premise is a structural equality, and the abstract syntax is
`SUB final? typeuse* comptype` (`1.2-syntax.types.spectec:120`), so writing
`SUB FINAL (FUNC ...)` fixes `final?` to present *and* `typeuse*` to empty.
That rejects `(sub (func))`, `(sub $t0 (func))` and `(sub final $t0 (func))`
alike — the whole runtime-types section of `gc/type-subtyping.wast`.  The
reference interpreter performs no such check: `typeuse` is just
`LPAR TYPE idx RPAR` (`interpreter/text/parser.mly:470-471`) and `func_type`
expands the deftype and accepts any `FuncT`, ignoring finality and supertypes
(`:165-169`).  The `SUB FINAL` in `Ttypeuse_/abbrev` (`6.2:174`) is correct and
is deliberately left alone.

**Why this patch is so large.**  The edit is four small things — a fresh
`tu*` binder in each of the two productions' variable lists, and `(list)`
becoming an iteration over it in each of the two premises — but a binder list
is printed before the production's symbol and attribute, so the two changes in
one production are about a thousand characters apart, and `spectec_erratum`
makes one contiguous replacement.  The minimal span that covers all four runs
from the first production's binder list to the second production's premise:
2155 of the definition's 2996 characters.  It was not written by hand; it is
the diff of the two frontend runs. -/

spectec_erratum 664 in Specs.wasm30 on "Ttypeuse_"
  because "6.2-text.types.spectec:164 and :169 read "
          "`-- if st*[i] = SUB FINAL (FUNC t_1* -> t_2*)`, which fixes final? to present and "
          "typeuse* to empty, so an explicit (type x) cannot name a non-final or subtyped "
          "function type; the premise must read `SUB FINAL? tu* (FUNC t_1* -> t_2*)`"
  replacing "(exp \"t_1*\" (iter (var \"valtype\") list)) (exp \"t_2*\" (iter (var \"valt"
            "ype\") list)) (seq (seq (text \"(\")) (seq (text \"type\")) (seq (attr (var "
            "\"x\") (var \"Ttypeidx_\" (exp (var \"I\"))))) (seq (text \")\"))) (tup (var"
            " \"x\") (var \"I'\")) (if (cmp eq bool (idx (dot (var \"I\") \"TYPEDEFS\") ("
            "proj (uncase (var \"x\") \"%\") 0)) (opt (case \"_DEF\" (tup (case \"REC\" ("
            "case \"%\" (tup (iter (var \"st\") list (dom \"st\" (var \"st*\")))))) (var "
            "\"i\")))))) (if (cmp eq bool (idx (iter (var \"st\") list (dom \"st\" (var "
            "\"st*\"))) (var \"i\")) (case \"SUB\" (tup (opt (case \"FINAL\" (tup))) (lis"
            "t) (case \"FUNC%->%\" (tup (case \"%\" (tup (iter (var \"t_1\") list (dom \""
            "t_1\" (var \"t_1*\"))))) (case \"%\" (tup (iter (var \"t_2\") list (dom \"t_"
            "2\" (var \"t_2*\"))))))))))) (if (cmp eq bool (var \"I'\") (struct (field \""
            "TYPES\" (list)) (field \"TAGS\" (list)) (field \"GLOBALS\" (list)) (field \""
            "MEMS\" (list)) (field \"TABLES\" (list)) (field \"FUNCS\" (list)) (field \"D"
            "ATAS\" (list)) (field \"ELEMS\" (list)) (field \"LOCALS\" (iter (opt (case "
            "\"%\" (tup (list)))) (listn (len (iter (var \"t_1\") list (dom \"t_1\" (var "
            "\"t_1*\"))))))) (field \"LABELS\" (list)) (field \"FIELDS\" (list)) (field "
            "\"TYPEDEFS\" (list)))))) (prod (exp \"x\" (var \"idx\")) (exp \"I'\" (var \""
            "I\")) (exp \"id?*\" (iter (iter (var \"char\") opt) list)) (exp \"t_1*\" (it"
            "er (var \"valtype\") list)) (exp \"t_2*\" (iter (var \"valtype\") list)) (ex"
            "p \"st*\" (iter (var \"subtype\") list)) (exp \"i\" (var \"n\")) (seq (seq ("
            "text \"(\")) (seq (text \"type\")) (seq (attr (var \"x\") (var \"Ttypeidx_\""
            " (exp (var \"I\"))))) (seq (text \")\")) (seq (attr (iter (tup (var \"t_1\")"
            " (opt (case \"%\" (tup (lift (iter (var \"id\") opt (dom \"id\" (var \"id?\""
            ")))))))) list (dom \"id?\" (var \"id?*\")) (dom \"t_1\" (var \"t_1*\"))) (it"
            "er (var \"Tparam_\" (exp (var \"I\"))) list))) (seq (attr (iter (var \"t_2\""
            ") list (dom \"t_2\" (var \"t_2*\"))) (iter (var \"Tresult_\" (exp (var \"I\""
            "))) list)))) (tup (var \"x\") (var \"I'\")) (if (cmp eq bool (idx (dot (var "
            "\"I\") \"TYPEDEFS\") (proj (uncase (var \"x\") \"%\") 0)) (opt (case \"_DEF"
            "\" (tup (case \"REC\" (case \"%\" (tup (iter (var \"st\") list (dom \"st\" ("
            "var \"st*\")))))) (var \"i\")))))) (if (cmp eq bool (idx (iter (var \"st\") "
            "list (dom \"st\" (var \"st*\"))) (var \"i\")) (case \"SUB\" (tup (opt (case "
            "\"FINAL\" (tup))) (list"
  with      "(exp \"tu*\" (iter (var \"typeuse\") list)) (exp \"t_1*\" (iter (var \"valty"
            "pe\") list)) (exp \"t_2*\" (iter (var \"valtype\") list)) (seq (seq (text \""
            "(\")) (seq (text \"type\")) (seq (attr (var \"x\") (var \"Ttypeidx_\" (exp ("
            "var \"I\"))))) (seq (text \")\"))) (tup (var \"x\") (var \"I'\")) (if (cmp e"
            "q bool (idx (dot (var \"I\") \"TYPEDEFS\") (proj (uncase (var \"x\") \"%\") "
            "0)) (opt (case \"_DEF\" (tup (case \"REC\" (case \"%\" (tup (iter (var \"st"
            "\") list (dom \"st\" (var \"st*\")))))) (var \"i\")))))) (if (cmp eq bool (i"
            "dx (iter (var \"st\") list (dom \"st\" (var \"st*\"))) (var \"i\")) (case \""
            "SUB\" (tup (iter (case \"FINAL\" (tup)) opt) (iter (var \"tu\") list (dom \""
            "tu\" (var \"tu*\"))) (case \"FUNC%->%\" (tup (case \"%\" (tup (iter (var \"t"
            "_1\") list (dom \"t_1\" (var \"t_1*\"))))) (case \"%\" (tup (iter (var \"t_2"
            "\") list (dom \"t_2\" (var \"t_2*\"))))))))))) (if (cmp eq bool (var \"I'\")"
            " (struct (field \"TYPES\" (list)) (field \"TAGS\" (list)) (field \"GLOBALS\""
            " (list)) (field \"MEMS\" (list)) (field \"TABLES\" (list)) (field \"FUNCS\" "
            "(list)) (field \"DATAS\" (list)) (field \"ELEMS\" (list)) (field \"LOCALS\" "
            "(iter (opt (case \"%\" (tup (list)))) (listn (len (iter (var \"t_1\") list ("
            "dom \"t_1\" (var \"t_1*\"))))))) (field \"LABELS\" (list)) (field \"FIELDS\""
            " (list)) (field \"TYPEDEFS\" (list)))))) (prod (exp \"x\" (var \"idx\")) (ex"
            "p \"I'\" (var \"I\")) (exp \"id?*\" (iter (iter (var \"char\") opt) list)) ("
            "exp \"t_1*\" (iter (var \"valtype\") list)) (exp \"t_2*\" (iter (var \"valty"
            "pe\") list)) (exp \"st*\" (iter (var \"subtype\") list)) (exp \"i\" (var \"n"
            "\")) (exp \"tu*\" (iter (var \"typeuse\") list)) (seq (seq (text \"(\")) (se"
            "q (text \"type\")) (seq (attr (var \"x\") (var \"Ttypeidx_\" (exp (var \"I\""
            "))))) (seq (text \")\")) (seq (attr (iter (tup (var \"t_1\") (opt (case \"%"
            "\" (tup (lift (iter (var \"id\") opt (dom \"id\" (var \"id?\")))))))) list ("
            "dom \"id?\" (var \"id?*\")) (dom \"t_1\" (var \"t_1*\"))) (iter (var \"Tpara"
            "m_\" (exp (var \"I\"))) list))) (seq (attr (iter (var \"t_2\") list (dom \"t"
            "_2\" (var \"t_2*\"))) (iter (var \"Tresult_\" (exp (var \"I\"))) list)))) (t"
            "up (var \"x\") (var \"I'\")) (if (cmp eq bool (idx (dot (var \"I\") \"TYPEDE"
            "FS\") (proj (uncase (var \"x\") \"%\") 0)) (opt (case \"_DEF\" (tup (case \""
            "REC\" (case \"%\" (tup (iter (var \"st\") list (dom \"st\" (var \"st*\")))))"
            ") (var \"i\")))))) (if (cmp eq bool (idx (iter (var \"st\") list (dom \"st\""
            " (var \"st*\"))) (var \"i\")) (case \"SUB\" (tup (iter (case \"FINAL\" (tup)"
            ") opt) (iter (var \"tu\") list (dom \"tu\" (var \"tu*\"))"

/-! ## #665 — block comments cannot end in a semicolon, and do not nest

`6.0-text.lexical.spectec:56-64` reads

```
grammar Tblockcomment =
  | "(;" Tblockchar* ";)"

grammar Tblockchar =
  | c:Tchar       -- if c =/= ";" /\ c =/= "("
  | ";"+ c:Tchar  -- if c =/= ";" /\ c =/= ")"
  | "("+ c:Tchar  -- if c =/= ";" /\ c =/= "("
  | Tblockcomment
```

The 1.0 and 2.0 RECs disambiguate block comments with *look-ahead*: `;` is
allowed if the next character is not `)`, `(` if the next is not `;`.  SpecTec
grammars have no look-ahead, and the transcription turned both restrictions
into productions that **consume** the next character.  Every alternative then
ends in a non-`;` character or in `)`, so no comment body can end in `;`:
`(;a;;)` and `comments.wast:26`'s `(;;;;;;;;;;;;;;)` have no derivation.  And
`;(` is consumed as a pair, so `(; ;(; x ;) ;)` loses its inner opener.  The
reference lexer's `comment` rule closes on `";)"`, recurses on `"(;"` and
skips anything else (`interpreter/text/lexer.mll:902-908`).

The replacement is look-ahead-free.  `#665` records an exhaustive comparison
of it against that rule, and the experiment was re-run here: over the
1 398 101 bodies of length 0 to 10 over `{; ( ) a}`, the corrected grammar
agrees with the lexer on every one and the literal grammar disagrees on
**181 548** of them.  `#665` quotes the figure 12 565, which is the
*cumulative* disagreement count through length 8 — a universe of 87 381
bodies — and not the count over the universe it is attached to; the
per-length counts are 1, 4, 13, 47, 174, 650, 2442, 9234, 35090, 133893 for
lengths 1 to 10.  It is two
edits: `Tblockcomment` gains a `";"*` run before the closing `";)"`, and
`Tblockchar` gains `c =/= "("` on the second alternative and `";"*` prefixes on
the third and fourth. -/

spectec_erratum 665 in Specs.wasm30 on "Tblockcomment"
  because "6.0-text.lexical.spectec:57 reads `| \"(;\" Tblockchar* \";)\"`, and no "
          "Tblockchar can end in `;`, so a comment body ending in `;` has no derivation; the "
          "closing delimiter must be allowed to be preceded by a run of semicolons"
  replacing "(seq (iter (var \"Tblockchar\") list)) (seq (text \";)\"))"
  with      "(seq (iter (var \"Tblockchar\") list)) (seq (iter (text \";\") list)) (seq ("
            "text \";)\"))"
  as erratum665Tblockcomment

spectec_erratum 665 in Specs.wasm30 on "Tblockchar"
  because "6.0-text.lexical.spectec:60-64 replaces the 1.0/2.0 look-ahead restrictions by "
          "productions that consume the next character, which SpecTec has no way to undo, so "
          "`(;;;;;;;;;;;;;;)` of comments.wast:26 has no derivation and `;(;` does not nest"
  replacing "(cmp ne bool (var \"c\") (case \"%\" (tup (num (nat 59))))) (cmp ne bool (va"
            "r \"c\") (case \"%\" (tup (num (nat 41)))))))) (prod (exp \"<implicit-prod-r"
            "esult>\" (tup)) (exp \"c\" (var \"char\")) (attr (var \"<implicit-prod-resul"
            "t>\") (seq (seq (iter (text \"(\") list1)) (seq (attr (var \"c\") (var \"Tch"
            "ar\"))))) (proj (tup (var \"<implicit-prod-result>\") (tup)) 1) (if (bin and"
            " bool (cmp ne bool (var \"c\") (case \"%\" (tup (num (nat 59))))) (cmp ne bo"
            "ol (var \"c\") (case \"%\" (tup (num (nat 40)))))))) (prod (exp \"<implicit-"
            "prod-result>\" (tup)) (attr (var \"<implicit-prod-result>\") (var \"Tblockco"
            "mment\""
  with      "(bin and bool (cmp ne bool (var \"c\") (case \"%\" (tup (num (nat 59))))) (c"
            "mp ne bool (var \"c\") (case \"%\" (tup (num (nat 41)))))) (cmp ne bool (var"
            " \"c\") (case \"%\" (tup (num (nat 40)))))))) (prod (exp \"<implicit-prod-re"
            "sult>\" (tup)) (exp \"c\" (var \"char\")) (attr (var \"<implicit-prod-result"
            ">\") (seq (seq (iter (text \";\") list)) (seq (iter (text \"(\") list1)) (se"
            "q (attr (var \"c\") (var \"Tchar\"))))) (proj (tup (var \"<implicit-prod-res"
            "ult>\") (tup)) 1) (if (bin and bool (cmp ne bool (var \"c\") (case \"%\" (tu"
            "p (num (nat 59))))) (cmp ne bool (var \"c\") (case \"%\" (tup (num (nat 40))"
            ")))))) (prod (exp \"<implicit-prod-result>\" (tup)) (attr (var \"<implicit-p"
            "rod-result>\") (seq (seq (iter (text \";\") list)) (seq (iter (text \"(\") l"
            "ist)) (var \"Tblockcomment\")"
  as erratum665Tblockchar

/-! ## #692 — an inline table element segment reads its body as a `Telemlist_`

`6.4-text.modules.spectec:187`, the second alternative of
`Texporttabledots_`, reads

```
  | Texportdots* Taddrtype? Treftype_(I) "(" "elem" Telemlist_(I) ")"
```

and `Telemlist_` (`:103-108`) has exactly two alternatives, one starting with a
reference type and one with the keyword `func`.  So the forms the test suite
uses — `(table funcref (elem $f))` throughout `test/core`, and
`(table $t funcref (elem (ref.func $f) ...))` at `elem.wast:84` — have no
derivation, while `(table funcref (elem func $f))`, which the reference
interpreter rejects with a syntax error, does.  The interpreter's `table_fields`
has the two bare forms, one or more element expressions and a possibly empty
index list, and gives both the *table's* reference type
(`interpreter/text/parser.mly:1208-1229`).

**This is half of `#692`.**  The issue reports the same defect twice, in
`Texporttabledots_` and in `Telemtable_/abbrev` (`:243-250`), and the second one
is an `==` equation that the elaborator erases, as the module header explains.
The patch below restores the two 2.0 abbreviations in the alternative that does
survive. -/

spectec_erratum 692 in Specs.wasm30 on "Texporttabledots_"
  because "6.4-text.modules.spectec:187 reads `| Texportdots* Taddrtype? Treftype_(I) "
          "\"(\" \"elem\" Telemlist_(I) \")\"`, and Telemlist_ (:103-108) needs a "
          "leading reftype or `func`, so `(table funcref (elem $f))` has no derivation; the "
          "body is a bare funcidx list or a bare element-expression list"
  replacing "(seq (var \"Telemlist_\" (exp (var \"I\""
  with      "(seq (var \"Tlist\" (typ (var \"expr\")) (gram (var \"Telemexpr_\" (exp (var"
            " \"I\")))))) (seq (text \")\")))) (proj (tup (var \"<implicit-prod-result>\""
            ") (tup)) 1)) (prod (exp \"<implicit-prod-result>\" (tup)) (attr (var \"<impl"
            "icit-prod-result>\") (seq (seq (iter (var \"Texportdots\") list)) (seq (iter"
            " (var \"Taddrtype\") opt)) (seq (var \"Treftype_\" (exp (var \"I\")))) (seq "
            "(text \"(\")) (seq (text \"elem\")) (seq (var \"Tlist\" (typ (var \"funcidx"
            "\")) (gram (var \"Tfuncidx_\" (exp (var \"I\"))"

/-! ## #694 — a line comment cannot follow a token

`6.0-text.lexical.spectec:26-27` reads

```
grammar Treserved =
  | (Tidchar | Tstring | "," | ";" | "[" | "]" | "{" | "}")+
```

With `;` inside the repeated run and the longest-match rule of
`document/core/text/lexical.rst:40-41`, the text `func;;bla` lexes as the
single reserved token `func;;bla` rather than as the keyword `func` followed by
a line comment.  Reserved tokens cannot occur in source text, so five of the
six modules of `token.wast:52-77` — the section headed "Tokens can be delimited
by comments" — are malformed.  The reference lexer keeps the punctuation out of
the run: `let reserved = (idchar | string)+ | ',' | ';' | '[' | ']' | '{' |
'}'` (`interpreter/text/lexer.mll:113`), and so does the 2.0 REC.  The merged
form is an artifact of the 2023 merge of the annotations proposal into main.

Splitting the alternatives turns one production into seven, six of which are
single characters: `0x2C`, `0x3B`, `0x5B`, `0x5D`, `0x7B`, `0x7D`. -/

spectec_erratum 694 in Specs.wasm30 on "Treserved"
  because "6.0-text.lexical.spectec:26-27 reads "
          "`| (Tidchar | Tstring | \",\" | \";\" | \"[\" | \"]\" | \"{\" | "
          "\"}\")+`, so by longest match `func;;bla` is one reserved token and "
          "token.wast:54-77 is malformed; the punctuation must be separate alternatives"
  replacing " (seq (text \",\")) (seq (text \";\")) (seq (text \"[\")) (seq (text \"]\"))"
            " (seq (text \"{\")) (seq (text \"}\"))) list1"
  with      ") list1)) (proj (tup (var \"<implicit-prod-result>\") (tup)) 1)) (prod (exp "
            "\"<implicit-prod-result>\" nat) (attr (var \"<implicit-prod-result>\") (num "
            "0x2C)) (proj (tup (var \"<implicit-prod-result>\") (tup)) 1)) (prod (exp \"<"
            "implicit-prod-result>\" nat) (attr (var \"<implicit-prod-result>\") (num 0x3"
            "B)) (proj (tup (var \"<implicit-prod-result>\") (tup)) 1)) (prod (exp \"<imp"
            "licit-prod-result>\" nat) (attr (var \"<implicit-prod-result>\") (num 0x5B))"
            " (proj (tup (var \"<implicit-prod-result>\") (tup)) 1)) (prod (exp \"<implic"
            "it-prod-result>\" nat) (attr (var \"<implicit-prod-result>\") (num 0x5D)) (p"
            "roj (tup (var \"<implicit-prod-result>\") (tup)) 1)) (prod (exp \"<implicit-"
            "prod-result>\" nat) (attr (var \"<implicit-prod-result>\") (num 0x7B)) (proj"
            " (tup (var \"<implicit-prod-result>\") (tup)) 1)) (prod (exp \"<implicit-pro"
            "d-result>\" nat) (attr (var \"<implicit-prod-result>\") (num 0x7D"

/-! ## The corrected script

The definitions below are `noncomputable` for the reason `Binary51.lean` gives:
building the closed term for a list of reflected `IL.Def`s this large makes
Lean v4.35's LCNF boxing pass panic.  Nothing here is ever run — the kernel
*reduces* these values when it checks `applyErrata_text6x`, which
`noncomputable` does not affect. -/

/-- The patchable text-format errata of `#677`: seven issues,
nine patches.  The order is irrelevant, since the nine targets are pairwise
distinct and `IL.applyErratum_comm` lets any two adjacent entries be swapped. -/
noncomputable def text6x : List Erratum :=
  [wasm30.erratum661, wasm30.erratum662Tfloat, wasm30.erratum662Thexfloat,
    wasm30.erratum663, wasm30.erratum664, wasm30.erratum665Tblockcomment,
    wasm30.erratum665Tblockchar, wasm30.erratum692, wasm30.erratum694]

/-- `Specs.wasm30` with the nine patches of `text6x` applied: the wasm-3.0
specification with its verified §6.x text-format errata corrected.  Written out
as the chain of `IL.replaceDefs` that `applyErrata text6x` reduces to, which
`applyErrata_text6x` certifies. -/
noncomputable def wasm30text6x : Script :=
  replaceDefs wasm30.erratum694.corrected
    (replaceDefs wasm30.erratum692.corrected
      (replaceDefs wasm30.erratum665Tblockchar.corrected
        (replaceDefs wasm30.erratum665Tblockcomment.corrected
          (replaceDefs wasm30.erratum664.corrected
            (replaceDefs wasm30.erratum663.corrected
              (replaceDefs wasm30.erratum662Thexfloat.corrected
                (replaceDefs wasm30.erratum662Tfloat.corrected
                  (replaceDefs wasm30.erratum661.corrected Specs.wasm30))))))))

/-- All nine patches apply, and `wasm30text6x` is their result.

This is the one statement here the kernel has to *compute*, and it carries the
content: `IL.Erratum.applies` holds for each patch in turn, which says that its
target is declared exactly once in the script it is applied to, that its
corrected definition declares that target, and — through `IL.defEq`, hence
through `IL.defS` — that the corrected definition really differs from the one
it replaces.  "Exactly these nine definitions change" is that last conjunct,
nine times; "and nowhere else" is `text6xPatch_eq_self` below, which needs no
computation at all. -/
theorem applyErrata_text6x :
    applyErrata text6x Specs.wasm30 = some wasm30text6x := by
  rfl

/-! ## What changed, and what did not -/

/-- The nine patches, as the single function they apply to each top-level
definition of the pinned script. -/
noncomputable def text6xPatch (d : Def) : Def :=
  replaceDef wasm30.erratum694.corrected
    (replaceDef wasm30.erratum692.corrected
      (replaceDef wasm30.erratum665Tblockchar.corrected
        (replaceDef wasm30.erratum665Tblockcomment.corrected
          (replaceDef wasm30.erratum664.corrected
            (replaceDef wasm30.erratum663.corrected
              (replaceDef wasm30.erratum662Thexfloat.corrected
                (replaceDef wasm30.erratum662Tfloat.corrected
                  (replaceDef wasm30.erratum661.corrected d))))))))

/-- The corrected script is the pinned one with `text6xPatch` mapped over it:
the patches act on each top-level definition independently and in place. -/
theorem wasm30text6x_eq_map : wasm30text6x = Specs.wasm30.map text6xPatch := by
  simp [wasm30text6x, text6xPatch, replaceDefs_eq_map, List.map_map, Function.comp_def]

/-- **Nowhere else.**  A definition that declares none of the nine targets — in
any of `free.ml`'s namespaces (`spectec/src/il/free.ml:205-212`), and at any
depth inside a `recD` group, which is where `Tblockcomment` and `Tblockchar`
live — comes through all nine patches untouched.  With `wasm30text6x_eq_map`,
that is "the corrected script differs from the pinned one only in those nine
definitions". -/
theorem text6xPatch_eq_self {d : Def} (h₁ : countDef "Tstringchar" d = 0)
    (h₂ : countDef "Tfloat" d = 0) (h₃ : countDef "Thexfloat" d = 0)
    (h₄ : countDef "Talign_" d = 0) (h₅ : countDef "Ttypeuse_" d = 0)
    (h₆ : countDef "Tblockcomment" d = 0) (h₇ : countDef "Tblockchar" d = 0)
    (h₈ : countDef "Texporttabledots_" d = 0) (h₉ : countDef "Treserved" d = 0) :
    text6xPatch d = d := by
  have e₁ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum661.corrected) (x := "Tstringchar") rfl d h₁
  have e₂ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum662Tfloat.corrected) (x := "Tfloat") rfl d h₂
  have e₃ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum662Thexfloat.corrected) (x := "Thexfloat") rfl d h₃
  have e₄ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum663.corrected) (x := "Talign_") rfl d h₄
  have e₅ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum664.corrected) (x := "Ttypeuse_") rfl d h₅
  have e₆ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum665Tblockcomment.corrected) (x := "Tblockcomment") rfl d h₆
  have e₇ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum665Tblockchar.corrected) (x := "Tblockchar") rfl d h₇
  have e₈ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum692.corrected) (x := "Texporttabledots_") rfl d h₈
  have e₉ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum694.corrected) (x := "Treserved") rfl d h₉
  rw [text6xPatch, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉]

/-- The corrected script has the same 976 top-level definitions as the pinned
one. -/
theorem length_wasm30text6x : wasm30text6x.length = Specs.wasm30.length := by
  simp [wasm30text6x]

/-- The corrected script declares exactly the identifiers the pinned one
declares, in exactly the same namespaces (`spectec/src/il/free.ml:205-212`). -/
theorem boundDefs_wasm30text6x : boundDefs wasm30text6x = boundDefs Specs.wasm30 := by
  rw [wasm30text6x, boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs,
    boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs,
    boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs]

/-! ## The patches, read back off the `Erratum` values -/

/-- Seven issues, nine patches.  `#666`, `#693` and `#695` are absent because
they are not expressible as an AST edit, and `#696` because it is a report
about the reference interpreter; the module header says why for each. -/
example : text6x.map Erratum.issue = [661, 662, 662, 663, 664, 665, 665, 692, 694] := by
  rfl

/-- The nine definitions `#677` corrects. -/
example : text6x.map Erratum.target =
    ["Tstringchar", "Tfloat", "Thexfloat", "Talign_", "Ttypeuse_", "Tblockcomment",
      "Tblockchar", "Texporttabledots_", "Treserved"] := by
  rfl

/-- Each corrected definition declares its target, and all nine are grammars —
the §6.x errata are errata in the text *grammar*, never in a function or a
relation.  The nine are pairwise distinct, which is the hypothesis
`IL.applyErratum_comm` needs. -/
example : text6x.map (fun e => declKind? e.corrected) =
    [some (.gram, "Tstringchar"), some (.gram, "Tfloat"), some (.gram, "Thexfloat"),
      some (.gram, "Talign_"), some (.gram, "Ttypeuse_"), some (.gram, "Tblockcomment"),
      some (.gram, "Tblockchar"), some (.gram, "Texporttabledots_"),
      some (.gram, "Treserved")] := by
  rfl

/-- Two patches with distinct targets commute, so the order in `text6x` is not
load-bearing.  `Tblockcomment` and `Tblockchar` are the interesting pair: they
sit inside the same `recD` group, and `replaceDef` still reaches each of them
independently. -/
example : applyErrata [wasm30.erratum665Tblockchar, wasm30.erratum665Tblockcomment]
      Specs.wasm30 =
    applyErrata [wasm30.erratum665Tblockcomment, wasm30.erratum665Tblockchar]
      Specs.wasm30 :=
  (applyErrata_pair_comm (by decide) Specs.wasm30).symm

end Silmaril.SpecTec.IL.Text6x
