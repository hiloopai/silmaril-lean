module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The wasm-2.0 errata

The verified errata of `#660`, as patches on
`Silmaril.SpecTec.Specs.wasm20`.  Each is a minimal textual edit of one
definition's own `--ast` rendering, written out by `spectec_erratum`
(`Silmaril/SpecTec/Errata.lean`), so that a reader sees exactly what changed.
`Silmaril/SpecTec/Errata/Binary51.lean` is the worked example this file
follows; its preamble explains the two `import all` lines, which are what make
`applyErrata_wasm20errata` below a `rfl` the kernel can do.
`Silmaril/SpecTec/Sem/Eval.lean` is imported for one thing only: the last
section runs the `#673` patch, whose correction is a reformulation rather than
a one-token diff.

| issue | upstream line | definition patched |
| --- | --- | --- |
| #670 | `A-binary.spectec:472` | `Binstr` |
| #671 | `A-binary.spectec:873` | `Belem` |
| #672 | `A-binary.spectec:924` | `Bmodule` |
| #673 | `2-syntax-aux.spectec:85-87` | `dataidx_instrs` |

Bare file names are in `specification/wasm-2.0/` at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`; `wasm-3.0/…` is
`specification/wasm-3.0/` and `interpreter/…` is the reference interpreter, at
that same pin.  The 2.0 stream is `specs/spectec/wasm-2.0.ast`, whose SHA-256
`specs/spectec/manifest.json` records.

## Four of the eight sub-issues get no patch

`#674`, `#675`, `#676` and `#678` are the four *incompletenesses*: SpecTec
marks each with a `TODO`, and what is missing is a premise, a side condition
or a context field rather than a wrong token.  A `spectec_erratum` edits one
existing top-level definition, and `IL.Erratum` can replace a definition but
not add one; each of these four needs a declaration the pinned 2.0 script does
not contain.  They are triaged below and left unpatched.

**#674, `6-typing.spectec:681` `;; TODO: refs`.**  `Instr_ok/ref.func`
(`6-typing.spectec:294-296`) is `C |- REF.FUNC x : eps -> FUNCREF` with the
single premise `-- if C.FUNCS[x] = ft`; the W3C 2.0 text and
`wasm-3.0/2.3-validation.instructions.spectec:209` also require
`-- if x <- C.REFS`.  Three things stand in the way, and the third is fatal:
`syntax context` (`6-typing.spectec:5-9`) has no `REFS` field, so the premise
names a field that does not exist; `Module_ok`'s two context literals
(`6-typing.spectec:701` and `:703`) would each have to list it; and *computing*
the field needs the function indices that occur outside function bodies, which
`wasm-3.0/2.4-validation.modules.spectec:166` gets from `$funcidx_nonfuncs`,
hence from `$funcidx_module` (`wasm-3.0/1.4-syntax.modules.spectec:141-142`)
and the `$free_*` family.  `specification/wasm-2.0/` declares no `$free_*` and
no `$funcidx_*` function at all — `$dataidx_*` (`2-syntax-aux.spectec:80-97`)
is its only free-index family — so the premise cannot be written with
identifiers the pinned script declares.

**#675, `6-typing.spectec:699` `;; -- TODO: disjoint export names`.**  The
premise wanted is `wasm-3.0/2.4-validation.modules.spectec:161`'s
`-- if $disjoint_(name, nm*)`, and `$disjoint_` is itself a recursive function
(`wasm-3.0/0.3-aux.seq.spectec:35-37`).  wasm-2.0's `0-aux.spectec` declares
`$list_`, `$concat_` and `$inv_concat_` and no `$disjoint_`; and its
`Export_ok` (`6-typing.spectec:655-657`) is `C |- export : xt`, which unlike
3.0's `C |- export : nm xt_E` does not even carry the name, so `Module_ok`
would first have to destructure `export*` to get at `nm*`.  Writing pairwise
distinctness with the IL's own operators needs a new recursive `decD`, which
is a declaration this patch form cannot add.

**#676, `1-syntax.spectec:472` `;; TODO: missing constraints`.**  `VCVTOP`
takes two unconstrained `shape`s (`1-syntax.spectec:470-472`) and
`Instr_ok/vcvtop` (`6-typing.spectec:365-366`) is correspondingly premise-free,
so `VCVTOP (I8 X 16) (F64 X 2) (EXTEND LOW S)` is well typed and none of
`Step_pure/vcvtop-full`, `-half`, `-zero` (`8-reduction.spectec:353`, `:360`,
`:367`) applies: progress fails.  The side condition that would restore it is
"`$vcvtop__` is defined here" — `$vcvtop__` is declared at
`3-numerics.spectec:383` with its five equations at `:571-579` — and SpecTec
has no definedness predicate, so that premise is not writable.  wasm-3.0 does
not add a premise either: it makes the operator a *family indexed by the two
shapes*, `syntax vcvtop__(shape_1, shape_2)`
(`wasm-3.0/1.3-syntax.instructions.spectec:166-170`), which changes the syntax
of `vcvtop`, the syntax of `instr`, the typing rule and all three reduction
rules together.  Enumerating the legal combinations by hand instead would be
new content, not a transcription of anything in the pinned tree.

**#678, `A-binary.spectec:139` `;; TODO: typeidx`.**  `Bexterntype` reads
`| 0x00 ft:Bfunctype => FUNC ft` where the format encodes a type index.  The
grammar cannot simply read a `Btypeidx`: `syntax externtype`
(`1-syntax.spectec:179-180`) is `FUNC functype | GLOBAL globaltype | …`, so the
abstract syntax stores a *resolved* function type, and a SpecTec grammar has
no module context to resolve an index against.  wasm-3.0 fixes it by changing
the abstract syntax so that `externtype` carries a `typeuse`, which is what
lets `wasm-3.0/5.2-binary.types.spectec:103` read
`| 0x00 x:Btypeidx => FUNC (_IDX x)` — which is what the reference
interpreter does too: `interpreter/binary/decode.ml:306-308` reads
`0x00 -> ExternFuncT (typeuse idx s)`.  In wasm-2.0 that is an edit to
`syntax externtype` and then to every rule that matches `FUNC ft` — a
redesign, not an erratum patch.

Three further typing and reduction defects of the same kind, and one in the W3C
appendix, were found after the audit this file transcribes and are not covered here.

## What each patch was checked against

Every line number quoted in a `because` string was read out of the pinned file
with `sed -n 'Np'` before it was written down.  Three of the sub-issues cite
line numbers that are wrong in the issue text itself and right here: `#674`
places `Instr_ok/ref.func` at `6-typing.spectec:286-288` where the pin has it
at `:294-296`, `#675` places the `TODO` at `:697-699` where the pin has it at
`:698-699`, and `#676` places `Instr_ok/vcvtop` at `:274-275` and the three
`Step_pure/vcvtop-*` rules at `:387`, `:394`, `:401` where the pin has them at
`:365-366` and `:353`, `:360`, `:367`.  The *content* quoted in all three is
verbatim correct.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL.Wasm20

set_option maxRecDepth 100000

/-! ## #670 — `0xFD 92` is given twice and `v128.load64_zero` has no encoding

`A-binary.spectec:471-472` reads

```
  | 0xFD 92:Bu32 ao:Bmemarg => VLOAD V128 (ZERO 32) ao
  | 0xFD 92:Bu32 ao:Bmemarg => VLOAD V128 (ZERO 64) ao
```

Line 472 should read `0xFD 93`.  As written `Binstr` is ambiguous — `0xFD 5C`
derives both `VLOAD V128 (ZERO 32) ao` and `VLOAD V128 (ZERO 64) ao`, so the
binary format is not a function of the byte string at this production — and
`v128.load64_zero` has no encoding at all.
`interpreter/binary/decode.ml:786-787` dispatches `0x5c` to
`v128_load32_zero` and `0x5d` to `v128_load64_zero`, and
`wasm-3.0/5.3-binary.instructions.spectec:416-417` has `92` and `93`.

`Binstr` prints `92` as `(num (nat 92))` twice, so the fragment below carries
the whole production through to its `(ZERO 64)` result, which is what tells
the two apart. -/

spectec_erratum 670 in Specs.wasm20 on "Binstr"
  because "A-binary.spectec:472 repeats :471's opcode `0xFD 92` for `VLOAD V128 (ZERO 64) ao`; "
          "it should be `0xFD 93`, as wasm-3.0/5.3-binary.instructions.spectec:417 and "
          "interpreter/binary/decode.ml:787 both have it"
  replacing "(num (nat 92)))) (var \"Bu32\"))) (seq (attr (var \"ao\") (var \"Bmemarg\")))) (case "
            "\"VLOAD\" (tup (case \"V128\" (tup)) (opt (case \"ZERO\" (num (nat 64))))"
  with      "(num (nat 93)))) (var \"Bu32\"))) (seq (attr (var \"ao\") (var \"Bmemarg\")))) (case "
            "\"VLOAD\" (tup (case \"V128\" (tup)) (opt (case \"ZERO\" (num (nat 64))))"

/-! ## #671 — element segment kind 6 omits the reference type

`A-binary.spectec:873-874` reads

```
  | 6:Bu32 x:Btableidx expr:Bexpr e*:Blist(Bexpr) =>
      ELEM FUNCREF e* (ACTIVE x expr)
```

The eight kinds pair up: `0` and `4` leave the element type implicit, `1`,
`2`, `3` read a `Belemkind` byte, and `5`, `6`, `7` read a full `Breftype`.
Kinds `5` (`:871`) and `7` (`:875`) do; kind `6` is the only member of its
group that does not, and its counterpart `2` (`:865`) does read `Belemkind`.
`interpreter/binary/decode.ml:1191-1195`, the `elem` decoder's `0x06l` case,
reads a `reftype`, and
`wasm-3.0/5.4-binary.modules.spectec:113-114` reads it, so as written the
grammar mis-aligns on every kind-6 segment: it would read the encoder's
reference-type byte as the leading `u32` of the expression vector.

The edit adds the binder `rt`, the symbol `rt:Breftype` between `Bexpr` and
`Blist(Bexpr)`, and replaces `FUNCREF` by `rt` in the result.  The corrected
production is `wasm-3.0`'s kind 6 with the 2.0 variable names: the binder
order `rt e* x expr` is the one the printer uses there
(`specs/spectec/wasm-3.0.ast`, `Belem`), and it is the order of first
occurrence in the result expression, which is how every other production of
this grammar is printed. -/

spectec_erratum 671 in Specs.wasm20 on "Belem"
  because "A-binary.spectec:873 reads `| 6:Bu32 x:Btableidx expr:Bexpr e*:Blist(Bexpr)`, "
          "omitting the `rt:Breftype` field that kinds 5 (:871) and 7 (:875) read and that "
          "wasm-3.0/5.4-binary.modules.spectec:113 reads"
  replacing "(exp \"e*\" (iter (var \"expr\") list)) (exp \"x\" (var \"idx\")) (exp \"expr\" (var "
            "\"expr\")) (seq (seq (attr (case \"%\" (tup (num (nat 6)))) (var \"Bu32\"))) (seq (att"
            "r (var \"x\") (var \"Btableidx\"))) (seq (attr (var \"expr\") (var \"Bexpr\"))) (seq ("
            "attr (iter (var \"e\") list (dom \"e\" (var \"e*\"))) (var \"Blist\" (typ (var \"expr"
            "\")) (gram (var \"Bexpr\")))))) (case \"ELEM\" (tup (case \"FUNCREF\" (tup))"
  with      "(exp \"rt\" (var \"reftype\")) (exp \"e*\" (iter (var \"expr\") list)) (exp \"x\" (var"
            " \"idx\")) (exp \"expr\" (var \"expr\")) (seq (seq (attr (case \"%\" (tup (num (nat 6)"
            "))) (var \"Bu32\"))) (seq (attr (var \"x\") (var \"Btableidx\"))) (seq (attr (var \"ex"
            "pr\") (var \"Bexpr\"))) (seq (attr (var \"rt\") (var \"Breftype\"))) (seq (attr (iter "
            "(var \"e\") list (dom \"e\" (var \"e*\"))) (var \"Blist\" (typ (var \"expr\")) (gram ("
            "var \"Bexpr\")))))) (case \"ELEM\" (tup (var \"rt\")"

/-! ## #672 — the module version is a LEB128 numeral, not four bytes

`A-binary.spectec:923-924` reads

```
grammar Bmodule : module =
  | 0x00 0x61 0x73 0x6D 1:Bu32
```

`Bu32` is `BuN(32)` (`:37`, `:20-22`), the LEB128 grammar, so `1:Bu32` derives
the single byte `0x01` — or any of its non-minimal spellings — where every
`.wasm` file has the four bytes `0x01 0x00 0x00 0x00`.
`interpreter/binary/decode.ml:1262-1266` reads both the magic and the version
with `word32`, four raw little-endian bytes, and
`wasm-3.0/5.4-binary.modules.spectec:173-174` splits the header into
`grammar Bmagic : () = 0x00 0x61 0x73 0x6D => ()` and
`grammar Bversion : () = 0x01 0x00 0x00 0x00 => ()` precisely to say this.

The patch form edits one definition, so the four bytes go inline into
`Bmodule` rather than into a new `Bversion` grammar; the derived byte strings
are the same.  `1:Bu32` binds nothing, so the production's parameter list is
unchanged.  The fragment is the only `Bu32` in `Bmodule`. -/

spectec_erratum 672 in Specs.wasm20 on "Bmodule"
  because "A-binary.spectec:924 writes the module version as `1:Bu32`; `Bu32` is `BuN(32)` (:37, "
          ":20-22), a LEB128 numeral, so this derives the single byte 0x01 where the format has "
          "the four bytes 0x01 0x00 0x00 0x00 of wasm-3.0/5.4-binary.modules.spectec:174"
  replacing "(seq (attr (case \"%\" (tup (num (nat 1)))) (var \"Bu32\")))"
  with      "(seq (num 0x01)) (seq (num 0x00)) (seq (num 0x00)) (seq (num 0x00))"

/-! ## #673 — `$dataidx_*` does not descend into block bodies

`2-syntax-aux.spectec:80-87` reads

```
def $dataidx_instr(instr) : dataidx*  hint(show $dataidx(%))
def $dataidx_instr(MEMORY.INIT x) = x
def $dataidx_instr(DATA.DROP x) = x
def $dataidx_instr(in) = eps

def $dataidx_instrs(instr*) : dataidx*  hint(show $dataidx(%))
def $dataidx_instrs(eps) = eps
def $dataidx_instrs(instr instr'*) = $dataidx_instr(instr) $dataidx_instrs(instr'*)
```

Neither function descends into the nested sequences of `BLOCK`, `LOOP` or
`IF`, so a `memory.init` or `data.drop` inside a block is invisible.
`A-binary.spectec:941` is the only consumer —
`-- if n? =/= eps \/ $dataidx_funcs(func*) = eps` — so a module whose only
`memory.init` is nested may omit the data count section, which
`interpreter/binary/decode.ml:1299-1301` rejects: its
`data count section required` check runs over `Free.func`, and
`interpreter/syntax/free.ml:139` sends `Block (bt, es) | Loop (bt, es)` into
the recursive `block` of `:192`.
`wasm-3.0/1.4-syntax.modules.spectec:144-145` replaces the family with
`$dataidx_funcs(func*) = $free_list($free_func(func)*).DATAS`, and `$free_instr`
recurses.

**Why the patch is on `$dataidx_instrs` and not on `$dataidx_instr`.**  The
obvious fix adds `def $dataidx_instr(BLOCK bt in*) = $dataidx_instrs(in*)` and
its `LOOP` and `IF` companions.  That makes `$dataidx_instr` and
`$dataidx_instrs` *mutually* recursive, and SpecTec prints a recursion group
as one `recD`: the pinned stream has `$dataidx_instr` as a plain `(def …)` and
`$dataidx_instrs` alone inside a `(rec …)`, and the fix would fuse the two
top-level definitions into one.  A `spectec_erratum` replaces a definition in
place, so it cannot express that.

The equivalent fix that *is* one definition puts the three cases in
`$dataidx_instrs`, which is already self-recursive and already alone in its
own `recD`:

```
def $dataidx_instrs(eps) = eps
def $dataidx_instrs((BLOCK bt in*) instr'*) = $dataidx_instrs(in*) $dataidx_instrs(instr'*)
def $dataidx_instrs((LOOP bt in*) instr'*) = $dataidx_instrs(in*) $dataidx_instrs(instr'*)
def $dataidx_instrs((IF bt in_1* ELSE in_2*) instr'*) =
  $dataidx_instrs(in_1*) $dataidx_instrs(in_2*) $dataidx_instrs(instr'*)
def $dataidx_instrs(instr instr'*) = $dataidx_instr(instr) $dataidx_instrs(instr'*)
```

Clauses are tried in order and the first match wins
(`spectec/src/il/eval.ml:640-671`: `reduce_exp_call` falls through to
`clauses'`), so the three new clauses have to precede the
general one, which is where the edit inserts them.  The resulting dependency
graph is the pinned one — `$dataidx_instrs` still calls only itself and the
earlier, still non-recursive `$dataidx_instr` — so the script's `recD`
grouping is unchanged, which is why this is a definition the printer could
have printed.  `$dataidx_instr`'s only caller anywhere in
`specification/wasm-2.0/` is `$dataidx_instrs` (`2-syntax-aux.spectec:87`), so
correcting `$dataidx_instrs` corrects every use.

The anchor below is the head of the general clause, which occurs once.

**Where the `with` fragment comes from.**  Like every other patch in this
tree, it is read off a frontend run rather than hand-written: the five
`.spectec` lines above were inserted into a copy of
`specification/wasm-2.0/2-syntax-aux.spectec`, the official frontend was
re-run at the pin over the ten sources in `specs/spectec/manifest.json`'s
order with `--ast-width 80`, and the printed `dataidx_instrs` was diffed
against the pinned one; the unpatched run of the same command reproduces
`specs/spectec/wasm-2.0.ast` byte for byte (SHA-256
`8986f40c8cf58f4e9dd5176595df83c59eeee92f8bdb908f5687b12fd08e797b`).  The
diff is a pure insertion in front of the general clause, and the fragment
below is it verbatim.  One detail only a frontend run settles: the `IF`
clause's three-way concatenation is elaborated **right**-associated,
`(cat A (cat B C))`, not `(cat (cat A B) C)`.  The two denote the same list,
but only one of them is a definition the printer could have printed. -/

spectec_erratum 673 in Specs.wasm20 on "dataidx_instrs"
  because "2-syntax-aux.spectec:85-87 folds $dataidx_instr over the top-level sequence only, so "
          "a MEMORY.INIT inside a BLOCK, LOOP or IF body is invisible and A-binary.spectec:941 "
          "lets the data count section be omitted; wasm-3.0/1.4-syntax.modules.spectec:145 "
          "recurses"
  replacing "(clause (exp \"instr\" (var \"instr\"))"
  with      "(clause (exp \"bt\" (var \"blocktype\")) (exp \"in*\" (iter (var \"instr\") list)) (ex"
            "p \"instr'*\" (iter (var \"instr\") list)) (exp (cat (list (case \"BLOCK\" (tup (var "
            "\"bt\") (iter (var \"in\") list (dom \"in\" (var \"in*\")))))) (iter (var \"instr'\") "
            "list (dom \"instr'\" (var \"instr'*\"))))) (cat (call \"dataidx_instrs\" (exp (iter (v"
            "ar \"in\") list (dom \"in\" (var \"in*\"))))) (call \"dataidx_instrs\" (exp (iter (var"
            " \"instr'\") list (dom \"instr'\" (var \"instr'*\"))))))) (clause (exp \"bt\" (var \"b"
            "locktype\")) (exp \"in*\" (iter (var \"instr\") list)) (exp \"instr'*\" (iter (var \"i"
            "nstr\") list)) (exp (cat (list (case \"LOOP\" (tup (var \"bt\") (iter (var \"in\") lis"
            "t (dom \"in\" (var \"in*\")))))) (iter (var \"instr'\") list (dom \"instr'\" (var \"in"
            "str'*\"))))) (cat (call \"dataidx_instrs\" (exp (iter (var \"in\") list (dom \"in\" (v"
            "ar \"in*\"))))) (call \"dataidx_instrs\" (exp (iter (var \"instr'\") list (dom \"instr"
            "'\" (var \"instr'*\"))))))) (clause (exp \"bt\" (var \"blocktype\")) (exp \"in_1*\" (i"
            "ter (var \"instr\") list)) (exp \"in_2*\" (iter (var \"instr\") list)) (exp \"instr'*"
            "\" (iter (var \"instr\") list)) (exp (cat (list (case \"IF%%ELSE%\" (tup (var \"bt\") "
            "(iter (var \"in_1\") list (dom \"in_1\" (var \"in_1*\"))) (iter (var \"in_2\") list (d"
            "om \"in_2\" (var \"in_2*\")))))) (iter (var \"instr'\") list (dom \"instr'\" (var \"in"
            "str'*\"))))) (cat (call \"dataidx_instrs\" (exp (iter (var \"in_1\") list (dom \"in_1"
            "\" (var \"in_1*\"))))) (cat (call \"dataidx_instrs\" (exp (iter (var \"in_2\") list (d"
            "om \"in_2\" (var \"in_2*\"))))) (call \"dataidx_instrs\" (exp (iter (var \"instr'\") l"
            "ist (dom \"instr'\" (var \"instr'*\")))))))) (clause (exp \"instr\" (var \"instr\"))"

/-! ## The corrected script

`noncomputable` for the reason `Binary51.lean` gives: building the closed term
for a list of reflected `IL.Def`s this large makes Lean v4.35's LCNF boxing
pass panic.  Nothing here is run; the kernel *reduces* these values when it
checks `applyErrata_wasm20errata`, which `noncomputable` does not affect. -/

/-- The four errata of `#660` that are expressible as AST
patches, in issue order.  The four targets are pairwise distinct, so
`IL.applyErratum_comm` lets any two adjacent entries be swapped. -/
noncomputable def wasm20errata : List Erratum :=
  [wasm20.erratum670, wasm20.erratum671, wasm20.erratum672, wasm20.erratum673]

/-- `Specs.wasm20` with `#670`, `#671`, `#672` and `#673` applied: the
corrected wasm-2.0 specification.  Written out as the chain of
`IL.replaceDefs` that `applyErrata wasm20errata` reduces to, which
`applyErrata_wasm20errata` certifies. -/
noncomputable def wasm20corrected : Script :=
  replaceDefs wasm20.erratum673.corrected
    (replaceDefs wasm20.erratum672.corrected
      (replaceDefs wasm20.erratum671.corrected
        (replaceDefs wasm20.erratum670.corrected Specs.wasm20)))

/-- All four patches apply, and `wasm20corrected` is their result.

This is the statement that carries the content: `IL.Erratum.applies` holds for
each patch in turn, which says that its target is declared exactly once in the
script it is applied to, that its corrected definition declares that target,
and — through `IL.defEq`, hence through `IL.defS` — that the corrected
definition really differs from the one it replaces.  "Exactly these four
definitions change" is that last conjunct, four times; "and nowhere else" is
`wasm20Patch_eq_self` below. -/
theorem applyErrata_wasm20errata :
    applyErrata wasm20errata Specs.wasm20 = some wasm20corrected := by
  rfl

/-! ## What changed, and what did not -/

/-- The four patches, as the single function they apply to each top-level
definition of the pinned script. -/
noncomputable def wasm20Patch (d : Def) : Def :=
  replaceDef wasm20.erratum673.corrected
    (replaceDef wasm20.erratum672.corrected
      (replaceDef wasm20.erratum671.corrected
        (replaceDef wasm20.erratum670.corrected d)))

/-- The corrected script is the pinned one with `wasm20Patch` mapped over it:
the patches act on each top-level definition independently and in place. -/
theorem wasm20corrected_eq_map : wasm20corrected = Specs.wasm20.map wasm20Patch := by
  simp [wasm20corrected, wasm20Patch, replaceDefs_eq_map, List.map_map, Function.comp_def]

/-- **Nowhere else.**  A definition that declares none of `Binstr`, `Belem`,
`Bmodule` and `dataidx_instrs` — in any of `free.ml`'s namespaces, and at any
depth inside a `recD` group — comes through all four patches untouched.  With
`wasm20corrected_eq_map`, that is "the corrected script differs from the
pinned one only in those four definitions". -/
theorem wasm20Patch_eq_self {d : Def} (h₁ : countDef "Binstr" d = 0)
    (h₂ : countDef "Belem" d = 0) (h₃ : countDef "Bmodule" d = 0)
    (h₄ : countDef "dataidx_instrs" d = 0) : wasm20Patch d = d := by
  have e₁ := replaceDef_of_countDef_eq_zero
    (new := wasm20.erratum670.corrected) (x := "Binstr") rfl d h₁
  have e₂ := replaceDef_of_countDef_eq_zero
    (new := wasm20.erratum671.corrected) (x := "Belem") rfl d h₂
  have e₃ := replaceDef_of_countDef_eq_zero
    (new := wasm20.erratum672.corrected) (x := "Bmodule") rfl d h₃
  have e₄ := replaceDef_of_countDef_eq_zero
    (new := wasm20.erratum673.corrected) (x := "dataidx_instrs") rfl d h₄
  rw [wasm20Patch, e₁, e₂, e₃, e₄]

/-- The corrected script has the same 467 top-level definitions as the pinned
one. -/
theorem length_wasm20corrected : wasm20corrected.length = Specs.wasm20.length := by
  simp [wasm20corrected]

/-- The corrected script declares exactly the identifiers the pinned one
declares, in exactly the same namespaces (`spectec/src/il/free.ml:205-212`). -/
theorem boundDefs_wasm20corrected : boundDefs wasm20corrected = boundDefs Specs.wasm20 := by
  rw [wasm20corrected, boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs,
    boundDefs_replaceDefs]

/-! ## The patches, read back off the `Erratum` values -/

/-- Four issues, four patches: the four of `#660` that an AST patch can
express. -/
example : wasm20errata.map Erratum.issue = [670, 671, 672, 673] := by rfl

/-- The four definitions these errata correct. -/
example : wasm20errata.map Erratum.target = ["Binstr", "Belem", "Bmodule", "dataidx_instrs"] := by
  rfl

/-- Each corrected definition declares its target: three grammars and one
function, and the four are pairwise distinct — the hypothesis
`IL.applyErratum_comm` needs.  `Binstr` and `dataidx_instrs` both sit inside a
`recD` group in the pinned script, and `IL.replaceDefs` reaches into one. -/
example : wasm20errata.map (fun e => declKind? e.corrected) =
    [some (.gram, "Binstr"), some (.gram, "Belem"), some (.gram, "Bmodule"),
      some (.dec, "dataidx_instrs")] := by
  rfl

/-- Two patches with distinct targets commute, so the order in `wasm20errata`
is not load-bearing. -/
example : applyErrata [wasm20.erratum672, wasm20.erratum671] Specs.wasm20 =
    applyErrata [wasm20.erratum671, wasm20.erratum672] Specs.wasm20 :=
  (applyErrata_pair_comm (by decide) Specs.wasm20).symm

/-! ## #673, evaluated

Three of the four patches are legible as diffs: one numeral, one field, four
terminals.  `#673`'s is a reformulation, so it is worth *running*.
`Silmaril/SpecTec/Sem/Eval.lean`'s fuel-indexed evaluator takes a script and a
call straight to a `Sem.Value`, and the witness below is
`#673`'s V8 module stripped to the nesting that matters:
`(block (memory.init 0))`, whose only `memory.init` is one level deep.

`with_unfolding_all` is needed because `Sem.callDef` is one of a mutual block
the equation compiler seals; the proof term is still `rfl` and the kernel
still does the whole computation. -/

/-- The index `0`, as an `IL.Exp`.  `1-syntax.spectec:101` makes `idx` a
`u32`, `:28` makes `u32` a `uN(32)` and `:18-19` makes `uN(N)` the numeric
range `0 | ... | 2^N-1`, which SpecTec elaborates to a one-case variant whose
mixop renders `%` — the `(case "%" (tup (num (nat 0))))` that the pinned
`Belem` and `Binstr` productions are full of. -/
def idxZero : Exp := .caseE "%" (.tupE [.numE (.natN 0)])

/-- The instruction sequence `(block (memory.init 0))`, as an `IL.Exp` of type
`instr*`: one `BLOCK` (`1-syntax.spectec:400-401` for the `_RESULT valtype?`
block type) wrapping one `MEMORY.INIT`. -/
def nestedMemoryInit : Exp :=
  .listE [.caseE "BLOCK" (.tupE [.caseE "_RESULT" (.optE none),
    .listE [.caseE "MEMORY.INIT" idxZero]])]

/-- The same, with `LOOP` instead of `BLOCK` and a trailing `NOP`, so that the
new clause has to recurse into the body *and* carry on down the tail. -/
def nestedLoopMemoryInit : Exp :=
  .listE [.caseE "LOOP" (.tupE [.caseE "_RESULT" (.optE none),
    .listE [.caseE "MEMORY.INIT" idxZero]]), .caseE "NOP" (.tupE [])]

/-- `(if ... else (data.drop 0))`, for the third new clause: the index is in
the `else` branch, which is the second of `IF%%ELSE%`'s two sequences. -/
def nestedIfDataDrop : Exp :=
  .listE [.caseE "IF%%ELSE%" (.tupE [.caseE "_RESULT" (.optE none),
    .listE [], .listE [.caseE "DATA.DROP" idxZero]])]

/-- The data index `0` as a `Sem.Value`: what `idxZero` evaluates to. -/
def idxZeroV : Sem.Value := .case "%" (.tuple [.num (.natN 0)])

/-- **The defect.**  In the pinned script `$dataidx_instrs` reports *no* data
index for `(block (memory.init 0))`, so `A-binary.spectec:941`'s
`$dataidx_funcs(func*) = eps` holds for a module whose only `memory.init` is
nested and the data count section may be dropped. -/
example : Sem.callDef 100 (Sem.envOfScript Specs.wasm20) Sem.VarEnv.empty
    "dataidx_instrs" [.expA nestedMemoryInit] = .ok (.list []) := by
  with_unfolding_all rfl

/-- **The correction.**  In `wasm20corrected` the same call reports `0`. -/
example : Sem.callDef 100 (Sem.envOfScript wasm20corrected) Sem.VarEnv.empty
    "dataidx_instrs" [.expA nestedMemoryInit] = .ok (.list [idxZeroV]) := by
  with_unfolding_all rfl

/-- The `LOOP` clause fires, and the tail after the loop is still folded. -/
example : Sem.callDef 100 (Sem.envOfScript wasm20corrected) Sem.VarEnv.empty
    "dataidx_instrs" [.expA nestedLoopMemoryInit] = .ok (.list [idxZeroV]) := by
  with_unfolding_all rfl

/-- The `IF` clause fires, on the `else` branch. -/
example : Sem.callDef 100 (Sem.envOfScript wasm20corrected) Sem.VarEnv.empty
    "dataidx_instrs" [.expA nestedIfDataDrop] = .ok (.list [idxZeroV]) := by
  with_unfolding_all rfl

/-- Nothing else moves: a top-level `memory.init` reports `0` in both
scripts, so the correction only *adds* the indices the fold was missing. -/
example : Sem.callDef 100 (Sem.envOfScript Specs.wasm20) Sem.VarEnv.empty
    "dataidx_instrs" [.expA (.listE [.caseE "MEMORY.INIT" idxZero])] =
      .ok (.list [idxZeroV]) := by
  with_unfolding_all rfl

end Silmaril.SpecTec.IL.Wasm20
