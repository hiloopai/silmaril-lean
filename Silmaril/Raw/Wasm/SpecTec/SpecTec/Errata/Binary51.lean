module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The wasm-3.0 binary §5.1 errata

The three verified errata of `#650`, as patches on
`Silmaril.SpecTec.Specs.wasm30`.  Each is a minimal textual edit of one
definition's own `--ast` rendering, written out by `spectec_erratum`
(`Silmaril/SpecTec/Errata.lean`) so that a reader sees exactly what changed.

| issue | upstream line | definitions patched |
| --- | --- | --- |
| #654 | `5.1-binary.values.spectec:31-32` | `Bi32`, `Bi64` |
| #655 | `5.1-binary.values.spectec:49` | `cont` |
| #656 | `5.1-binary.values.spectec:63` | `utf8` |

All line numbers are in
`specification/wasm-3.0/5.1-binary.values.spectec` at the pin
`608711107b7f1edb13efd57b7d79b49477462d36` (SHA-256
`7bdb1686c6fa9be9b67542b38e5be0537a29a44d48fb6b51f33b5a43b0f72d69`, the value
`specs/spectec/manifest.json` records).

`spectec_import` adds `Specs.wasm30` with `Lean.addDecl`, which bypasses the
`@[expose]` of the section it sits in, so the constant's *value* is not visible
to an importing module: neither the elaborator's `(← getEnv).find?` nor the
kernel can unfold it.  The two `import all` lines above are what Lean's own
diagnostic prescribes for that, and they are why `applyErrata_binary51` below
is a `rfl` the kernel can actually do.

**Three issues, four patches.**  `#654` is one defect reported once but spelled
twice in the source — `grammar Bi32 : i32 = BuN(32)` and
`grammar Bi64 : i64 = BuN(64)` — and an `IL.Erratum` carries exactly one
corrected definition, so it becomes two patches with the same `issue` number.
The optional `as` clause of `spectec_erratum` names them apart.

## How each edit was checked

The patches here were written against the printed form, which is a derived
artifact.  Each one was *also* checked against the source: the three edits were
applied to a copy of `specification/wasm-3.0/`, the official frontend was re-run
over it at the pin with the same `--ast-width 80` and the same file order as
`specs/spectec/manifest.json`, and the resulting stream was diffed against the
pinned one.  The diff is exactly four definitions — `cont`, `utf8`, `Bi32`,
`Bi64` — and in each one the corrected definition is byte-for-byte what the
`replacing`/`with` pair below produces.  The unpatched run reproduces
`specs/spectec/wasm-3.0.ast` byte for byte, so the comparison is sound.

`#654` is the one whose elaborated consequence is not obvious from the source
diff: changing the right-hand side from `BuN(32)` to `BiN(32)` also changes the
type SpecTec infers for the implicit production result, from `uN(32)` to
`iN(32)`, and both appear in the printed form.  The re-run confirms both.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL.Binary51

set_option maxRecDepth 100000

/-! ## #654 — `Bi32`/`Bi64` use unsigned LEB128 where they should use signed

`5.1-binary.values.spectec:31-32` reads

```
grammar Bi32 : i32 = BuN(32)
grammar Bi64 : i64 = BuN(64)
```

where `BuN` (`:9-11`) is the *unsigned* LEB128 grammar.  The signed one is
`BiN` (`:18-19`), which is defined and then used by nothing.  The type checker
cannot catch this because `1.1-syntax.values.spectec:14-15` makes `iN(N)` an
alias of `uN(N)`.  The consequence is that `i32.const`/`i64.const` immediates
(`5.3-binary.instructions.spectec:191-193`) decode as unsigned, so `41 7F` is
`i32.const 127` rather than `i32.const -1`.

The printed form carries both halves of the correction: the production's
implicit result is declared at `uN(32)` and bound to `BuN(32)`, and the
corrected one is declared at `iN(32)` and bound to `BiN(32)`. -/

spectec_erratum 654 in Specs.wasm30 on "Bi32"
  because "5.1-binary.values.spectec:31 reads `grammar Bi32 : i32 = BuN(32)`, the unsigned "
          "LEB128 grammar; it should be `BiN(32)`, the signed one (BiN is defined at :18-19 "
          "and otherwise unused), so that i32.const immediates decode as signed"
  replacing "(var \"uN\" (exp (num (nat 32))))) (attr "
            "(var \"<implicit-prod-result>\") (var \"BuN\""
  with      "(var \"iN\" (exp (num (nat 32))))) (attr "
            "(var \"<implicit-prod-result>\") (var \"BiN\""
  as erratum654Bi32

spectec_erratum 654 in Specs.wasm30 on "Bi64"
  because "5.1-binary.values.spectec:32 reads `grammar Bi64 : i64 = BuN(64)`, the unsigned "
          "LEB128 grammar; it should be `BiN(64)`, the signed one (BiN is defined at :18-19 "
          "and otherwise unused), so that i64.const immediates decode as signed"
  replacing "(var \"uN\" (exp (num (nat 64))))) (attr "
            "(var \"<implicit-prod-result>\") (var \"BuN\""
  with      "(var \"iN\" (exp (num (nat 64))))) (attr "
            "(var \"<implicit-prod-result>\") (var \"BiN\""
  as erratum654Bi64

/-! ## #655 — `$cont` excludes the continuation byte `0x80`

`5.1-binary.values.spectec:49` reads

```
def $cont(b) = $(b - 0x80) -- if (0x80 < b < 0xC0)
```

A UTF-8 continuation byte is `10xxxxxx`, i.e. `0x80..0xBF`, so the lower bound
has to be inclusive.  Read literally, `$utf8(ch)` is undefined for every scalar
value whose encoding contains a `0x80` continuation byte — 50 323 of them,
including U+0400, U+2014 and U+10000.

The printed form elaborates `0x80 < b` to `(cmp lt nat (num (nat 128)) …)`;
the fragment below is the only `lt` in the definition with `128` on the left,
the other comparison being `b < 0xC0`. -/

spectec_erratum 655 in Specs.wasm30 on "cont"
  because "5.1-binary.values.spectec:49 reads `-- if (0x80 < b < 0xC0)`; UTF-8 continuation "
          "bytes are 10xxxxxx, that is 0x80..0xBF, so the lower bound must be `0x80 <= b`"
  replacing "(cmp lt nat (num (nat 128))"
  with      "(cmp le nat (num (nat 128))"

/-! ## #656 — the four-byte UTF-8 range ends at U+11000

`5.1-binary.values.spectec:63` reads

```
  -- if U+10000 <= ch < U+11000
```

inside the four-byte clause of `$utf8`.  The bound is missing a hex digit: it
should be `U+110000`, which is what the 1.0 REC, the 2.0 CR snapshot, the
reference interpreter and the test suite all use.  Read literally, every scalar
value from U+11000 to U+10FFFF — 93.9% of Unicode, all emoji among them — has
no encoding in either the binary or the text format.

`0x11000` is `69632` and `0x110000` is `1114112`; `69632` occurs once in the
printed `utf8`, in exactly that premise. -/

spectec_erratum 656 in Specs.wasm30 on "utf8"
  because "5.1-binary.values.spectec:63 reads `-- if U+10000 <= ch < U+11000` in the "
          "four-byte clause of $utf8; the bound is one hex digit short and should be U+110000"
  replacing "(num (nat 69632))"
  with      "(num (nat 1114112))"

/-! ## The corrected script

The three definitions below are `noncomputable` only to avoid a compiler bug:
building the closed term for a list of reflected `IL.Def`s this large makes
Lean v4.35's LCNF boxing pass panic (`unknown join point 'block_0'`).  Nothing
here is ever run — the kernel *reduces* these values when it checks
`applyErrata_binary51`, which `noncomputable` does not affect. -/

/-- The three errata of `#650`, as the four patches they
spell out.  The order is irrelevant: the four targets are pairwise distinct, so
`IL.applyErratum_comm` lets any two adjacent entries be swapped. -/
noncomputable def binary51 : List Erratum :=
  [wasm30.erratum654Bi32, wasm30.erratum654Bi64, wasm30.erratum655, wasm30.erratum656]

/-- `Specs.wasm30` with `#654`, `#655` and `#656` applied: the corrected
wasm-3.0 specification.  Written out as the chain of `IL.replaceDefs` that
`applyErrata binary51` reduces to, which `applyErrata_binary51` certifies. -/
noncomputable def wasm30binary51 : Script :=
  replaceDefs wasm30.erratum656.corrected
    (replaceDefs wasm30.erratum655.corrected
      (replaceDefs wasm30.erratum654Bi64.corrected
        (replaceDefs wasm30.erratum654Bi32.corrected Specs.wasm30)))

/-- All four patches apply, and `wasm30binary51` is their result.

This is the one statement here that the kernel has to *compute*, and it is the
one that carries the content: `IL.Erratum.applies` holds for each patch in
turn, which says that its target is declared exactly once in the script it is
applied to, that its corrected definition declares that target, and — through
`IL.defEq`, hence through `IL.defS` — that the corrected definition really
differs from the one it replaces.  "Exactly these four definitions change" is
that last conjunct, four times; "and nowhere else" is
`binary51Patch_eq_self` below, which needs no computation at all. -/
theorem applyErrata_binary51 :
    applyErrata binary51 Specs.wasm30 = some wasm30binary51 := by
  rfl

/-! ## What changed, and what did not -/

/-- The four patches, as the single function they apply to each top-level
definition of the pinned script. -/
noncomputable def binary51Patch (d : Def) : Def :=
  replaceDef wasm30.erratum656.corrected
    (replaceDef wasm30.erratum655.corrected
      (replaceDef wasm30.erratum654Bi64.corrected
        (replaceDef wasm30.erratum654Bi32.corrected d)))

/-- The corrected script is the pinned one with `binary51Patch` mapped over it:
the patches act on each top-level definition independently and in place. -/
theorem wasm30binary51_eq_map : wasm30binary51 = Specs.wasm30.map binary51Patch := by
  simp [wasm30binary51, binary51Patch, replaceDefs_eq_map, List.map_map, Function.comp_def]

/-- **Nowhere else.**  A definition that declares none of `Bi32`, `Bi64`,
`cont` and `utf8` — in any of `free.ml`'s namespaces, and at any depth inside a
`recD` group — comes through all four patches untouched.  With
`wasm30binary51_eq_map`, that is "the corrected script differs from the pinned
one only in those four definitions". -/
theorem binary51Patch_eq_self {d : Def} (h₁ : countDef "Bi32" d = 0)
    (h₂ : countDef "Bi64" d = 0) (h₃ : countDef "cont" d = 0)
    (h₄ : countDef "utf8" d = 0) : binary51Patch d = d := by
  have e₁ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum654Bi32.corrected) (x := "Bi32") rfl d h₁
  have e₂ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum654Bi64.corrected) (x := "Bi64") rfl d h₂
  have e₃ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum655.corrected) (x := "cont") rfl d h₃
  have e₄ := replaceDef_of_countDef_eq_zero
    (new := wasm30.erratum656.corrected) (x := "utf8") rfl d h₄
  rw [binary51Patch, e₁, e₂, e₃, e₄]

/-- The corrected script has the same 976 top-level definitions as the pinned
one. -/
theorem length_wasm30binary51 : wasm30binary51.length = Specs.wasm30.length := by
  simp [wasm30binary51]

/-- The corrected script declares exactly the identifiers the pinned one
declares, in exactly the same namespaces (`spectec/src/il/free.ml:205-212`). -/
theorem boundDefs_wasm30binary51 : boundDefs wasm30binary51 = boundDefs Specs.wasm30 := by
  rw [wasm30binary51, boundDefs_replaceDefs, boundDefs_replaceDefs, boundDefs_replaceDefs,
    boundDefs_replaceDefs]

/-! ## The patches, read back off the `Erratum` values -/

/-- Three issues, four patches. -/
example : binary51.map Erratum.issue = [654, 654, 655, 656] := by rfl

/-- The four definitions `#650` corrects. -/
example : binary51.map Erratum.target = ["Bi32", "Bi64", "cont", "utf8"] := by rfl

/-- Each corrected definition declares its target, two in the grammar
namespace and two in the function namespace, and the four are pairwise
distinct — which is the hypothesis `IL.applyErratum_comm` needs. -/
example : binary51.map (fun e => declKind? e.corrected) =
    [some (.gram, "Bi32"), some (.gram, "Bi64"), some (.dec, "cont"),
      some (.dec, "utf8")] := by
  rfl

/-- Two patches with distinct targets commute, so the order in `binary51` is
not load-bearing. -/
example : applyErrata [wasm30.erratum655, wasm30.erratum654Bi32] Specs.wasm30 =
    applyErrata [wasm30.erratum654Bi32, wasm30.erratum655] Specs.wasm30 :=
  (applyErrata_pair_comm (by decide) Specs.wasm30).symm

end Silmaril.SpecTec.IL.Binary51
