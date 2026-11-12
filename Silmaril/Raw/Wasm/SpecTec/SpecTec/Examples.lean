module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Encoding

/-!
# Inline snippets, and what the kernel can and cannot reduce

`spectec_sexp%` and `spectec_def%` quote a fragment of an `--ast` stream as a
`SExp` and as an `IL.Def`, both with *literal* atoms.  That makes this file the
place where the literal certificate is actually checked by the kernel.

Two facts about reduction shape everything here and in
`Silmaril/SpecTec/Import.lean`:

* **Printing reduces.**  `defS d = s` is a `rfl` the kernel can do:
  `Escape.quote` is phrased over `String.utf8EncodeChar` and `IL.Digits` uses
  explicit fuel, so both unfold.  It is not cheap — Lean v4.35's `String` is
  UTF-8/`ByteArray` backed, so each character costs real work — but it is
  linear and fine at this scale.
* **Decoding does not reduce.**  `Escape.unquote?` ends in
  `Silmaril.Unicode.utf8?`, i.e. `String.fromUTF8?`, which is opaque to the
  kernel; `decodeDef? s = some d` by `rfl` does not terminate.  It does not
  need to: `defS d = s` plus the general theorem `decodeDef?_defS` gives the
  decoding certificate with no computation at all, which is exactly the
  mechanism `spectec_import` uses for a whole 1.5 MB stream.

The snippets are taken verbatim from `specs/spectec/wasm-1.0.ast` and
`specs/spectec/wasm-3.0.ast`.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL.Examples

open Silmaril.SpecTec (SExp)

/-- A nullary variant: `MUT` from `specs/spectec/wasm-1.0.ast`. -/
def mutSExp : SExp := spectec_sexp% "(typ \"MUT\" (inst (variant (case \"MUT\" (tup)))))"

/-- The same definition, decoded at elaboration time. -/
def mutDef : Def := spectec_def% "(typ \"MUT\" (inst (variant (case \"MUT\" (tup)))))"

example : mutDef = .typD "MUT" [] [.instD [] [] (.variantT [.mk "MUT" (.tupT []) [] []])] := by
  rfl

/-- The literal certificate: printing the decoded definition reproduces the
S-expression that was read, atom for atom. -/
theorem defS_mutDef : defS mutDef = mutSExp := by rfl

/-- …from which decoding it back is free. -/
example : decodeDef? mutSExp = some mutDef := defS_mutDef ▸ decodeDef?_defS mutDef

/-- An alias with a numeric type. -/
def natSExp : SExp := spectec_sexp% "(typ \"N\" (inst (alias nat)))"

example : defS (spectec_def% "(typ \"N\" (inst (alias nat)))") = natSExp := by rfl

/-- A definition with a parameter, a clause and a premise. -/
def sizeSExp : SExp :=
  spectec_sexp% "(def \"size\" (exp \"valtype\" (var \"valtype\")) nat
    (clause (exp \"valtype\" (var \"valtype\")) (exp (var \"valtype\")) (num (nat 32))
      (if (cmp eq bool (var \"valtype\") (case \"I32\" (tup))))))"

/-- The same definition. -/
def sizeDef : Def :=
  spectec_def% "(def \"size\" (exp \"valtype\" (var \"valtype\")) nat
    (clause (exp \"valtype\" (var \"valtype\")) (exp (var \"valtype\")) (num (nat 32))
      (if (cmp eq bool (var \"valtype\") (case \"I32\" (tup))))))"

/-- A `param`/`arg` prefix, a tail and a premise all round-trip. -/
theorem defS_sizeDef : defS sizeDef = sizeSExp := by rfl

example : decodeDef? sizeSExp = some sizeDef := defS_sizeDef ▸ decodeDef?_defS sizeDef

/-- A grammar production with a byte terminal. -/
def byteSExp : SExp := spectec_sexp% "(gram \"Bbyte\" nat (prod (num 0x0B) (num (nat 11))))"

/-- The same definition. -/
def byteDef : Def := spectec_def% "(gram \"Bbyte\" nat (prod (num 0x0B) (num (nat 11))))"

theorem defS_byteDef : defS byteDef = byteSExp := by rfl

/-- A `0x%02X` terminal wider than two digits, as the UTF-8 productions of
`specs/spectec/wasm-3.0.ast` use: `%02X` is a minimum width, not a bound. -/
def highSExp : SExp := spectec_sexp% "(gram \"Bhigh\" nat (prod (num 0x10FFFF) (num (nat 1))))"

/-- The same definition. -/
def highDef : Def := spectec_def% "(gram \"Bhigh\" nat (prod (num 0x10FFFF) (num (nat 1))))"

example : highDef =
    .gramD "Bhigh" [] (.numT .natT) [.prodD [] (.numG 0x10FFFF) (.numE (.natN 1)) []] := by
  rfl

theorem defS_highDef : defS highDef = highSExp := by rfl

/-- The encoding relation holds of each snippet, by definition. -/
example : defRel mutSExp mutDef := defS_mutDef

example : defRel sizeSExp sizeDef := defS_sizeDef

example : defRel byteSExp byteDef := defS_byteDef

example : defRel highSExp highDef := defS_highDef

/-- The general theorems specialize with no computation. -/
example : decodeDef? (defS sizeDef) = some sizeDef := decodeDef?_defS sizeDef

end Silmaril.SpecTec.IL.Examples
