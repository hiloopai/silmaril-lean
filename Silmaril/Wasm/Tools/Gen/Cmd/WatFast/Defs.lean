module

public import Silmaril.Wasm.Binaryen.Toolkit.WatSource

/-!
# A faster copy of silmaril's certified WAT module elaborator

silmaril's `Binaryen.Toolkit.Wat.Source.module?` elaborates every function field under the
module's identifier context `I` extended by the function's parameters and locals, and checks
`IdCtx.Ok` of the extended context: that the names of *every* index space are pairwise
distinct (a `List.Nodup`, quadratic). With `F` named functions that is `F` quadratic checks of
the whole module's names; on the 1.9 MB text of a module with 813 named functions it is 15 s
of the 19 s `mutate` spends reading the text.

Here the module-level check is made once per elaboration pass (`I.Ok`), and each function
checks only that its locals are distinct from each other and from `I.locals`
(`Distinct (I.locals ++ L)`); `ok_locals` shows that this gives the same `IdCtx.Ok` of the
extended context, so the certificates are silmaril's own (`DeclT`, `ModuleT`). When the
module-level check fails, the original `field?` is used.

* `funcF?`, `WithUses.funcF?`: silmaril's `func?` and `WithUses.func?` with that check;
* `fieldF?`: silmaril's `field?` dispatching to them;
* `moduleF?`: silmaril's `module?` with `fieldF?` in both passes when the pass's context is
  `Ok`;
* `parseF?`: silmaril's `parseSupported?` (canonical fast path first) with `moduleF?`.

`Thms`: `funcF?_eq`, `fieldF?_eq`, `moduleF?_eq`, `parseF?_eq` (**equal** to silmaril's
functions), so `parseF?_sound` (the module is one the text grammar gives the tree).

New definitions; the bodies are copies of silmaril's (`WatSource.lean`) with the check
replaced.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.WatFast

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (toList? doc)
open Text.Core
open Silmaril.Wasm.Binaryen.Toolkit.Wat
open Silmaril.Wasm.Binaryen.Toolkit.Wat.Source

/-- Extending an `Ok` context by locals keeps it `Ok` exactly when the locals (with the
context's own) are distinct. -/
theorem ok_locals_iff {I : IdCtx} (hI : I.Ok) (L : List (Option String)) :
    (I ++ ({ locals := L } : IdCtx)).Ok ↔ Distinct (I.locals ++ L) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h10, h11⟩ := hI
  change (IdCtx.append I { locals := L }).Ok ↔ _
  simp only [IdCtx.Ok, IdCtx.append, List.append_nil]
  exact ⟨fun h => h.2.2.2.2.2.2.2.2.1,
    fun h => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h, h10, h11⟩⟩

/-- silmaril's `func?`, deciding `I'.Ok` from `I.Ok` by the locals alone. -/
def funcF? (I : IdCtx) (hI : I.Ok) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "func" x
  let ns ← exports? h.exports
  let tu ← typeUse? I h
  let ls ← concat? (local? I) h.locals
  let I' := I ++ { locals := tu.parameters ++ ls.1.map Prod.snd }
  have : Decidable I'.Ok :=
    decidable_of_iff _ (ok_locals_iff hI (tu.parameters ++ ls.1.map Prod.snd)).symm
  if hok : I'.Ok then do
    let e ← expr? I' h.body
    if hx : x = L (.atom (.sym "func") :: (idSyntax h.name ++ h.exports ++
        h.typeSyntax ++ h.locals ++ h.body)) then
      some ⟨(.func ⟨tu.index, ls.1.map Prod.fst, e.1⟩ :: selfExports ns.1,
        { funcs := [h.name] }, tu.uses), by
        rw [hx]
        simpa using DeclT.func (idSyntax_sound h.name) ns.2 tu.sound ls.2 hok e.2⟩
    else none
  else none

/-- silmaril's `WithUses.func?`, deciding `I'.Ok` from `I.Ok` by the locals alone. -/
def WithUses.funcF? (I : IdCtx) (hI : I.Ok) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} := do
  let h ← header? "func" x
  let ns ← exports? h.exports
  let tu ← typeUse? I h
  let ls ← concat? (local? I) h.locals
  let I' := I ++ { locals := tu.parameters ++ ls.1.map Prod.snd }
  have : Decidable I'.Ok :=
    decidable_of_iff _ (ok_locals_iff hI (tu.parameters ++ ls.1.map Prod.snd)).symm
  if hok : I'.Ok then do
    let e ← Source.WithUses.expr? I' h.body
    if hx : x = L (.atom (.sym "func") :: (idSyntax h.name ++ h.exports ++
        h.typeSyntax ++ h.locals ++ h.body)) then
      some ⟨(.func ⟨tu.index, ls.1.map Prod.fst, e.value⟩ :: selfExports ns.1,
        { funcs := [h.name] }, tu.uses ++ e.uses), by
        rw [hx]
        simpa using DeclT.func (idSyntax_sound h.name) ns.2 tu.sound ls.2 hok e.sound⟩
    else none
  else none

/-- silmaril's `field?` with `funcF?` for function fields (the other fields are elaborated by
`field?` itself). -/
def fieldF? (I : IdCtx) (hI : I.Ok) (x : SExp) :
    Option {out : FieldOut // DeclT I x out.1 out.2.1 out.2.2} :=
  match toList? x with
  | some (.atom (.sym "func") :: _) =>
      (inlineImportField? I x).orElse fun _ =>
        (funcF? I hI x).orElse fun _ => WithUses.funcF? I hI x
  | _ => field? I x

/-- One elaboration pass over the fields: `fieldF?` when the context is `Ok` (checked once),
silmaril's `field?` otherwise. -/
def fieldsF? (I : IdCtx) (fields : List SExp) :
    Option {outs : List FieldOut // List.Forall₂ (fun x out => DeclT I x out.1 out.2.1 out.2.2)
      fields outs} :=
  if hI : I.Ok then mapCertified (fieldF? I hI) fields else mapCertified (field? I) fields

/-- silmaril's `module?` with `fieldsF?` for both passes. -/
def moduleF? (x : SExp) : Option {m : Wasm.Module // ModuleT x m} := do
  let source ← moduleFields? x
  let fields := source.1
  let names : IdCtx := { types := fields.flatMap rawTypeNames }
  let hints := fields.map (fieldHintAt names)
  let J := IdCtx.concat (hints.map Prod.fst)
  let implicit := implicitTypes J.typedefs (hints.flatMap Prod.snd)
  let provisional := J ++ implicitCtx implicit
  let first ← fieldsF? provisional fields
  let refined := IdCtx.concat (first.1.map (·.2.1))
  let actualUses := first.1.flatMap (·.2.2)
  let I := refined ++ implicitCtx (implicitTypes refined.typedefs actualUses)
  let outs ← fieldsF? I fields
  let J' := IdCtx.concat (outs.1.map (·.2.1))
  let ds := outs.1.flatMap (·.1)
  let implicit' := implicitTypes J'.typedefs (outs.1.flatMap (·.2.2))
  if hI : I = J' ++ implicitCtx implicit' then
    if hok : I.Ok then
      if ho : orderedAfter false ds = true then
        if hs : startCount ds ≤ 1 then
          some ⟨build (resolve ds) implicit', by
            exact ⟨fields, outs.1, I, source.2, outs.2,
              hI, hok, (orderedAfter_sound ho).1, hs, rfl⟩⟩
        else none
      else none
    else none
  else none

/-- silmaril's `parseSupported?` (canonical fast path, then source elaboration) with
`moduleF?`. -/
def parseF? (x : Text.SExp) : Option Wasm.Module :=
  match parseCanonical? x with
  | some m => some m
  | none => (moduleF? x).map Subtype.val

end Silmaril.Wasm.Tools.Gen.Cmd.WatFast
