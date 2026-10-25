module

public import Silmaril.Wasm.Text.Extensions.LegacyExceptions.RenderInstructions
public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.RenderInstructionsSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.LegacyExceptions

open Silmaril Silmaril.Formats.SExpEncoding Binaryen.Toolkit

theorem CatchesT.of_forall₂ {I : Core.IdCtx} {xs : List SExp}
    {cs : List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr)}
    (h : List.Forall₂ (CatchT I) xs cs) : CatchesT I xs cs := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons hc ih

theorem parts_sound (leaf : LeafRenderer)
    (hleaf : ∀ I i xs, leaf I i = some xs → LeafT I xs i) (fuel : Nat)
    {I : Core.IdCtx} {is : Wasm.Extensions.LegacyExceptions.Expr} {parts : List (List SExp)}
    (h : is.mapM (Structured.instructionTreeFuel? leaf fuel I) = some parts) :
    InstrsT I parts.flatten is :=
  Structured.InstrsT.of_forall₂ (Structured.mapM_sound
    (fun i xs hi => Structured.instructionTreeFuel?_sound leaf hleaf fuel (i := i) (xs := xs) hi) h)

theorem catchSyntaxFuel?_sound (leaf : LeafRenderer)
    (hleaf : ∀ I i xs, leaf I i = some xs → LeafT I xs i) (fuel : Nat)
    {I : Core.IdCtx} {c : TagIdx × Wasm.Extensions.LegacyExceptions.Expr} {x : SExp}
    (h : catchSyntaxFuel? leaf fuel I c = some x) : CatchT I x c := by
  unfold catchSyntaxFuel? at h
  obtain ⟨tag, ht, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact .mk (Wat.indexSyntax?_sound ht _) (parts_sound leaf hleaf fuel hp)

theorem finalSyntaxFuel?_sound (leaf : LeafRenderer)
    (hleaf : ∀ I i xs, leaf I i = some xs → LeafT I xs i) (fuel : Nat)
    {I : Core.IdCtx} {all : Option Wasm.Extensions.LegacyExceptions.Expr} {xs : List SExp}
    (h : finalSyntaxFuel? leaf fuel I all = some xs) : FinalT I xs all := by
  cases all with
  | none => cases h; exact .none
  | some is =>
    simp only [finalSyntaxFuel?] at h
    obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .catchAll (parts_sound leaf hleaf fuel hp)

theorem leafSyntaxFuel?_sound (fuel : Nat) {I : Core.IdCtx}
    {i : Wasm.Extensions.LegacyExceptions.Leaf} {xs : List SExp}
    (h : leafSyntaxFuel? fuel I i = some xs) : LeafT I xs i := by
  induction fuel generalizing I i xs with
  | zero => cases h
  | succ fuel ih =>
    have hrec : ∀ I i xs, leafSyntaxFuel? fuel I i = some xs → LeafT I xs i :=
      fun I i xs h => ih (I := I) (i := i) (xs := xs) h
    cases i <;> simp only [leafSyntaxFuel?] at h
    case base i => exact .base (BinaryenMemory.leafSyntax?_sound h)
    case rethrow label =>
      obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .rethrow (Wat.indexSyntax?_sound hi _)
    case try_ type body catches all =>
      obtain ⟨header, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨cs, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨fs, hf, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .try_ (Wat.blockTypeSyntaxAt?_sound ht)
        (parts_sound _ hrec fuel hp)
        (CatchesT.of_forall₂ (Structured.mapM_sound (fun c x hx => catchSyntaxFuel?_sound _ hrec fuel (c := c) (x := x) hx) hc))
        (finalSyntaxFuel?_sound _ hrec fuel hf)
    case delegate type body label =>
      obtain ⟨header, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .delegate (Wat.blockTypeSyntaxAt?_sound ht) (parts_sound _ hrec fuel hp)
        (Wat.indexSyntax?_sound hi _)

theorem leafSyntax?_sound {I : Core.IdCtx} {i : Wasm.Extensions.LegacyExceptions.Leaf} {xs : List SExp}
    (h : leafSyntax? I i = some xs) : LeafT I xs i := leafSyntaxFuel?_sound _ h

theorem instructionTree?_sound {I : Core.IdCtx} {i : Wasm.Extensions.LegacyExceptions.Instr} {xs : List SExp}
    (h : instructionTree? I i = some xs) : InstrT I xs i :=
  Structured.instructionTree?_sound leafSyntax? (fun _ _ _ h => leafSyntax?_sound h) h

end Silmaril.Wasm.Text.Extensions.LegacyExceptions
