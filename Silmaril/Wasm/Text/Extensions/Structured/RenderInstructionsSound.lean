module

public import Silmaril.Wasm.Text.Extensions.Structured.RenderInstructions
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

theorem mapM_sound {α β : Type} {f : α → Option β} {R : β → α → Prop}
    (hf : ∀ a b, f a = some b → R b a) :
    ∀ {as bs}, as.mapM f = some bs → List.Forall₂ R bs as := by
  intro as
  induction as with
  | nil => intro bs h; cases h; exact .nil
  | cons a as ih =>
    intro bs h
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs', hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .cons (hf a b hb) (ih hbs)

theorem InstrsT.of_forall₂ {Leaf : Type} {G : Core.IdCtx → List SExp → Leaf → Prop}
    {I : Core.IdCtx} {xs : List (List SExp)} {is : Wasm.Extensions.Structured.Expr Leaf}
    (h : List.Forall₂ (InstrT G I) xs is) : InstrsT G I xs.flatten is := by
  induction h with
  | nil => exact .nil
  | cons hi _ ih => exact .cons hi ih

theorem instructionTreeFuel?_sound {Leaf : Type} {G : Core.IdCtx → List SExp → Leaf → Prop}
    (leaf : Core.IdCtx → Leaf → Option (List SExp))
    (hleaf : ∀ I i xs, leaf I i = some xs → G I xs i) (fuel : Nat)
    {I : Core.IdCtx} {i : Wasm.Extensions.Structured.Instr Leaf} {xs : List SExp}
    (h : instructionTreeFuel? leaf fuel I i = some xs) : InstrT G I xs i := by
  induction fuel generalizing i I xs with
  | zero => cases h
  | succ fuel ih =>
    cases i <;> simp only [instructionTreeFuel?] at h
    case leaf i => exact .leaf (hleaf I i xs h)
    case block t body =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .block (Wat.blockTypeSyntaxAt?_sound hh)
        (.of_forall₂ (mapM_sound (fun i xs hx => ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hp))
    case loop t body =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .loop (Wat.blockTypeSyntaxAt?_sound hh)
        (.of_forall₂ (mapM_sound (fun i xs hx => ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hp))
    case if_ t a b =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨left, hl, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨right, hr, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .if_ (Wat.blockTypeSyntaxAt?_sound hh)
        (.of_forall₂ (mapM_sound (fun i xs hx => ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hl))
        (.of_forall₂ (mapM_sound (fun i xs hx => ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hr))
    case tryTable t catches body =>
      obtain ⟨header, hh, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨cs, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨parts, hp, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .tryTable (Wat.blockTypeSyntaxAt?_sound hh)
        (mapM_sound (fun _ _ hx => Wat.catchSyntax?_sound hx I) hc)
        (.of_forall₂ (mapM_sound (fun i xs hx => ih (I := { I with labels := none :: I.labels }) (i := i) (xs := xs) hx) hp))

theorem instructionTree?_sound {Leaf : Type} {G : Core.IdCtx → List SExp → Leaf → Prop}
    (leaf : Core.IdCtx → Leaf → Option (List SExp))
    (hleaf : ∀ I i xs, leaf I i = some xs → G I xs i)
    {I : Core.IdCtx} {i : Wasm.Extensions.Structured.Instr Leaf} {xs : List SExp}
    (h : instructionTree? leaf I i = some xs) : InstrT G I xs i :=
  instructionTreeFuel?_sound leaf hleaf _ h

end Silmaril.Wasm.Text.Extensions.Structured
