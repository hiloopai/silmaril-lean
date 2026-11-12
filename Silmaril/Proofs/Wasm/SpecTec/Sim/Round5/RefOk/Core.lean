module

public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Defs

/-!
# Round 5: Core's side of the counterexamples

* `refOk_nullAny`: Core types `null` at `REF NULL ANY`, by `RefOk.sub` from `RefOk.null`.
* `refOk_null_inv`: Core types `null` only at `REF NULL BOT` or at a type valid in `{}`.
* `not_tyOk_nested`: the nested type is not valid in `{}`. Core's `Deftype_ok` checks a group
  under `Δ.withRecs subs`, which replaces `RECS`, so the inner `REC 1` finds no subtype.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.RefOk

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `REF NULL ANY` is valid in the empty context. -/
theorem tyOk_nullAny : TyOk {} nullAny := .ref (.abs .any)

/-- `REF NULL ANY` is bounded. -/
theorem tyBnd_nullAny : Round4.tyBnd nullAny = true := rfl

/-- **Core types `null` at `REF NULL ANY`**, in every store. -/
theorem refOk_nullAny (s : Store H) : RefOk s .null nullAny :=
  .sub .null tyOk_nullAny (.refNull .bot)

/-- **Core types `null` at `REF NULL BOT`, or at a type valid in `{}`.** -/
theorem refOk_null_inv {s : Store H} {rt : CRefType} (h : RefOk s .null rt) :
    rt = .ref true .bot ∨ TyOk {} rt := by
  generalize hr : Ref.null = r at h
  induction h with
  | null => exact .inl rfl
  | sub _ hok _ _ => exact .inr hok
  | _ => cases hr

/-- A valid `REF null? (deftype)` has a valid defined type. -/
theorem tyOk_refDt_inv {Δ : TypeCtx} {n : Bool} {d : DefType}
    (h : TyOk Δ (Ty.ref n (.use (.dt d)))) : TyOk Δ d := by
  cases h with | ref h =>
  cases h with | use h =>
  cases h with | dt h => exact h

/-- A valid one-member group whose member is a parentless one-field structure of a reference:
the reference is valid under the group's own `RECS` (`withRecs`). -/
theorem tyOk_oneRef_inv {Δ : TypeCtx} {fin : Bool} {m : Mutability} {r : CRefType}
    (h : TyOk Δ (Ty.defn (.group (.cons (.sub fin .nil (.struct (.cons (.field m (.val (.refv r)))
      .nil))) .nil)) 0)) :
    TyOk (Δ.withRecs [.sub fin .nil (.struct (.cons (.field m (.val (.refv r))) .nil))]) r := by
  cases h with | defn h _ =>
  cases h with | cons h _ =>
  cases h with | noSuper h =>
  cases h with | struct h =>
  cases h with | cons h _ =>
  cases h with | field h =>
  cases h with | val h =>
  cases h with | refv h => exact h

/-- A valid `REF null? (REC i)` finds a subtype at `RECS[i]`. -/
theorem tyOk_refRecv_inv {Δ : TypeCtx} {n : Bool} {i : Nat}
    (h : TyOk Δ (Ty.ref n (.use (.recv i)))) : ∃ st, Δ.recs[i]? = some st := by
  cases h with | ref h =>
  cases h with | use h =>
  cases h with | recv h => exact ⟨_, h⟩

/-- **The nested type is not valid in `{}`**: inside `D_in`, Core's `RECS` is `[stIn]`, so
`REC 1` is unbound. -/
theorem not_tyOk_nested : ¬ TyOk {} nestedRT := fun h =>
  have h₁ : TyOk {} dOut := tyOk_refDt_inv h
  have h₂ : TyOk (TypeCtx.withRecs {} [stOut]) (Ty.ref true (.use (.dt dIn))) :=
    tyOk_oneRef_inv h₁
  have h₃ : TyOk (TypeCtx.withRecs {} [stOut]) dIn := tyOk_refDt_inv h₂
  have h₄ : TyOk ((TypeCtx.withRecs {} [stOut]).withRecs [stIn]) (Ty.ref true (.use (.recv 1))) :=
    tyOk_oneRef_inv h₃
  have h₅ : ∃ st, ((TypeCtx.withRecs {} [stOut]).withRecs [stIn]).recs[1]? = some st :=
    tyOk_refRecv_inv h₄
  absurd h₅ (by simp [TypeCtx.withRecs])

/-- **Core does not type `null` at the nested type.** -/
theorem not_refOk_null_nested (s : Store H) : ¬ RefOk s .null nestedRT := fun h =>
  (refOk_null_inv h).elim (fun he => by simp [nestedRT] at he) not_tyOk_nested

end Silmaril.Wasm.SpecTec.Sim.Round5.RefOk
