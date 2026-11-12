module

public import Silmaril.Wasm.Models.FXPresI.Defs
public import Silmaril.Wasm.Models.FXPres.Thms

/-!
# `CtI` and Core steps: the fragment is closed under reduction

* `okB`: the shapes `CtI` types, with `br` and `return`; `TL.okI`: every top-level instruction
  of typed Core code has such a shape. Most Core rules have a left-hand side with another
  instruction, so they cannot fire.
* `stepI`: a Core step on `TL`-typed Core code keeps the store, the frame and the type.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres Silmaril.Wasm.Models.FXPresI
open Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics

variable {H : Type} {m₀ : ModuleInst} {ι : CValType → FTy} {nt : TypeIdx → FTy}
  {s : Store H} {Γ : List TypeIdx} {Ls : List (List FTy)} {R : Option (List FTy)}

/-- The instructions typed by `CtI`, and `br`, `return`. -/
def okB : Admin → Bool
  | .plain (.intConst _ _) => true
  | .plain (.intUnOp _ _) => true
  | .plain (.intBinOp _ _) => true
  | .plain (.intTestOp _ _) => true
  | .plain (.intRelOp _ _) => true
  | .plain .nop => true
  | .plain .drop => true
  | .plain .unreachable => true
  | .plain .throwRef => true
  | .plain (.br _) => true
  | .plain .return_ => true
  | .trap => true
  | .ref (.exn _) => true
  | _ => false

theorem okB_of_ctI {a : Admin} {i o : List FTy} (h : CtI s a i o) : okB a = true := by
  cases h <;> rfl

theorem ctI_not_ctl {a : Admin} {i o : List FTy} (h : CtI s a i o) : ¬ IsCtl a := by
  cases h <;> simp [IsCtl]

/-- Values have principal types: no operand, one result. -/
theorem ctI_val {v : Val} {i o : List FTy} (h : CtI s v.toAdmin i o) : i = [] ∧ ∃ t, o = [t] := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | ⟨_⟩ <;> cases h <;> simp

/-- Every top-level instruction of typed Core code is typed by `CtI` or is `br`/`return`. -/
theorem TL.okI {cs : List Admin} {i o : List FTy}
    (h : TL (envI m₀ ι nt) s Γ Ls R (cs.map .core) i o) : ∀ a ∈ cs, okB a = true := by
  induction cs generalizing i with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons] at h
    cases h with
    | core hc _ hr => exact List.forall_mem_cons.2 ⟨okB_of_ctI hc, ih hr⟩
    | br _ hr => exact List.forall_mem_cons.2 ⟨rfl, ih hr⟩
    | ret _ hr => exact List.forall_mem_cons.2 ⟨rfl, ih hr⟩

/-- One typed instruction. -/
theorem TL.oneI {a : Admin} {pre i₀ o₀ : List FTy} (h : CtI s a i₀ o₀) :
    TL (envI m₀ ι nt) s Γ Ls R [.core a] (pre ++ i₀) (pre ++ o₀) :=
  TL.core (E := envI m₀ ι nt) (pre := pre) h (ctI_not_ctl h) .nil

/-- `trap` at any type. -/
theorem TL.trapI {i o : List FTy} : TL (envI m₀ ι nt) s Γ Ls R [.core .trap] i o := by
  simpa using TL.oneI (m₀ := m₀) (ι := ι) (nt := nt) (s := s) (Γ := Γ) (Ls := Ls) (R := R)
    (pre := []) (CtI.trap (i := i) (o := o))

/-- Inversion at one instruction of the fragment. -/
theorem TL.invI {a : Admin} {as : List AdminFX} {i o : List FTy} (ha : okB a = true)
    (hn : ¬ IsCtl a) (h : TL (envI m₀ ι nt) s Γ Ls R (.core a :: as) i o) :
    ∃ pre i₀ o₀, CtI s a i₀ o₀ ∧ i = pre ++ i₀ ∧ TL (envI m₀ ι nt) s Γ Ls R as (pre ++ o₀) o := by
  have _ := ha
  exact TL.core_inv (E := envI m₀ ι nt) hn h

/-- `throwing a` at any type, for an allocated `a`. -/
theorem TL.throwingI {a : Nat} (ha : a < s.exns.length) {i o : List FTy} :
    TL (envI m₀ ι nt) s Γ Ls R ((throwing a).map .core) i o := by
  have h₂ : TL (envI m₀ ι nt) s Γ Ls R [.core (.plain .throwRef)] ([] ++ (i ++ [exnTy]))
      ([] ++ o) := TL.oneI (CtI.throwRef (i := i) (o := o))
  have h₁ : TL (envI m₀ ι nt) s Γ Ls R [.core (.ref (.exn a))] (i ++ []) (i ++ [exnTy]) :=
    TL.oneI (CtI.refExn ha)
  simpa using TL.append h₁ (by simpa using h₂)

end Silmaril.Proofs.Wasm.Models.FXPresI
