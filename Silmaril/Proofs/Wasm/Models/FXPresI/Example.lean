module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Hyp
public import Silmaril.Wasm.Execution.Core.Soundness.RedexTyping

/-!
# `envI` is not empty, and the naive Silmaril typing is not a `CoreHyp`

* `configOk_add`, `step_add`: `i32.const 1; i32.const 2; i32.add` is a typed configuration of
  `envI`, and it steps under `StepFXS`.
* `naive_val_fails`: Silmaril's `AdminsOk` on one instruction, read at value types, types
  `i32.const 0` at `[i32] → [i32, i32]` (its `frame` rule), so it violates `CoreHyp.val`.
* `naive_trap_fails`: read at value types it has no `trap` at a continuation type, so it violates
  `CoreHyp.trap`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres Silmaril.Wasm.Models.FXPresI
open Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {ι : CValType → FTy} {nt : TypeIdx → FTy}

/-- `i32.const 1; i32.const 2; i32.add`. -/
def addCode : List Admin :=
  [.plain (.intConst .i32 1), .plain (.intConst .i32 2), .plain (.intBinOp .i32 .add)]

theorem tl_add {s : Store H} {Γ : List TypeIdx} {Ls : List (List FTy)} {R : Option (List FTy)} :
    TL (envI m₀ ι nt) s Γ Ls R (addCode.map .core) [] [intTy .i32] := by
  have h₁ : TL (envI m₀ ι nt) s Γ Ls R [.core (.plain (.intConst .i32 1))] [] [intTy .i32] := by
    simpa using TL.oneI (m₀ := m₀) (ι := ι) (nt := nt) (s := s) (Γ := Γ) (Ls := Ls) (R := R)
      (pre := []) (CtI.intConst (t := .i32) (x := 1))
  have h₂ : TL (envI m₀ ι nt) s Γ Ls R [.core (.plain (.intConst .i32 2))] [intTy .i32]
      [intTy .i32, intTy .i32] := by
    simpa using TL.oneI (m₀ := m₀) (ι := ι) (nt := nt) (s := s) (Γ := Γ) (Ls := Ls) (R := R)
      (pre := [intTy .i32]) (CtI.intConst (t := .i32) (x := 2))
  have h₃ : TL (envI m₀ ι nt) s Γ Ls R [.core (.plain (.intBinOp .i32 .add))]
      [intTy .i32, intTy .i32] [intTy .i32] := by
    simpa using TL.oneI (m₀ := m₀) (ι := ι) (nt := nt) (s := s) (Γ := Γ) (Ls := Ls) (R := R)
      (pre := []) (CtI.intBinOp (t := .i32) (op := .add))
  exact TL.append h₁ (TL.append h₂ h₃)

/-- **A typed configuration of `envI`.** -/
theorem configOk_add {s : Store H} {f : Frame} (hf : f.module = m₀) :
    ConfigOk (envI m₀ ι nt) [] ⟨s, [], f, addCode.map .core⟩ [intTy .i32] :=
  ⟨hf, ⟨rfl, fun _ _ h => by simp at h⟩, tl_add⟩

/-- It steps. -/
theorem step_add {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {f : Frame} :
    StepFXS P host fx ⟨s, [], f, addCode.map .core⟩
      ⟨s, [], f, [Admin.plain (.intConst .i32 3)].map .core⟩ :=
  .core (.numeric (.intBinOp rfl))

/-- The naive Core typing: Silmaril's `AdminsOk` on one instruction, at value types. -/
def ctNaive (C : Context) (s : Store H) (a : Admin) (i o : List FTy) : Prop :=
  ∃ i' o' xs, i = vtys i' ∧ o = vtys o' ∧ AdminsOk s C [a] ⟨i', xs, o'⟩

/-- **The naive typing is not principal on values** (`CoreHyp.val` fails). -/
theorem naive_val_fails (C : Context) (s : Store H) :
    ctNaive C s (Val.i32 0).toAdmin [intTy .i32] [intTy .i32, intTy .i32] := by
  have hv : AdminsOk s C [(Val.i32 0).toAdmin] (.plain [] [.num (.int .i32)]) :=
    AdminsOk.val_single (ValOk.num _)
  have hok : ResultOk C.toTypeCtx [.num (.int .i32)] := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact TyOk.num _
  exact ⟨_, _, _, rfl, rfl, AdminsOk.frame hv hok⟩

/-- **The naive typing has no `trap` at a continuation type** (`CoreHyp.trap` fails). -/
theorem naive_trap_fails (C : Context) (s : Store H) (ct : TypeIdx) :
    ¬ ctNaive C s .trap [.cont ct] [] := by
  rintro ⟨i', o', xs, hi, -, -⟩
  cases i' <;> simp [vtys] at hi

end Silmaril.Proofs.Wasm.Models.FXPresI
