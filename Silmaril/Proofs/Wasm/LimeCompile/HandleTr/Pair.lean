module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Invoke
public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Inst
public import Silmaril.Wasm.V2.ToCore.Validation

/-!
# Source and target of the handle compiler on 2.0 function types: types and arguments

* `hV2val`, `hV2FT`: the handle rewrite on 2.0 value and function types;
  `hRec_toCoreRec`: it commutes with the Core embedding, so the target's closed types are
  `allocTypes_v2` of the rewritten 2.0 types;
* `argOk_src`, `argOk_tgt`: a target argument related to a source argument by `ArgRelT` at a
  2.0 parameter type is well typed at the rewritten type iff... in the direction needed:
  target to source uses `HandleOk`, source to target is immediate;
* `resRel_of_argRel`: related arguments are related results (`Handle.ResRel`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.HandleTr
open Silmaril.Wasm.LimeCompile.Handle (handleRef ResRel)

variable {H : Type}

/-- The handle rewrite of a 2.0 value type. -/
def hV2val : V2.ValType → V2.ValType
  | .ref _ => .num (.int .i32)
  | t => t

/-- The handle rewrite of a 2.0 function type. -/
def hV2FT (t : V2.FuncType) : V2.FuncType := ⟨t.params.map hV2val, t.results.map hV2val⟩

theorem hv_toCore (τ : V2.ValType) : hv τ.toCore = (hV2val τ).toCore := by
  cases τ with
  | num t => rfl
  | vec t => rfl
  | ref r => cases r <;> rfl

theorem hRec_toCoreRec (t : V2.FuncType) : hRec t.toCoreRec = (hV2FT t).toCoreRec := by
  simp [hRec, V2.FuncType.toCoreRec, hSub, hComp, hFT, V2.FuncType.toCore, V2.ResultType.toCore,
    hV2FT, List.map_map, Function.comp_def, hv_toCore]

theorem allocTypes_v2 (ts : List V2.FuncType) :
    allocTypes (ts.map V2.FuncType.toCoreRec) = ts.map V2.FuncType.toDefType :=
  allocTypes_eq (V2.Validation.typesOk_map ts {})

theorem handleRef_toCore (τ : V2.ValType) : handleRef τ.toCore = true ↔ ∃ r, τ = .ref r := by
  cases τ with
  | num t => simp [V2.ValType.toCore, handleRef]
  | vec t => simp [V2.ValType.toCore, handleRef]
  | ref r => cases r <;> simp [V2.ValType.toCore, V2.RefType.toCore, handleRef]

/-- Values of number and vector types are store-independent. -/
theorem valOk_nonref {s s' : Store H} {v : Val} {τ : V2.ValType} (hτ : ∀ r, τ ≠ .ref r)
    (h : ValOk s v τ.toC) : ValOk s' v τ.toC := by
  cases τ with
  | num t =>
    cases h with
    | num v => exact .num v
  | vec t =>
    cases h with
    | vec b => exact .vec b
  | ref r => exact absurd rfl (hτ r)

theorem valOk_nonref_not_func {s : Store H} {v : Val} {τ : V2.ValType} (hτ : ∀ r, τ ≠ .ref r)
    (h : ValOk s v τ.toC) (b : Nat) : v ≠ .ref (.func b) := by
  rintro rfl
  cases τ with
  | num t => cases h
  | vec t => cases h
  | ref r => exact hτ r rfl

/-- A store-independent handle value is well typed at its 2.0 reference type. -/
theorem valOk_handle {s : Store H} {r : V2.RefType} {v : Val}
    (h : HandleOk (V2.ValType.ref r).toCore v) : ValOk s v (V2.ValType.ref r).toC := by
  rcases h with ⟨-, rfl⟩ | ⟨hx, a, rfl⟩
  · show ValOk s (.ref .null) (.refv r.toC)
    exact .ref (.sub .null (V2.Validation.tyOk_toC_ref {} r) (by cases r <;> exact .refNull .bot))
  · cases r with
    | funcref => simp [externRef, V2.ValType.toCore, V2.RefType.toCore] at hx
    | externref =>
      refine .ref (.sub (.extern (.host a) (by simp)) (V2.Validation.tyOk_toC_ref {} .externref) ?_)
      exact .refNull .heapRefl

theorem handleOk_not_func {t : ValType} {v : Val} (h : HandleOk t v) (b : Nat) :
    v ≠ .ref (.func b) := by
  rcases h with ⟨-, rfl⟩ | ⟨-, a, rfl⟩ <;> simp

theorem handleOk_ref {t : ValType} {v : Val} (h : HandleOk t v) : ∃ r, v = .ref r := by
  rcases h with ⟨-, rfl⟩ | ⟨-, a, rfl⟩ <;> exact ⟨_, rfl⟩

/-- **Target to source**: a related argument well typed at the rewritten type gives a source
argument well typed at the source type. -/
theorem argOk_src {σ : List Val} {s s' : Store H} {τ : V2.ValType} {w v : Val}
    (h : ArgRelT σ τ.toCore w v) (hw : ValOk s' w (hV2val τ).toC) : ValOk s v τ.toC := by
  rcases h with ⟨hr, rfl⟩ | ⟨hr, k, rfl, -, hok⟩
  · have hτ : ∀ r, τ ≠ .ref r := by
      rintro r rfl
      cases r <;> simp [V2.ValType.toCore, V2.RefType.toCore, handleRef] at hr
    have : hV2val τ = τ := by cases τ <;> simp_all [hV2val]
    rw [this] at hw
    exact valOk_nonref hτ hw
  · obtain ⟨r, rfl⟩ := (handleRef_toCore τ).mp hr
    exact valOk_handle hok

/-- **Source to target.** -/
theorem argOk_tgt {σ : List Val} {s s' : Store H} {τ : V2.ValType} {w v : Val}
    (h : ArgRelT σ τ.toCore w v) (hv : ValOk s v τ.toC) : ValOk s' w (hV2val τ).toC := by
  rcases h with ⟨hr, rfl⟩ | ⟨hr, k, rfl, -, -⟩
  · have hτ : ∀ r, τ ≠ .ref r := by
      rintro r rfl
      cases r <;> simp [V2.ValType.toCore, V2.RefType.toCore, handleRef] at hr
    have : hV2val τ = τ := by cases τ <;> simp_all [hV2val]
    rw [this]
    exact valOk_nonref hτ hv
  · obtain ⟨r, rfl⟩ := (handleRef_toCore τ).mp hr
    exact .num _

theorem argRel_src_not_func {σ : List Val} {s : Store H} {τ : V2.ValType} {w v : Val}
    (h : ArgRelT σ τ.toCore w v) (hv : ValOk s v τ.toC) (b : Nat) : v ≠ .ref (.func b) := by
  rcases h with ⟨hr, rfl⟩ | ⟨-, k, rfl, -, hok⟩
  · have hτ : ∀ r, τ ≠ .ref r := by
      rintro r rfl
      cases r <;> simp [V2.ValType.toCore, V2.RefType.toCore, handleRef] at hr
    exact valOk_nonref_not_func hτ hv b
  · exact handleOk_not_func hok b

theorem argRel_tgt_not_func {σ : List Val} {s : Store H} {τ : V2.ValType} {w v : Val}
    (h : ArgRelT σ τ.toCore w v) (hv : ValOk s v τ.toC) (b : Nat) : w ≠ .ref (.func b) := by
  rcases h with ⟨hr, rfl⟩ | ⟨-, k, rfl, -, -⟩
  · exact argRel_src_not_func (σ := σ) (.inl ⟨hr, rfl⟩) hv b
  · simp [Val.i32]

theorem resRel_of_argRel {σ : List Val} {t : ValType} {w v : Val} (h : ArgRelT σ t w v) :
    ResRel σ w v := by
  rcases h with ⟨-, rfl⟩ | ⟨-, k, rfl, hk, hok⟩
  · exact .inl rfl
  · obtain ⟨r, rfl⟩ := handleOk_ref hok
    exact .inr ⟨k, r, rfl, rfl, hk⟩

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
