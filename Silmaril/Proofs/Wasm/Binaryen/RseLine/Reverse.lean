module

public import Silmaril.Proofs.Wasm.Binaryen.RseLine.Sound
public import Silmaril.Wasm.Binaryen.Deferred.Thms

@[expose] public section

/-! # Self-store elimination: the reverse simulation and soundness at every profile

The original `local.get x; local.set x` (or `local.get x; local.tee x`) is on the
**left**. Its read of `v` is matched by the result's read (and, for `set`, the
result's `drop`). The two sides now agree only through the frame: the original still
stores `v` into `x`, which already holds `v`, so the store leaves the frame unchanged
(`RedundantSetLine.setLocal_self`). The store (and the tee expansion before it) is a
forced step (`Deferred.Forced.{set,tee}`), so the left successor normalises to the
right one, and the deferred closure (`Silmaril.Wasm.Binaryen.Deferred`) gives export
refinement at every numerical profile. With silmaril's forward simulation
`RedundantSetLine.rsBaseSim` (already profile-generic) this gives exact export
equivalence at every numerical profile, with no determinism argument.
-/

namespace Silmaril.Proofs.Wasm.Binaryen.RseLine

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.RseLine

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen.RedundantSetLine
open Silmaril.Wasm.Binaryen.Deferred

variable {H : Type} {P : Profile}

/-- Runtime base pairs of the reverse simulation: the original on the left. -/
inductive rsRB : List Admin → List Admin → Prop where
  | set (x : LocalIdx) : rsRB [.plain (.localGet x), .plain (.localSet x)]
      [.plain (.localGet x), .plain .drop]
  | tee (x : LocalIdx) : rsRB [.plain (.localGet x), .plain (.localTee x)]
      [.plain (.localGet x)]

/-- Storing a local's own value is a forced step that leaves the frame unchanged. -/
theorem self_set_forced {s : Store H} {f : Frame} {vs : List Val} {v : Val} {x : LocalIdx}
    {rest : List Admin} (hv : f.local? x = some (some v)) :
    Normalizes ⟨s, f, vals vs ++ v.toAdmin :: .plain (.localSet x) :: rest⟩
      ⟨s, f, vals vs ++ rest⟩ := by
  have hx : x.toNat < f.locals.length := (List.getElem?_eq_some_iff.mp hv).1
  have h : Forced ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localSet x)] ++ rest⟩
      ⟨s, f.setLocal x v, vals vs ++ rest⟩ := Forced.set s f vs v x rest hx
  have hf : f.setLocal x v = f := setLocal_self hv
  simpa [hf] using Normalizes.single h

/-- A self tee is a forced expansion followed by a forced self store. -/
theorem self_tee_forced {s : Store H} {f : Frame} {vs : List Val} {v : Val} {x : LocalIdx}
    {rest : List Admin} (hv : f.local? x = some (some v)) :
    Normalizes ⟨s, f, vals vs ++ v.toAdmin :: .plain (.localTee x) :: rest⟩
      ⟨s, f, vals (vs ++ [v]) ++ rest⟩ := by
  have h₁ : Forced ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localTee x)] ++ rest⟩
      ⟨s, f, vals vs ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest⟩ :=
    Forced.tee s f vs v x rest
  have h₂ : Normalizes ⟨s, f, vals (vs ++ [v]) ++ v.toAdmin :: .plain (.localSet x) :: rest⟩
      ⟨s, f, vals (vs ++ [v]) ++ rest⟩ := self_set_forced hv
  have h₁' : Normalizes ⟨s, f, vals vs ++ v.toAdmin :: .plain (.localTee x) :: rest⟩
      ⟨s, f, vals (vs ++ [v]) ++ v.toAdmin :: .plain (.localSet x) :: rest⟩ := by
    simpa [vals, List.append_assoc] using Normalizes.single h₁
  exact h₁'.trans h₂

/-- The result's `local.get x; drop` runs to its continuation. -/
theorem get_drop_steps {t : Store H} {f : Frame} {vs : List Val} {v : Val} {x : LocalIdx}
    {rest' : List Admin} (hv : f.local? x = some (some v)) :
    Relation.TransGen (Step P closedHost)
      ⟨t, f, vals vs ++ [.plain (.localGet x), .plain .drop] ++ rest'⟩ ⟨t, f, vals vs ++ rest'⟩ := by
  have h₁ : Step P closedHost ⟨t, f, vals vs ++ [.plain (.localGet x)] ++ (.plain .drop :: rest')⟩
      ⟨t, f, vals vs ++ [v.toAdmin] ++ (.plain .drop :: rest')⟩ :=
    (Forced.get t f vs x v (.plain .drop :: rest') hv).step
  have h₂ : Step P closedHost ⟨t, f, vals vs ++ [v.toAdmin, .plain .drop] ++ rest'⟩
      ⟨t, f, vals vs ++ [] ++ rest'⟩ :=
    Step.append_right (Step.vals_left
      (Step.parametric (P := P) (host := closedHost) (s := t) (f := f) (ParametricStep.drop v)) vs)
      rest'
  exact .tail (.single (by simpa using h₁)) (by simpa using h₂)

theorem rsReverseFacts {F : FuncInst H → FuncInst H → Prop} :
    BaseFacts P closedHost F (fun a b => rsBI b a) rsRB fwRank where
  src := by
    intro x y h
    cases h with
    | set x => exact .set x
    | tee x => exact .tee x
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | set x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localGet x))
        (x' := [.plain (.localSet x)]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa using he)
    | tee x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localGet x))
        (x' := [.plain (.localTee x)]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | set x => exact hall (.plain (.localGet x)) (by simp) rfl
    | tee x => exact hall (.plain (.localGet x)) (by simp) rfl

/-- **The reverse simulation**: the original simulates the result, deferring the
original's self store, at every numerical profile. -/
theorem rsReverseSim {F : FuncInst H → FuncInst H → Prop} :
    DeferredBaseSim P F (fun a b => rsBI b a) rsRB where
  facts := rsReverseFacts
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | set x =>
      have hs : Step P closedHost
          ⟨s, f, vals vs ++ .plain (.localGet x) :: (.plain (.localSet x) :: rest)⟩
          ⟨s', f', es'⟩ := by simpa using hstep
      obtain ⟨v, hv, hs₁, hf₁, he₁⟩ := get_step_inv hs
      rw [hs₁, hf₁, he₁]
      exact ⟨_, _, self_set_forced hv, Or.inl (get_drop_steps hv), hst, rfl,
        (AdminsRel.refl _).append hrest⟩
    | tee x =>
      have hs : Step P closedHost
          ⟨s, f, vals vs ++ .plain (.localGet x) :: (.plain (.localTee x) :: rest)⟩
          ⟨s', f', es'⟩ := by simpa using hstep
      obtain ⟨v, hv, hs₁, hf₁, he₁⟩ := get_step_inv hs
      have hrun : Step P closedHost ⟨t, f, vals vs ++ [.plain (.localGet x)] ++ rest'⟩
          ⟨t, f, vals (vs ++ [v]) ++ rest'⟩ := by
        simpa [vals, List.append_assoc] using (Forced.get t f vs x v rest' hv).step (P := P)
      rw [hs₁, hf₁, he₁]
      exact ⟨_, _, self_tee_forced hv, Or.inl (.single hrun), hst, rfl,
        (AdminsRel.refl _).append hrest⟩

/-- The raw rewrite is exactly export-equivalent at every numerical profile. -/
theorem rseLine_sound_any {m : BModule} (hm : m.Ok) (hm' : (rseLine m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (rseLine m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel rsBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (rseLine_bodiesRel m) hm' hm,
    (deferred_exportRefines_of_bodiesRel rsReverseSim
      (rseLine_bodiesRel m).flip hm hm').mono fun _ _ h => h.symm⟩

/-- The checked stage keeps validity and is exactly export-equivalent at every
numerical profile; its validator fallback is the identity. -/
theorem rseLineChecked_sound_any {m : BModule} (hm : m.Ok) :
    (RseLine.rseLineChecked m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (RseLine.rseLineChecked m).lower m.lower := by
  unfold RseLine.rseLineChecked
  dsimp only
  split
  · next h => exact ⟨Exe.validOk_sound h, rseLine_sound_any hm (Exe.validOk_sound h)⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Proofs.Wasm.Binaryen.RseLine
