module

public import Silmaril.Proofs.Wasm.Binaryen.TeeForm.Sound
public import Silmaril.Wasm.Binaryen.Deferred.Thms

@[expose] public section

/-! # Tee formation: the reverse simulation and soundness at every profile

The original `local.set x; local.get x` is on the **left**. Its store step (to frame
`f[x := v]`, code `local.get x`) is matched by two result steps, `v; local.tee x` to
`v; v; local.set x` to `v`, reaching the same frame. The two sides now agree only
through the frame: the original still reads `x`, which holds `v`. That read is a
forced step (`Deferred.Forced.get`), so the left successor normalises to the right
one, and the deferred closure (`Silmaril.Wasm.Binaryen.Deferred`) gives export
refinement at every numerical profile. With the forward simulation `tfBaseSim`
(`Sound.lean`, already profile-generic) this gives exact export equivalence at every
numerical profile, with no determinism argument.
-/

namespace Silmaril.Proofs.Wasm.Binaryen.TeeForm

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.TeeForm

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen.Deferred

variable {H : Type} {P : Profile}

/-- Runtime base pairs of the reverse simulation: the original on the left. -/
inductive tfRB : List Admin → List Admin → Prop where
  | mk (x : LocalIdx) : tfRB [.plain (.localSet x), .plain (.localGet x)] [.plain (.localTee x)]

/-- Invert a local store at the active head, with an arbitrary value prefix. -/
theorem set_head_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {x : LocalIdx}
    {rest es' : List Admin}
    (h : Step P closedHost ⟨s, f, vals vs ++ .plain (.localSet x) :: rest⟩ ⟨s', f', es'⟩) :
    ∃ pre v, vs = pre ++ [v] ∧ x.toNat < f.locals.length ∧ s' = s ∧
      f' = f.setLocal x v ∧ es' = vals pre ++ rest := by
  obtain ⟨pre, args, c₀, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) h
  obtain ⟨w, hargs, hx, hc₀⟩ : ∃ w, args = [w] ∧ x.toNat < f.locals.length ∧
      c₀ = ⟨s, f.setLocal x w, []⟩ := SimplifyLocalsLite.head_localSet hh
  have hvs : vs = pre ++ [w] := by rw [hW, hargs]
  have hparts : s' = s ∧ f' = f.setLocal x w ∧ es' = vals pre ++ rest := by
    simpa only [hc₀, Config.mk.injEq, List.append_nil] using he
  exact ⟨pre, w, hvs, hx, hparts⟩

/-- The result's `local.tee x` runs to the frame the original's store produces. -/
theorem tee_set_steps {t : Store H} {f : Frame} {pre : List Val} {v : Val} {x : LocalIdx}
    {rest' : List Admin} (hx : x.toNat < f.locals.length) :
    Relation.TransGen (Step P closedHost)
      ⟨t, f, vals (pre ++ [v]) ++ [.plain (.localTee x)] ++ rest'⟩
      ⟨t, f.setLocal x v, vals (pre ++ [v]) ++ rest'⟩ := by
  have h₁ : Step P closedHost ⟨t, f, vals pre ++ [v.toAdmin, .plain (.localTee x)] ++ rest'⟩
      ⟨t, f, vals pre ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest'⟩ :=
    (Forced.tee t f pre v x rest').step
  have h₂ : Step P closedHost
      ⟨t, f, vals (pre ++ [v]) ++ [v.toAdmin, .plain (.localSet x)] ++ rest'⟩
      ⟨t, f.setLocal x v, vals (pre ++ [v]) ++ rest'⟩ :=
    (Forced.set t f (pre ++ [v]) v x rest' hx).step
  exact .tail (.single (by simpa [vals, List.append_assoc] using h₁))
    (by simpa [vals, List.append_assoc] using h₂)

/-- The original's read of the value it just stored is forced. -/
theorem get_after_set {s : Store H} {f : Frame} {pre : List Val} {v : Val} {x : LocalIdx}
    {rest : List Admin} (hx : x.toNat < f.locals.length) :
    Normalizes ⟨s, f.setLocal x v, vals pre ++ .plain (.localGet x) :: rest⟩
      ⟨s, f.setLocal x v, vals (pre ++ [v]) ++ rest⟩ := by
  have h : Forced ⟨s, f.setLocal x v, vals pre ++ [.plain (.localGet x)] ++ rest⟩
      ⟨s, f.setLocal x v, vals pre ++ [v.toAdmin] ++ rest⟩ :=
    Forced.get s (f.setLocal x v) pre x v rest (local?_setLocal hx)
  simpa [vals, List.append_assoc] using Normalizes.single h

theorem tfReverseFacts {F : FuncInst H → FuncInst H → Prop} :
    BaseFacts P closedHost F (fun a b => tfBI b a) tfRB fwRank where
  src := by
    intro x y h
    cases h with
    | mk x => exact .mk x
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | mk x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localSet x))
        (x' := [.plain (.localGet x)]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | mk x => exact hall (.plain (.localSet x)) (by simp) rfl

/-- **The reverse simulation**: the original simulates the result, deferring the
original's read of the stored local, at every numerical profile. -/
theorem tfReverseSim {F : FuncInst H → FuncInst H → Prop} :
    DeferredBaseSim P F (fun a b => tfBI b a) tfRB where
  facts := tfReverseFacts
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | mk x =>
      have hs : Step P closedHost
          ⟨s, f, vals vs ++ .plain (.localSet x) :: (.plain (.localGet x) :: rest)⟩
          ⟨s', f', es'⟩ := by simpa using hstep
      obtain ⟨pre, v, hvs, hx, hs₁, hf₁, he₁⟩ := set_head_inv hs
      rw [hvs, hs₁, hf₁, he₁]
      exact ⟨_, _, get_after_set hx, Or.inl (tee_set_steps hx), hst, rfl,
        (AdminsRel.refl _).append hrest⟩

/-- The raw rewrite is exactly export-equivalent at every numerical profile. -/
theorem teeForm_sound_any {m : BModule} (hm : m.Ok) (hm' : (teeForm m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (teeForm m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel tfBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (teeForm_bodiesRel m) hm' hm,
    (deferred_exportRefines_of_bodiesRel tfReverseSim
      (teeForm_bodiesRel m).flip hm hm').mono fun _ _ h => h.symm⟩

/-- The checked stage keeps validity and is exactly export-equivalent at every
numerical profile; its validator fallback is the identity. -/
theorem teeFormChecked_sound_any {m : BModule} (hm : m.Ok) :
    (teeFormChecked m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (teeFormChecked m).lower m.lower := by
  unfold teeFormChecked
  dsimp only
  split
  · next h => exact ⟨Exe.validOk_sound h, teeForm_sound_any hm (Exe.validOk_sound h)⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Proofs.Wasm.Binaryen.TeeForm
