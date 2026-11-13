module

public import Silmaril.Wasm.FX.Asyncify.Tool.CoreRefute.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# A counterexample to `Task.machine_core`: proofs

* `cx_holds`, `cx_globals`, `cx_mem`: the store `cxS` holds the asyncified `cxP`, the globals
  `[2, 9]`, and every word memory that is zero at the aligned words (`m7` and the zero memory).
* `runTo_sound`: a result of `runTo` is a run of `stepB` ending in a return.
* `cx_run7`, `cx_run0`: from the same globals, the machine returns `[7]` on `m7` and `[0]` on the
  zero memory.
* `vals_unique`: two Core runs of one configuration to values, in the deterministic profile
  without host, end at the same values (silmaril-lean's diamond property `Det.DStep.join'` and
  Church–Rosser).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreRefute

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.FX.Asyncify.Tool

theorem cxP_wf : cxP.WF := by
  unfold Prog.WF
  decide

theorem cxP_fn : (asyncifyProg cxP).fns[0]? = some cxFd := rfl

theorem cx_holds : HoldsProg cxS cxMI (asyncifyProg cxP) := by
  intro j fd h
  match j, h with
  | 0, h =>
    have hfd : fd = cxFd := by
      rw [cxP_fn] at h
      exact (Option.some.inj h).symm
    rw [hfd]
    exact ⟨0, _, ⟨0⟩, _, _, rfl, rfl, rfl, rfl,
      Expand.iff.2 (V2.FuncType.toDefType_expand _), rfl, rfl⟩
  | _ + 1, h => simp [asyncifyProg, cxP] at h

theorem cx_globals : GlobalsAre cxS ⟨[], cxMI⟩ [2, 9] := by
  refine ⟨by decide, ?_, ?_⟩
  · intro g hg
    match g, hg with
    | 0, _ => exact ⟨0, _, rfl, rfl, rfl⟩
    | 1, _ => exact ⟨1, _, rfl, rfl, rfl⟩
  · intro g g' a a' gi gi' h h' hg hg' ha
    match g, g', hg, hg' with
    | 0, 0, _, _ => rfl
    | 1, 1, _, _ => rfl
    | 0, 1, _, _ => cases h; cases h'; cases ha
    | 1, 0, _, _ => cases h; cases h'; cases ha

theorem cx_mem (m : Nat → W) (hm : ∀ a, a % 4 = 0 → m a = 0) : MemAre cxS ⟨[], cxMI⟩ m 12 := by
  refine ⟨0, _, rfl, rfl, ?_⟩
  intro a ha hc
  rw [hm a ha]
  have h3 : a = 0 ∨ a = 4 ∨ a = 8 := by omega
  rcases h3 with rfl | rfl | rfl <;> decide

theorem m7_aligned (a : Nat) (ha : a % 4 = 0) : m7 a = 0 := by
  have h1 : a ≠ 1 := by omega
  simp [m7, h1]

theorem runTo_sound {cap : Nat} {E : Env} : ∀ {n : Nat} {c : Cfg} {vs : List W},
    runTo cap E n c = some vs → ∃ c' c'', BSteps cap E c c' ∧ stepB cap E c' = .done vs c''
  | 0, _, _, h => by cases h
  | n + 1, c, vs, h => by
    unfold runTo at h
    split at h
    · obtain ⟨c', c'', h1, h2⟩ := runTo_sound h
      exact ⟨c', c'', .cons (by assumption) h1, h2⟩
    · cases h
      exact ⟨c, _, .refl c, by assumption⟩
    · cases h

theorem cx_run7 :
    runTo 12 (asyncifyProg cxP) 50 ⟨[entry 0 cxFd [3]], [2, 9], m7⟩ = some [7] := by
  decide

theorem cx_run0 :
    runTo 12 (asyncifyProg cxP) 50 ⟨[entry 0 cxFd [3]], [2, 9], fun _ => 0⟩ = some [0] := by
  decide

/-- Determinism up to bubbling, as the hypothesis of `Relation.church_rosser`. -/
theorem dstep_cr {o : Numerics.GrowKind → Nat → Nat → Nat → Bool} (a b c : Config Unit)
    (hb : Det.DStep o a b) (hc : Det.DStep o a c) :
    ∃ d, Relation.ReflGen (Det.DStep o) b d ∧ Relation.ReflTransGen (Det.DStep o) c d := by
  obtain ⟨d, h1, h2⟩ := Det.DStep.join' hb hc
  have h2' : Relation.ReflTransGen (Det.DStep o) c d := by
    cases h2 with
    | refl => exact .refl
    | single h => exact .single h
  exact ⟨d, h1, h2'⟩

/-- A configuration of values is a normal form. -/
theorem vals_nf {o : Numerics.GrowKind → Nat → Nat → Nat → Bool} {s : Store Unit}
    {f : Execution.Core.Frame} {w : List Val} {d : Config Unit}
    (h : Relation.ReflTransGen (Det.DStep o) ⟨s, f, vals w⟩ d) : d = ⟨s, f, vals w⟩ := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head h _ => exact (Det.not_step_vals h).elim

/-- **Values are unique**: two Core runs of one configuration to values (deterministic profile,
no host) end at the same values. -/
theorem vals_unique {o : Numerics.GrowKind → Nat → Nat → Nat → Bool} {C : Config Unit}
    {s₁ s₂ : Store Unit} {f₁ f₂ : Execution.Core.Frame} {w₁ w₂ : List Val}
    (h₁ : Execution.Core.Steps (Numerics.Profile.deterministic o) Det.noHost C ⟨s₁, f₁, vals w₁⟩)
    (h₂ : Execution.Core.Steps (Numerics.Profile.deterministic o) Det.noHost C ⟨s₂, f₂, vals w₂⟩) :
    vals w₁ = vals w₂ := by
  obtain ⟨d, e₁, e₂⟩ := Relation.church_rosser dstep_cr h₁ h₂
  have hd : (⟨s₁, f₁, vals w₁⟩ : Config Unit) = ⟨s₂, f₂, vals w₂⟩ :=
    (vals_nf e₁).symm.trans (vals_nf e₂)
  exact congrArg Config.code hd

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreRefute
