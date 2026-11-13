module

public import Silmaril.Proofs.Wasm.Wasmi.RoundFree.Preserve
public import Silmaril.Wasm.Atlas.Variant.Thms

@[expose] public section

/-!
# The wasmi 0.40.0 model is Core 3.0 on code without rounding operators

* `pending_false`: free code has no pending quirk redex;
* `ctx_quirk_false`: no quirk step (in any context) starts from free code;
* `step_iff`: from a `Free` configuration a model step is exactly a Core 3.0 step;
* `behaviours_eq`: from a `Free` configuration, under a host that keeps stores free, the model
  and Core 3.0 have the same observations (finite results and divergence), by a lock-step
  simulation in each direction on the relation "equal and `Free`" (`step_free`).

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi.RoundFree

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Observed Silmaril.Wasm.Wasmi.RoundFree

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem redexB_false {t : FloatType} {x : FloatValue t} {t' : FloatType} {op : FloatUnOp}
    (h : IsRound op = false) : redexB t x t' op = false := by
  cases t <;> cases t' <;> simp [redexB, h]

mutual
theorem pendingA_false : ∀ a : Admin, rfA a = true → pendingA a = false
  | .label _ _ b, h => by
    simp only [rfA, Bool.and_eq_true] at h
    simp only [pendingA]; exact pending_false b h.2
  | .handler _ _ b, h => by
    simp only [rfA] at h
    simp only [pendingA]; exact pending_false b h
  | .frame _ _ b, h => by
    simp only [rfA] at h
    simp only [pendingA]; exact pending_false b h
  | .plain _, _ => by simp [pendingA]
  | .ref _, _ => by simp [pendingA]
  | .callRefType _, _ => by simp [pendingA]
  | .returnCallRefType _, _ => by simp [pendingA]
  | .trap, _ => by simp [pendingA]

/-- **Free code has no pending quirk redex.** -/
theorem pending_false : ∀ l : List Admin, rfAs l = true → pending l = false
  | [], _ => by simp [pending]
  | a :: rest, h => by
    have h' := h
    simp only [rfAs_cons, Bool.and_eq_true] at h'
    have ihr := pending_false rest h'.2
    have iha := pendingA_false a h'.1
    unfold pending
    split
    · rfl
    · rename_i heq
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      simp only [rfAs_cons, rfA, rfI, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact redexB_false h.2.1
    · split <;> simp_all
end

/-- **No quirk step starts from free code**, in any evaluation context. -/
theorem ctx_quirk_false {c c' : Config H} (h : Variant.Ctx Quirk c c') (hc : rfAs c.code = true) :
    False := by
  induction h with
  | base hq =>
    cases hq with
    | roundNaN hop _ => simp [rfA, rfI, hop] at hc
  | instrs _ ih =>
    simp only [rfAs_append, rfAs_vals, Bool.true_and, Bool.and_eq_true] at hc
    exact ih hc.1
  | label _ ih =>
    simp only [rfAs_cons, rfA, rfAs_nil, Bool.and_true, Bool.and_eq_true] at hc
    exact ih hc.2
  | handler _ ih =>
    simp only [rfAs_cons, rfA, rfAs_nil, Bool.and_true] at hc
    exact ih hc
  | frame _ ih =>
    simp only [rfAs_cons, rfA, rfAs_nil, Bool.and_true] at hc
    exact ih hc

/-- **From free code, a model step is exactly a Core 3.0 step.** -/
theorem step_iff {c c' : Config H} (hc : rfAs c.code = true) :
    Silmaril.Wasm.Wasmi.Observed.Step P host c c' ↔ Execution.Core.Step P host c c' := by
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact h
    · exact (ctx_quirk_false h hc).elim
  · exact fun h => Or.inl ⟨pending_false _ hc, h⟩

/-- **The model and Core 3.0 have the same observations from a free configuration**, under a
host that keeps stores free. -/
theorem behaviours_eq (hh : HostKeeps host) {c : Config H} (hc : Free c) :
    Variant.behavioursR (Silmaril.Wasm.Wasmi.Observed.Step P host) c = behavioursOf P host c := by
  rw [Variant.behavioursOf_eq]
  have terminal : ∀ {c d : Config H} {r : Result}, (c = d ∧ Free c) → c.code = r.toAdmin →
      d.code = r.toAdmin := by
    rintro c d r ⟨rfl, -⟩ h
    exact h
  apply Set.Subset.antisymm
  · refine Variant.behavioursR_subset_of_sim (Rel := fun c d => c = d ∧ Free c) ?_ terminal
      ⟨rfl, hc⟩
    rintro c c' d hs ⟨rfl, hf⟩
    have hcore := (step_iff hf.1).1 hs
    exact ⟨c', hcore, rfl, step_free hh hcore hf⟩
  · refine Variant.behavioursR_subset_of_sim (Rel := fun c d => c = d ∧ Free c) ?_ terminal
      ⟨rfl, hc⟩
    rintro c c' d hs ⟨rfl, hf⟩
    exact ⟨c', (step_iff hf.1).2 hs, rfl, step_free hh hs hf⟩

/-- The invocation of a call on a free store is free. -/
theorem free_invoke {s : Store H} (hs : StoreFree s) (a : Nat) (vs : List Val) :
    Free (invoke s a vs) :=
  ⟨by simp [invoke, rfA], hs⟩

/-- **The model's call observations are Core's at a free point.** -/
theorem obs_eq (P : Profile) {x : Core.Pt H} (hs : StoreFree x.1) (hh : HostKeeps x.2)
    (c : Core.Call) : Silmaril.Wasm.Wasmi.Observed.obs P x c = Core.obs P x c :=
  behaviours_eq hh (free_invoke hs c.1 c.2)

/-- Hosts over `Empty` have no host functions, so they keep every store. -/
theorem hostKeeps_empty (host : HostSemantics Empty) : HostKeeps host :=
  fun h => h.elim

/-- `StoreFree` is a Boolean check. -/
theorem storeFree_iff (s : Store H) : StoreFree s ↔ s.funcs.all rfF = true := by
  simp [StoreFree]

end Silmaril.Proofs.Wasm.Wasmi.RoundFree
