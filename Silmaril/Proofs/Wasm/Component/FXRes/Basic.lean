module

public import Silmaril.Wasm.Component.FXRes.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# Continuations as resources: the continuation store as a handle protocol (proofs)

* `kstep_of_stepFX`, `kstep_of_stepFX'`: every step changes the store by a `KStep`;
  `ksteps_of_stepsFX`, `ksteps_of_stepsFX'`: every run by a `KSteps`.
* `kstep_run`, `ksteps_run`: from a related protocol state, the events are accepted by
  `handleProto ℕ r` for both roles, and the relation is kept.
* `kstep_consumed`, `ksteps_consumed`: a consumed index stays consumed.
* `kstep_budget`, `ksteps_count_free`: along any sequence of store changes, `free k` occurs at
  most `budget K k ≤ 1` times.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : Silmaril.Wasm.Execution.Core.HostSemantics H}
  {fx : H → Option FuncFX}

theorem kstep_of_stepFX {c d : ConfigFX H} (h : StepFX P host fx c d) :
    ∃ evs, KStep c.conts d.conts evs := by
  induction h with
  | seq _ _ ih => exact ih
  | ctxLabel _ ih => exact ih
  | ctxFrame _ ih => exact ih
  | ctxHandler _ ih => exact ih
  | contNew => exact ⟨_, .alloc _ _⟩
  | contBind hk => exact ⟨_, .swap _ hk⟩
  | resume hk => exact ⟨_, .consume hk⟩
  | resumeThrow hk => exact ⟨_, .consume hk⟩
  | suspend => exact ⟨_, .alloc _ _⟩
  | switch hk => exact ⟨_, .swap _ hk⟩
  | _ => exact ⟨_, .same _⟩

theorem kstep_of_stepFX' {c d : ConfigFX H} (h : StepFX' P host fx c d) :
    ∃ evs, KStep c.conts d.conts evs := by
  induction h with
  | seq _ _ ih => exact ih
  | ctxLabel _ ih => exact ih
  | ctxFrame _ ih => exact ih
  | ctxHandler _ ih => exact ih
  | contNew => exact ⟨_, .alloc _ _⟩
  | contBind hk => exact ⟨_, .swap _ hk⟩
  | resume hk => exact ⟨_, .consume hk⟩
  | resumeThrow hk => exact ⟨_, .consume hk⟩
  | suspend => exact ⟨_, .alloc _ _⟩
  | switch hk => exact ⟨_, .swap _ hk⟩
  | _ => exact ⟨_, .same _⟩

theorem ksteps_trans {K₁ K₂ K₃ : KStore} {e₁ e₂ : List (HEv ℕ)} (h₁ : KSteps K₁ K₂ e₁)
    (h₂ : KSteps K₂ K₃ e₂) : KSteps K₁ K₃ (e₁ ++ e₂) := by
  induction h₁ with
  | refl => simpa using h₂
  | cons h _ ih => simpa [List.append_assoc] using KSteps.cons h (ih h₂)

theorem ksteps_single {K K' : KStore} {e : List (HEv ℕ)} (h : KStep K K' e) : KSteps K K' e := by
  simpa using KSteps.cons h (.refl K')

theorem ksteps_of_stepsFX {c d : ConfigFX H} (h : StepsFX P host fx c d) :
    ∃ evs, KSteps c.conts d.conts evs := by
  induction h with
  | refl => exact ⟨[], .refl _⟩
  | tail _ hs ih =>
    obtain ⟨e₁, h₁⟩ := ih
    obtain ⟨e₂, h₂⟩ := kstep_of_stepFX hs
    exact ⟨_, ksteps_trans h₁ (ksteps_single h₂)⟩

theorem ksteps_of_stepsFX' {c d : ConfigFX H} (h : StepsFX' P host fx c d) :
    ∃ evs, KSteps c.conts d.conts evs := by
  induction h with
  | refl => exact ⟨[], .refl _⟩
  | tail _ hs ih =>
    obtain ⟨e₁, h₁⟩ := ih
    obtain ⟨e₂, h₂⟩ := kstep_of_stepFX' hs
    exact ⟨_, ksteps_trans h₁ (ksteps_single h₂)⟩

/-! ## The handle protocol -/

theorem kRel_nil : KRel [] ([] : KStore) := ⟨List.nodup_nil, fun i => by simp⟩

theorem not_live_length {L : List ℕ} {K : KStore} (hL : KRel L K) : K.length ∉ L := by
  intro h
  obtain ⟨C, hC⟩ := (hL.2 _).1 h
  simp at hC

theorem kRel_alloc {L : List ℕ} {K : KStore} (hL : KRel L K) (C : ContFX) :
    KRel (K.length :: L) (K ++ [some C]) := by
  refine ⟨List.nodup_cons.2 ⟨not_live_length hL, hL.1⟩, fun i => ?_⟩
  rcases Nat.lt_trichotomy i K.length with hi | rfl | hi
  · rw [List.getElem?_append_left hi]
    simp [Nat.ne_of_lt hi, hL.2 i]
  · simp
  · have hn : ¬ i < K.length := by omega
    have hnL : i ∉ L := fun hm => by
      obtain ⟨C', hC'⟩ := (hL.2 i).1 hm
      have := (List.getElem?_eq_some_iff.1 hC').1
      omega
    rw [List.getElem?_append_right (by omega)]
    have : i - K.length ≠ 0 := by omega
    simp [Nat.ne_of_gt hi, hnL, this]

theorem kRel_consume {L : List ℕ} {K : KStore} {k : ℕ} (hL : KRel L K) :
    KRel (L.erase k) (K.set k none) := by
  refine ⟨hL.1.erase k, fun i => ?_⟩
  rw [hL.1.mem_erase_iff]
  by_cases hik : i = k
  · subst hik
    simp [List.getElem?_set_self']
  · simp [hik, List.getElem?_set_ne (Ne.symm hik), hL.2 i]

theorem alloc_step {L : List ℕ} {K : KStore} (hL : KRel L K) (r : Role) :
    handleStep r (some L) (.alloc K.length) = some (some (K.length :: L)) := by
  simp [handleStep, not_live_length hL]

theorem free_step {L : List ℕ} {K : KStore} {k : ℕ} {C : ContFX} (hL : KRel L K)
    (hk : K[k]? = some (some C)) (r : Role) :
    handleStep r (some L) (.free k) = some (some (L.erase k)) := by
  have hkL : k ∈ L := (hL.2 k).2 ⟨C, hk⟩
  simp [handleStep, hkL]

theorem step_eq (r : Role) : (handleProto ℕ r).step = handleStep r := rfl

theorem run_alloc {L : List ℕ} {K : KStore} (hL : KRel L K) (C : ContFX) (r : Role) :
    ∃ L', (handleProto ℕ r).run (some L) [.alloc K.length] = some (some L') ∧
      KRel L' (K ++ [some C]) := by
  refine ⟨_, ?_, kRel_alloc hL C⟩
  rw [Protocol.run_cons, step_eq, alloc_step hL]
  rfl

theorem run_free {L : List ℕ} {K : KStore} {k : ℕ} {C : ContFX} (hL : KRel L K)
    (hk : K[k]? = some (some C)) (r : Role) :
    ∃ L', (handleProto ℕ r).run (some L) [.free k] = some (some L') ∧ KRel L' (K.set k none) := by
  refine ⟨_, ?_, kRel_consume hL⟩
  rw [Protocol.run_cons, step_eq, free_step hL hk]
  rfl

theorem run_swap {L : List ℕ} {K : KStore} {k : ℕ} {C : ContFX} (hL : KRel L K)
    (hk : K[k]? = some (some C)) (C' : ContFX) (r : Role) :
    ∃ L', (handleProto ℕ r).run (some L) [.free k, .alloc K.length] = some (some L') ∧
      KRel L' (K.set k none ++ [some C']) := by
  obtain ⟨L₁, h₁, hL₁⟩ := run_free hL hk r
  have hlen : (K.set k none).length = K.length := List.length_set
  obtain ⟨L₂, h₂, hL₂⟩ := run_alloc hL₁ C' r
  rw [hlen] at h₂
  refine ⟨L₂, ?_, hL₂⟩
  have hsplit : [HEv.free k, HEv.alloc K.length] = [HEv.free k] ++ [HEv.alloc K.length] := rfl
  rw [hsplit, Protocol.run_append, h₁]
  exact h₂

/-- **One store change is accepted** by the handle protocol in either orientation. -/
theorem kstep_run {K K' : KStore} {evs : List (HEv ℕ)} (h : KStep K K' evs) (r : Role)
    {L : List ℕ} (hL : KRel L K) :
    ∃ L', (handleProto ℕ r).run (some L) evs = some (some L') ∧ KRel L' K' := by
  cases h with
  | same => exact ⟨L, rfl, hL⟩
  | alloc C => exact run_alloc hL C r
  | consume hk => exact run_free hL hk r
  | swap C' hk => exact run_swap hL hk C' r

/-- **Every sequence of store changes is accepted** from a related state. -/
theorem ksteps_run {K K' : KStore} {evs : List (HEv ℕ)} (h : KSteps K K' evs) (r : Role) :
    ∀ {L : List ℕ}, KRel L K →
      ∃ L', (handleProto ℕ r).run (some L) evs = some (some L') ∧ KRel L' K' := by
  induction h with
  | refl => exact fun hL => ⟨_, rfl, hL⟩
  | cons h₁ _ ih =>
    intro L hL
    obtain ⟨L₁, hr₁, hL₁⟩ := kstep_run h₁ r hL
    obtain ⟨L₂, hr₂, hL₂⟩ := ih hL₁
    exact ⟨L₂, by rw [Protocol.run_append, hr₁]; exact hr₂, hL₂⟩

/-! ## Persistence and the one-shot budget -/

theorem kstep_consumed {K K' : KStore} {evs : List (HEv ℕ)} (h : KStep K K' evs) {k : ℕ}
    (hk : Consumed K k) : Consumed K' k := by
  unfold Consumed at *
  have hlt : k < K.length := (List.getElem?_eq_some_iff.1 hk).1
  cases h with
  | same => exact hk
  | alloc C => rw [List.getElem?_append_left hlt]; exact hk
  | consume hj =>
    rename_i j _
    by_cases hkj : k = j
    · subst hkj; simp [hlt]
    · rw [List.getElem?_set_ne (Ne.symm hkj)]; exact hk
  | swap C' hj =>
    rename_i j _
    rw [List.getElem?_append_left (by simpa using hlt)]
    by_cases hkj : k = j
    · subst hkj; simp [hlt]
    · rw [List.getElem?_set_ne (Ne.symm hkj)]; exact hk

theorem ksteps_consumed {K K' : KStore} {evs : List (HEv ℕ)} (h : KSteps K K' evs) {k : ℕ}
    (hk : Consumed K k) : Consumed K' k := by
  induction h with
  | refl => exact hk
  | cons h₁ _ ih => exact ih (kstep_consumed h₁ hk)

theorem budget_le_one (K : KStore) (k : ℕ) : budget K k ≤ 1 := by
  unfold budget
  split <;> simp

theorem budget_append_left {K : KStore} {k : ℕ} (hk : k < K.length) (C : ContFX) :
    budget (K ++ [some C]) k = budget K k := by
  simp [budget, List.getElem?_append_left hk]

theorem budget_ge_length {K : KStore} {k : ℕ} (hk : K.length ≤ k) (K' : KStore) :
    budget (K ++ K') k = budget K' (k - K.length) ∧ budget K k = 1 := by
  refine ⟨by simp [budget, List.getElem?_append_right hk], ?_⟩
  simp [budget, List.getElem?_eq_none hk]

theorem budget_singleton_some (C : ContFX) (j : ℕ) : budget [some C] j = 1 := by
  cases j <;> simp [budget]

theorem budget_set_ne {K : KStore} {k j : ℕ} (hkj : k ≠ j) :
    budget (K.set j none) k = budget K k := by
  simp [budget, List.getElem?_set_ne (Ne.symm hkj)]

theorem budget_alloc (K : KStore) (C : ContFX) (k : ℕ) :
    budget (K ++ [some C]) k = budget K k := by
  by_cases hk : k < K.length
  · exact budget_append_left hk C
  · obtain ⟨h₁, h₂⟩ := budget_ge_length (Nat.le_of_not_lt hk) [some C]
    rw [h₁, h₂, budget_singleton_some]

theorem count_free_ne {k j : ℕ} (hkj : k ≠ j) : [HEv.free j].count (HEv.free k) = 0 := by
  simp [Ne.symm hkj]

theorem count_free_alloc (k j n : ℕ) :
    [HEv.free j, HEv.alloc n].count (HEv.free k) = [HEv.free j].count (HEv.free k) := by
  simp [List.count_cons]

theorem budget_consume_self {K : KStore} {k : ℕ} {C : ContFX} (hj : K[k]? = some (some C)) :
    budget K k = 1 ∧ budget (K.set k none) k = 0 := by
  have hlt : k < K.length := (List.getElem?_eq_some_iff.1 hj).1
  have h1 : budget K k = 1 := by unfold budget; rw [hj]
  have h0 : budget (K.set k none) k = 0 := by unfold budget; simp [hlt]
  exact ⟨h1, h0⟩

theorem kstep_budget_consume {K : KStore} {j : ℕ} {C : ContFX} (hj : K[j]? = some (some C))
    (k : ℕ) : [HEv.free j].count (.free k) + budget (K.set j none) k ≤ budget K k := by
  by_cases hkj : k = j
  · subst hkj
    have hb := budget_consume_self hj
    simp [hb.1, hb.2]
  · simp [count_free_ne hkj, budget_set_ne hkj]

/-- **The budget of one store change**: a `free k` uses up the budget of `k`. -/
theorem kstep_budget {K K' : KStore} {evs : List (HEv ℕ)} (h : KStep K K' evs) (k : ℕ) :
    evs.count (.free k) + budget K' k ≤ budget K k := by
  cases h with
  | same => simp
  | alloc C => simp [budget_alloc]
  | consume hj => exact kstep_budget_consume hj k
  | swap C' hj =>
    rw [count_free_alloc, budget_alloc]
    exact kstep_budget_consume hj k

theorem ksteps_budget {K K' : KStore} {evs : List (HEv ℕ)} (h : KSteps K K' evs) (k : ℕ) :
    evs.count (.free k) + budget K' k ≤ budget K k := by
  induction h with
  | refl => simp
  | cons h₁ _ ih =>
    have := kstep_budget h₁ k
    rw [List.count_append]
    omega

/-- **One-shot**: along any sequence of store changes, each index is consumed at most once. -/
theorem ksteps_count_free {K K' : KStore} {evs : List (HEv ℕ)} (h : KSteps K K' evs) (k : ℕ) :
    evs.count (.free k) ≤ 1 :=
  le_trans (Nat.le_of_add_right_le (ksteps_budget h k)) (budget_le_one K k)

end Silmaril.Wasm.Component.FXRes
