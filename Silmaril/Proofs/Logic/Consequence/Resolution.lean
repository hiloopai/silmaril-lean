module

public import Silmaril.Logic.Consequence.Resolution.Defs

/-!
# Proofs for propositional clause reasoning: every rule preserves truth
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Resolution

open Silmaril.Consequence.Resolution
open Silmaril.Logic.Smt (SE)

variable (v : SE → Prop)

theorem holdsAny_iff : ∀ as : List SE, HoldsAny v as ↔ ∃ a ∈ as, Holds v a
  | [] => by simp [HoldsAny]
  | a :: as => by simp [HoldsAny, holdsAny_iff as]

theorem holdsAll_iff : ∀ as : List SE, HoldsAll v as ↔ ∀ a ∈ as, Holds v a
  | [] => by simp [HoldsAll]
  | a :: as => by simp [HoldsAll, holdsAll_iff as]

theorem holds_neg (t : SE) : Holds v (neg t) ↔ ¬ Holds v t := by
  simp [neg, Holds]

theorem holds_mkOr (as : List SE) : Holds v (mkOr as) ↔ ∃ a ∈ as, Holds v a := by
  rw [← holdsAny_iff]; simp [mkOr, Holds]

theorem holds_mkAnd (as : List SE) : Holds v (mkAnd as) ↔ ∀ a ∈ as, Holds v a := by
  rw [← holdsAll_iff]; simp [mkAnd, Holds]

theorem resolve_sound {pos : Bool} {p : SE} {c d e : Clause} (h : resolve pos p c d = some e)
    (hc : ClauseHolds v c) (hd : ClauseHolds v d) : ClauseHolds v e := by
  unfold resolve at h
  cases pos <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;> split at h <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · -- the pivot `(not p)` in `c`, `p` in `d`
    by_cases hp : Holds v p
    · obtain ⟨t, ht, htv⟩ := hc
      refine ⟨t, List.mem_append_left _ (List.mem_filter.2 ⟨ht, ?_⟩), htv⟩
      simp only [decide_eq_true_eq]; rintro rfl; exact (holds_neg v p).1 htv hp
    · obtain ⟨t, ht, htv⟩ := hd
      refine ⟨t, List.mem_append_right _ (List.mem_filter.2 ⟨ht, ?_⟩), htv⟩
      simp only [decide_eq_true_eq]; rintro rfl; exact hp htv
  · -- the pivot `p` in `c`, `(not p)` in `d`
    by_cases hp : Holds v p
    · obtain ⟨t, ht, htv⟩ := hd
      refine ⟨t, List.mem_append_right _ (List.mem_filter.2 ⟨ht, ?_⟩), htv⟩
      simp only [decide_eq_true_eq]; rintro rfl; exact (holds_neg v p).1 htv hp
    · obtain ⟨t, ht, htv⟩ := hc
      refine ⟨t, List.mem_append_left _ (List.mem_filter.2 ⟨ht, ?_⟩), htv⟩
      simp only [decide_eq_true_eq]; rintro rfl; exact hp htv

theorem resolveChain_sound : ∀ {c : Clause} {ps : List (SE × Bool)} {ds : List Clause} {e : Clause},
    resolveChain c ps ds = some e → ClauseHolds v c → (∀ d ∈ ds, ClauseHolds v d) →
      ClauseHolds v e
  | c, [], [], e, h, hc, _ => by simp [resolveChain] at h; exact h ▸ hc
  | c, (p, pos) :: ps, d :: ds, e, h, hc, hds => by
    simp only [resolveChain, Option.bind_eq_some_iff] at h
    obtain ⟨c', h1, h2⟩ := h
    exact resolveChain_sound h2 (resolve_sound v h1 hc (hds d List.mem_cons_self))
      (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
  | _, [], _ :: _, _, h, _, _ => by simp [resolveChain] at h
  | _, _ :: _, [], _, h, _, _ => by simp [resolveChain] at h

theorem unit_holds {t : SE} (h : ClauseHolds v [t]) : Holds v t := by
  obtain ⟨s, hs, hv⟩ := h; simp at hs; exact hs ▸ hv

/-- **Each rule's computed conclusion holds when its premises do.** -/
theorem apply_sound (r : Rule) (ps : List Clause) (d : Clause) (h : r.apply ps = some d)
    (hps : ∀ p ∈ ps, ClauseHolds v p) : ClauseHolds v d := by
  unfold Rule.apply at h
  split at h
  · -- resolution
    rename_i pivots c ds
    exact resolveChain_sound v h (hps c List.mem_cons_self)
      fun d hd => hps d (List.mem_cons_of_mem _ hd)
  · -- or
    rename_i as
    simp only [Option.some.injEq] at h; subst h
    exact (holds_mkOr v _).1 (unit_holds v (hps _ List.mem_cons_self))
  · -- and
    rename_i i as
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    have := (holds_mkAnd v as).1 (unit_holds v (hps _ List.mem_cons_self))
    exact ⟨a, List.mem_singleton_self a, this a (List.mem_of_getElem? ha)⟩
  · -- not_or
    rename_i i as
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    have h1 := unit_holds v (hps _ List.mem_cons_self)
    have h2 : ¬ Holds v (mkOr as) := (holds_neg v (mkOr as)).1 h1
    refine ⟨neg a, List.mem_singleton_self _, (holds_neg v a).2 fun ha' => h2 ?_⟩
    exact (holds_mkOr v as).2 ⟨a, List.mem_of_getElem? ha, ha'⟩
  · -- or_pos
    rename_i as
    simp only [Option.some.injEq] at h; subst h
    by_cases hor : Holds v (mkOr as)
    · obtain ⟨a, ha, hv⟩ := (holds_mkOr v as).1 hor
      exact ⟨a, List.mem_cons_of_mem _ ha, hv⟩
    · exact ⟨_, List.mem_cons_self, (holds_neg v _).2 hor⟩
  · -- or_neg
    rename_i as i
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    by_cases hv : Holds v a
    · exact ⟨mkOr as, List.mem_cons_self, (holds_mkOr v as).2 ⟨a, List.mem_of_getElem? ha, hv⟩⟩
    · exact ⟨neg a, by simp, (holds_neg v a).2 hv⟩
  · -- and_pos
    rename_i as i
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    by_cases hv : Holds v a
    · exact ⟨a, by simp, hv⟩
    · refine ⟨neg (mkAnd as), List.mem_cons_self, (holds_neg v _).2 fun hand => hv ?_⟩
      exact (holds_mkAnd v as).1 hand a (List.mem_of_getElem? ha)
  · -- and_neg
    rename_i as
    simp only [Option.some.injEq] at h; subst h
    by_cases hall : ∀ a ∈ as, Holds v a
    · exact ⟨mkAnd as, List.mem_cons_self, (holds_mkAnd v as).2 hall⟩
    · push Not at hall
      obtain ⟨a, ha, hv⟩ := hall
      exact ⟨neg a, List.mem_cons_of_mem _ (List.mem_map_of_mem ha), (holds_neg v a).2 hv⟩
  · -- contraction
    simp only [Option.some.injEq] at h; subst h
    exact hps _ List.mem_cons_self
  · -- true
    simp only [Option.some.injEq] at h; subst h
    exact ⟨_, List.mem_singleton_self _, by simp [Holds]⟩
  · -- false
    simp only [Option.some.injEq] at h; subst h
    exact ⟨_, List.mem_singleton_self _, (holds_neg v _).2 (by simp [Holds])⟩
  · cases h

end Silmaril.Proofs.Logic.Consequence.Resolution
