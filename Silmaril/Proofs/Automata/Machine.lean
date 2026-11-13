module

public import Silmaril.Automata.Machine.Defs

/-!
# Finite machines: proofs

For `Silmaril.Automata.Machine.Thms`: the deterministic machines inside the nondeterministic
ones, runs as CSLib multistep transitions, the NFA bridge, synchronous products, and language
nonemptiness as reachability.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Silmaril.Automata

variable {S T L : Type}

theorem toN_toLTS (M : DMachine S L) : M.toN.toLTS = M.toLTS := by
  unfold NMachine.toLTS DMachine.toN DMachine.toLTS
  congr 1; funext s l s'
  simp [Option.mem_toFinset]

theorem run_append (M : DMachine S L) (s : S) (w v : List L) :
    M.run s (w ++ v) = (M.run s w).bind fun s' => M.run s' v := by
  induction w generalizing s with
  | nil => simp [DMachine.run]
  | cons l w ih =>
    simp only [List.cons_append, DMachine.run]
    cases M.step s l with
    | none => rfl
    | some s' => exact ih s'

theorem run_some_iff_MTr (M : DMachine S L) (s : S) (w : List L) (s' : S) :
    M.run s w = some s' ↔ M.toLTS.MTr s w s' := by
  induction w generalizing s with
  | nil =>
    simp only [DMachine.run, Option.some.injEq]
    constructor
    · rintro rfl; exact .refl
    · intro h; cases h; rfl
  | cons l w ih =>
    simp only [DMachine.run]
    constructor
    · intro h
      cases hs : M.step s l with
      | none => rw [hs] at h; cases h
      | some m => rw [hs] at h; exact .stepL hs ((ih m).mp h)
    · intro h
      cases h with
      | stepL htr hrest =>
        change M.step s l = some _ at htr
        rw [htr]; exact (ih _).mpr hrest

theorem accepts_toNFA_iff (M : Marked S L) (w : List L) :
    Cslib.Automata.Acceptor.Accepts M.toNFA w ↔ M.Accepts w := by
  constructor
  · rintro ⟨s, hs, s', hs', hm⟩
    exact ⟨s, hs, s', (run_some_iff_MTr M.machine s w s').mpr hm, hs'⟩
  · rintro ⟨s, hs, s', hr, hs'⟩
    exact ⟨s, hs, s', hs', (run_some_iff_MTr M.machine s w s').mp hr⟩

theorem prod_step_iff (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) (l : L) (s' : S)
    (t' : T) : (M.prod N).step (s, t) l = some (s', t') ↔
      M.step s l = some s' ∧ N.step t l = some t' := by
  simp only [DMachine.prod]
  cases M.step s l <;> cases N.step t l <;> simp

theorem prod_run_iff (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) (w : List L)
    (s' : S) (t' : T) : (M.prod N).run (s, t) w = some (s', t') ↔
      M.run s w = some s' ∧ N.run t w = some t' := by
  induction w generalizing s t with
  | nil => simp [DMachine.run]
  | cons l w ih =>
    simp only [DMachine.run]
    cases hm : M.step s l with
    | none =>
      have : (M.prod N).step (s, t) l = none := by simp [DMachine.prod, hm]
      simp [this]
    | some m =>
      cases hn : N.step t l with
      | none =>
        have : (M.prod N).step (s, t) l = none := by simp [DMachine.prod, hm, hn]
        simp [this]
      | some n =>
        have : (M.prod N).step (s, t) l = some (m, n) := by simp [DMachine.prod, hm, hn]
        simp only [this, Option.bind_some]
        exact ih m n

theorem accepts_prod_iff (M : Marked S L) (N : Marked T L) (w : List L) :
    (M.prod N).Accepts w ↔ M.Accepts w ∧ N.Accepts w := by
  constructor
  · rintro ⟨⟨s, t⟩, hi, ⟨s', t'⟩, hr, ha⟩
    simp only [Marked.prod, Marks.prod, Bool.and_eq_true] at hi ha hr
    obtain ⟨h1, h2⟩ := (prod_run_iff M.machine N.machine s t w s' t').mp hr
    exact ⟨⟨s, hi.1, s', h1, ha.1⟩, ⟨t, hi.2, t', h2, ha.2⟩⟩
  · rintro ⟨⟨s, hs, s', hr, ha⟩, ⟨t, ht, t', hr', ha'⟩⟩
    refine ⟨(s, t), ?_, (s', t'), ?_, ?_⟩
    · simp [Marked.prod, Marks.prod, hs, ht]
    · exact (prod_run_iff M.machine N.machine s t w s' t').mpr ⟨hr, hr'⟩
    · simp [Marked.prod, Marks.prod, ha, ha']

theorem reach_iff_run (M : DMachine S L) (s t : S) :
    ReachVia M.toLTS (fun _ => True) s t ↔ ∃ w, M.run s w = some t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hst ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨l, -, htr⟩ := hst
      refine ⟨w ++ [l], ?_⟩
      rw [run_append, hw]
      simp only [Option.bind_some, DMachine.run]
      change M.step _ l = some _ at htr
      rw [htr]; rfl
  · rintro ⟨w, hw⟩
    induction w generalizing s with
    | nil => simp [DMachine.run] at hw; subst hw; exact Relation.ReflTransGen.refl
    | cons l w ih =>
      simp only [DMachine.run] at hw
      cases hs : M.step s l with
      | none => rw [hs] at hw; cases hw
      | some m =>
        rw [hs] at hw
        exact Relation.ReflTransGen.head ⟨l, trivial, hs⟩ (ih m hw)

theorem nonempty_iff_reach (M : Marked S L) :
    (∃ w, M.Accepts w) ↔ ∃ s, M.marks.initial s = true ∧ ∃ t, M.marks.accepting t = true ∧
      ReachVia M.machine.toLTS (fun _ => True) s t := by
  constructor
  · rintro ⟨w, s, hs, t, hr, ht⟩
    exact ⟨s, hs, t, ht, (reach_iff_run M.machine s t).mpr ⟨w, hr⟩⟩
  · rintro ⟨s, hs, t, ht, hr⟩
    obtain ⟨w, hw⟩ := (reach_iff_run M.machine s t).mp hr
    exact ⟨w, s, hs, t, hw, ht⟩

theorem nprod_tr_iff (M : NMachine S L) (N : NMachine T L) (s : S) (t : T) (l : L) (s' : S)
    (t' : T) : (M.prod N).toLTS.Tr (s, t) l (s', t') ↔ M.toLTS.Tr s l s' ∧ N.toLTS.Tr t l t' := by
  simp [NMachine.prod, NMachine.toLTS, Finset.mem_product]

end Silmaril.Proofs.Automata
