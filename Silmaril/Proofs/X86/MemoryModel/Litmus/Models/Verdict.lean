module

public import Silmaril.Proofs.X86.MemoryModel.Litmus.Models.Ax
public import Silmaril.X86.MemoryModel.Litmus.Thms

/-!
# Litmus models: verdicts from outcome lists

A test's witness depends only on the outcome (`witness_outcome`), so the verdict computed from an
exact outcome list holds (`verdictOf_holds`), and the per-test Boolean checks give the verdict
statements (`tsoVerdicts_of_check`, `xl_of_checkXl`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

theorem lookup_zip_map_key {β : Type} (ks : List Key) (g : Key → β) (k : Key) (h : k ∈ ks) :
    (ks.zip (ks.map g)).lookup k = some (g k) := by
  induction ks with
  | nil => simp at h
  | cons a ks ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup]
    by_cases hk : k = a
    · subst hk; simp
    · have : (k == a) = false := by simpa using hk
      simp only [this]
      exact ih (by simpa [hk] using h)

theorem atom_eval (f : Final) (a : Atom) : a.eval f = (Key.eval f a.key == some a.value) := by
  cases a with
  | reg t r bits v => simp [Atom.eval, Atom.key, Atom.value, Key.eval]
  | mem a n v => simp [Atom.eval, Atom.key, Atom.value, Key.eval]

theorem cond_eval (f : Final) (c : Cond) : c.eval f = c.evalK (Key.eval f) := by
  induction c with
  | tt => rfl
  | atom a => simp [Cond.eval, Cond.evalK, atom_eval]
  | not p ih => simp [Cond.eval, Cond.evalK, ih]
  | and p q ihp ihq => simp [Cond.eval, Cond.evalK, ihp, ihq]
  | or p q ihp ihq => simp [Cond.eval, Cond.evalK, ihp, ihq]

theorem evalK_congr (c : Cond) {g g' : Key → Option Nat} (h : ∀ a ∈ c.atoms, g a.key = g' a.key) :
    c.evalK g = c.evalK g' := by
  induction c with
  | tt => rfl
  | atom a => simp [Cond.evalK, h a (by simp [Cond.atoms])]
  | not p ih => simp [Cond.evalK, ih (fun a ha => h a (by simpa [Cond.atoms] using ha))]
  | and p q ihp ihq =>
    simp [Cond.evalK, ihp (fun a ha => h a (by simp [Cond.atoms, ha])),
      ihq (fun a ha => h a (by simp [Cond.atoms, ha]))]
  | or p q ihp ihq =>
    simp [Cond.evalK, ihp (fun a ha => h a (by simp [Cond.atoms, ha])),
      ihq (fun a ha => h a (by simp [Cond.atoms, ha]))]

theorem witness_atoms (t : Test) : t.witness.atoms = t.cond.atoms := by
  unfold Test.witness; split <;> rfl

/-- The witness depends only on the outcome. -/
theorem witness_outcome (t : Test) (f : Final) : t.witness.eval f = t.witnessOn (t.outcome f) := by
  rw [cond_eval]
  unfold Test.witnessOn Test.outcome
  apply evalK_congr
  intro a ha
  rw [witness_atoms] at ha
  have hk : a.key ∈ t.keys := by
    simp only [Test.keys, mem_uniq, List.mem_map]; exact ⟨a, ha, rfl⟩
  rw [lookup_zip_map_key _ _ _ hk]
  rfl

/-- **The verdict of an exact outcome list holds.** -/
theorem verdictOf_holds {t : Test} {os : List Outcome} {R : Final → Prop}
    (h : ∀ o, o ∈ os ↔ ∃ f, R f ∧ t.outcome f = o) : (t.verdictOf os).Holds t R := by
  have key : t.Allowed R ↔ os.any t.witnessOn = true := by
    simp only [Test.Allowed, List.any_eq_true]
    constructor
    · rintro ⟨f, hf, hw⟩
      exact ⟨t.outcome f, (h _).mpr ⟨f, hf, rfl⟩, by rwa [← witness_outcome]⟩
    · rintro ⟨o, ho, hw⟩
      obtain ⟨f, hf, rfl⟩ := (h o).mp ho
      exact ⟨f, hf, by rwa [witness_outcome]⟩
  unfold Test.verdictOf
  split
  · rename_i ha; exact key.mpr ha
  · rename_i ha; exact fun hA => ha (key.mp hA)

theorem sameSet_iff {a b : List Outcome} (h : sameSet a b = true) (o : Outcome) : o ∈ a ↔ o ∈ b := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, memB_iff] at h
  exact ⟨h.1 o, h.2 o⟩

theorem exists_of_isEmpty_false {α : Type} {l : List α} (h : (!l.isEmpty) = true) : ∃ a, a ∈ l := by
  cases l with
  | nil => simp at h
  | cons a _ => exact ⟨a, List.mem_cons_self⟩

/-- A nonempty exact outcome list gives a reachable final state. -/
theorem some_of_outs {t : Test} {os : List Outcome} {R : Final → Prop}
    (h : ∀ o, o ∈ os ↔ ∃ f, R f ∧ t.outcome f = o) (hne : (!os.isEmpty) = true) : ∃ f, R f := by
  obtain ⟨o, ho⟩ := exists_of_isEmpty_false hne
  obtain ⟨f, hf, _⟩ := (h o).mp ho
  exact ⟨f, hf⟩

theorem tsoVerdicts_of_check {t : Test} {T : List (List XTrace)} (h : t.checkTso T = true) :
    TsoVerdicts t T := by
  unfold Test.checkTso at h
  split at h
  · rename_i os js hop hax
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hsame, htso⟩, hsc⟩, hxl⟩, hne⟩ := h
    have hO := opOut_spec hop
    have hT : ∀ o, o ∈ outsBy js Model.tso.sel ↔ ∃ f, AxReach t T Exec.Tso f ∧ t.outcome f = o :=
      axJudge_spec hax .tso
    have hS : ∀ o, o ∈ outsBy js Model.sc.sel ↔ ∃ f, AxReach t T Exec.Sc f ∧ t.outcome f = o :=
      axJudge_spec hax .sc
    have hX : ∀ o, o ∈ outsBy js Model.xl.sel ↔ ∃ f, AxReach t T Exec.Xl f ∧ t.outcome f = o :=
      axJudge_spec hax .xl
    refine ⟨?_, ?_, ?_, ?_, ?_, some_of_outs hS hne⟩
    · intro o; rw [← hO, ← hT]; exact sameSet_iff hsame o
    · intro v hv
      rw [hv, Option.some.injEq] at htso; subst htso
      exact verdictOf_holds fun o => (sameSet_iff hsame o).symm.trans (hO o)
    · intro v hv
      rw [hv, Option.some.injEq] at htso; subst htso
      exact verdictOf_holds hT
    · intro v hv
      rw [hv, Option.some.injEq] at hsc; subst hsc
      exact verdictOf_holds hS
    · rw [hxl]; exact verdictOf_holds hX
  · cases h

theorem plainLoose_of_check {t : Test} {T : List (List XTrace)} (h : t.checkPlainLoose T = true) :
    (∀ o, (∃ f, OpReach t T f ∧ t.outcome f = o) ↔ (∃ f, AxReach t T Exec.Tso f ∧ t.outcome f = o)) ∧
      Verdict.forbidden.Holds t (OpReach t T) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Tso) ∧
      t.xl.Holds t (AxReach t T Exec.Xl) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Sc) ∧
      ∃ f, AxReach t T Exec.Sc f := by
  unfold Test.checkPlainLoose at h
  split at h
  · rename_i os js hop hax
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hsame, htso⟩, hxl⟩, hsc⟩, hne⟩ := h
    have hO := opOut_spec hop
    have hT : ∀ o, o ∈ outsBy js Model.tso.sel ↔ ∃ f, AxReach t T Exec.Tso f ∧ t.outcome f = o :=
      axJudge_spec hax .tso
    have hS : ∀ o, o ∈ outsBy js Model.sc.sel ↔ ∃ f, AxReach t T Exec.Sc f ∧ t.outcome f = o :=
      axJudge_spec hax .sc
    have hX : ∀ o, o ∈ outsBy js Model.xl.sel ↔ ∃ f, AxReach t T Exec.Xl f ∧ t.outcome f = o :=
      axJudge_spec hax .xl
    refine ⟨fun o => ?_, ?_, ?_, ?_, ?_, some_of_outs hS hne⟩
    · rw [← hO, ← hT]; exact sameSet_iff hsame o
    · have := verdictOf_holds (R := OpReach t T) fun o => (sameSet_iff hsame o).symm.trans (hO o)
      rwa [htso] at this
    · have := verdictOf_holds hT
      rwa [htso] at this
    · rw [hxl]; exact verdictOf_holds hX
    · have := verdictOf_holds hS
      rwa [hsc] at this
  · cases h

theorem loose_of_check {t : Test} {T : List (List XTrace)} (h : t.checkLoose T = true) :
    t.xl.Holds t (AxReach t T Exec.Xl) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Tso) ∧
      Verdict.forbidden.Holds t (AxReach t T Exec.Sc) ∧ ∃ f, AxReach t T Exec.Sc f := by
  unfold Test.checkLoose at h
  split at h
  · rename_i js hax
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hxl, htso⟩, hsc⟩, hne⟩ := h
    have hT : ∀ o, o ∈ outsBy js Model.tso.sel ↔ ∃ f, AxReach t T Exec.Tso f ∧ t.outcome f = o :=
      axJudge_spec hax .tso
    have hS : ∀ o, o ∈ outsBy js Model.sc.sel ↔ ∃ f, AxReach t T Exec.Sc f ∧ t.outcome f = o :=
      axJudge_spec hax .sc
    have hX : ∀ o, o ∈ outsBy js Model.xl.sel ↔ ∃ f, AxReach t T Exec.Xl f ∧ t.outcome f = o :=
      axJudge_spec hax .xl
    refine ⟨?_, ?_, ?_, some_of_outs hS hne⟩
    · rw [hxl]; exact verdictOf_holds hX
    · have := verdictOf_holds hT
      rwa [htso] at this
    · have := verdictOf_holds hS
      rwa [hsc] at this
  · cases h

theorem xl_of_checkXl {t : Test} {T : List (List XTrace)} (h : t.checkXl T = true) :
    t.xl.Holds t (AxReach t T Exec.Xl) := by
  unfold Test.checkXl at h
  split at h
  · rename_i js hax
    simp only [beq_iff_eq] at h
    rw [h]; exact verdictOf_holds (R := AxReach t T Exec.Xl) (axJudge_spec hax .xl)
  · cases h

end Silmaril.Proofs.X86.MemoryModel.Litmus
