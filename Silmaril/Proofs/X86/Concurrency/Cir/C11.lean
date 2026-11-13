module

public import Silmaril.X86.Concurrency.Cir.C11.Defs
public import Silmaril.X86.Concurrency.Cir.Rc11.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# C11 litmus tests on CIR: the check is sound

The flags `C11Test.flags` mean what `C11Test.check` reads them as:

* `rc11_agrees`: RC11 consistency and raciness depend on a candidate only through what the
  enumerator's agreement relation preserves, so the enumerator (`candidates`, complete by
  `candidates_complete`) is complete for RC11 too;
* `flags_bit`: a flag is set iff some enumerated candidate sets it;
* `enum_reach` (soundness) and `reach_enum` (completeness): an enumerated candidate is a
  behaviour, and every behaviour under a model without `com` two-cycles is an enumerated
  candidate up to agreement;
* `C11Test.holds_of_check`: everything together (`C11Test.Holds`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.C11

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.C11
open Silmaril.X86.Concurrency.Cir.Rc11 (Consistent Racy)
open Silmaril.X86.MemoryModel.Litmus (Test XTrace Byte Verdict units rmwPairs cellsOk candidates
  readsOkB ReadsOk finalAx seqL AxReach mkExec readsOf cellsOf rfChoices arrangements writesIn
  Agrees candidates_complete)
open Silmaril.X86.MemoryModel.Axiomatic (Exec Ev)

/-! ## Lists and bits -/

theorem mem_seqL {α : Type} (l : List α) (ls : List (List α)) :
    l ∈ seqL ls ↔ List.Forall₂ (· ∈ ·) l ls := by
  induction ls generalizing l with
  | nil =>
    simp only [seqL, List.mem_singleton]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | cons m ls ih =>
    simp only [seqL, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, l', hl', rfl⟩
      exact .cons ha ((ih l').mp hl')
    · intro h
      cases h with
      | cons ha hrest => exact ⟨_, ha, _, (ih _).mpr hrest, rfl⟩

theorem readsOkB_iff {t : Test} {x : Exec} {exps : List (List Byte)} :
    readsOkB t x exps = true ↔ ReadsOk t x exps := by
  simp only [readsOkB, ReadsOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq]
  constructor
  · intro h r hr hR
    rcases h r hr with h | h
    · rw [hR] at h; cases h
    · exact h
  · intro h r hr
    cases hR : (x.evN r).isR
    · exact Or.inl rfl
    · exact Or.inr (h r hr hR)

theorem testBit_foldl_or {α : Type} (f : α → Nat) (i : Nat) :
    ∀ (l : List α) (acc : Nat), (l.foldl (fun a y => a ||| f y) acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ y ∈ l, (f y).testBit i = true
  | [], acc => by simp
  | y :: l, acc => by
    rw [List.foldl_cons, testBit_foldl_or f i l, Nat.testBit_or, Bool.or_eq_true]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem testBit_foldl_or0 {α : Type} (f : α → Nat) (i : Nat) (l : List α) :
    (l.foldl (fun a y => a ||| f y) 0).testBit i = true ↔ ∃ y ∈ l, (f y).testBit i = true := by
  rw [testBit_foldl_or]; simp

/-! ## The flags of one candidate -/

theorem flagsOf_bit (xl tso rc racy w : Bool) :
    (flagsOf xl tso rc racy w).testBit 0 = (xl && !rc) ∧
    (flagsOf xl tso rc racy w).testBit 1 = (rc && racy) ∧
    (flagsOf xl tso rc racy w).testBit 2 = (rc && w) ∧
    (flagsOf xl tso rc racy w).testBit 3 = (xl && w) ∧
    (flagsOf xl tso rc racy w).testBit 4 = rc ∧
    (flagsOf xl tso rc racy w).testBit 5 = xl ∧
    (flagsOf xl tso rc racy w).testBit 6 = false ∧
    (flagsOf xl tso rc racy w).testBit 7 = (tso && w) := by
  cases xl <;> cases tso <;> cases rc <;> cases racy <;> cases w <;> decide

/-- The XL flag of a candidate. -/
def xlB (x : Exec) : Bool := decide x.Tso || (!decide x.Tame && decide x.Xl)

theorem xlB_iff {x : Exec} : xlB x = true ↔ x.Xl := by
  unfold xlB
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    rcases h with h | h
    · exact x.xl_of_tso h
    · exact h.2
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    by_cases ht : x.Tso
    · exact Or.inl ht
    · exact Or.inr ⟨fun hT => ht ((x.xl_iff_tso_of_tame hT).mp h), h⟩

theorem candFlags_eq {P : Prog} {t : Test} {trs : List XTrace} {exps : List (List Byte)} {x : Exec}
    (hw : (x.Wf && readsOkB t x exps) = true) {rc racy : Bool}
    (hj : Rc11.judge (P.roles x) x = some (rc, racy)) :
    candFlags P t trs exps x =
      flagsOf (xlB x) (decide x.Tso) rc racy (t.witness.eval (finalAx t trs x)) := by
  unfold candFlags xlB
  rw [ite_eq_left hw, hj]
  simp only
  cases hT : decide x.Tso <;> cases hX : (!decide x.Tame && decide x.Xl) <;>
    cases hW : t.witness.eval (finalAx t trs x) <;> rfl

theorem candFlags_none {P : Prog} {t : Test} {trs : List XTrace} {exps : List (List Byte)}
    {x : Exec} (hw : (x.Wf && readsOkB t x exps) = true) (hj : Rc11.judge (P.roles x) x = none) :
    candFlags P t trs exps x = 64 := by
  unfold candFlags; rw [ite_eq_left hw, hj]

theorem candFlags_bad {P : Prog} {t : Test} {trs : List XTrace} {exps : List (List Byte)}
    {x : Exec} (hw : (x.Wf && readsOkB t x exps) = false) : candFlags P t trs exps x = 0 := by
  unfold candFlags; rw [ite_eq_right (by simp [hw])]

/-! ## The enumeration -/

/-- The units, expected reads and locked pairs of a choice of runs. -/
def evsOf (trs : List XTrace) : List Ev := (units trs).map Prod.fst
def expsOf (trs : List XTrace) : List (List Byte) := (units trs).map Prod.snd

/-- `x` is an enumerated, well-formed candidate with the right reads for the runs `trs`. -/
def IsEnum (t : Test) (T : List (List XTrace)) (trs : List XTrace) (x : Exec) : Prop :=
  trs ∈ seqL T ∧ x ∈ candidates t (evsOf trs) (expsOf trs) (rmwPairs (evsOf trs)) ∧
    (x.Wf && readsOkB t x (expsOf trs)) = true

theorem flags_bit {P : Prog} {t : Test} {T : List (List XTrace)}
    (h6 : (progFlags P t T).testBit 6 = false) :
    (∀ trs ∈ seqL T, cellsOk (evsOf trs) = true) ∧
    (∀ trs x, IsEnum t T trs x → ∃ rc racy, Rc11.judge (P.roles x) x = some (rc, racy)) ∧
    ∀ i, i ≠ 6 → ((progFlags P t T).testBit i = true ↔
      ∃ trs x, IsEnum t T trs x ∧ ∃ rc racy, Rc11.judge (P.roles x) x = some (rc, racy) ∧
        (flagsOf (xlB x) (decide x.Tso) rc racy (t.witness.eval (finalAx t trs x))).testBit i =
          true) := by
  have hS : ∀ i, (progFlags P t T).testBit i = true ↔
      ∃ trs ∈ seqL T, (comboFlags P t trs).testBit i = true := fun i =>
    testBit_foldl_or0 _ i _
  have hcells : ∀ trs ∈ seqL T, cellsOk (evsOf trs) = true := by
    intro trs htrs
    by_contra hc
    have : (comboFlags P t trs).testBit 6 = true := by
      unfold comboFlags; simp only; rw [ite_eq_right (by simpa [evsOf] using hc)]; decide
    have := (hS 6).mpr ⟨trs, htrs, this⟩
    rw [h6] at this; cases this
  have hcombo : ∀ trs ∈ seqL T, ∀ i, (comboFlags P t trs).testBit i = true ↔
      ∃ x ∈ candidates t (evsOf trs) (expsOf trs) (rmwPairs (evsOf trs)),
        (candFlags P t trs (expsOf trs) x).testBit i = true := by
    intro trs htrs i
    unfold comboFlags
    simp only
    rw [ite_eq_left (by simpa [evsOf] using hcells trs htrs)]
    exact testBit_foldl_or0 _ i _
  have hjudge : ∀ trs x, IsEnum t T trs x → ∃ rc racy, Rc11.judge (P.roles x) x = some (rc, racy) := by
    rintro trs x ⟨htrs, hx, hw⟩
    cases hj : Rc11.judge (P.roles x) x with
    | none =>
      have : (candFlags P t trs (expsOf trs) x).testBit 6 = true := by
        rw [candFlags_none hw hj]; decide
      have := (hS 6).mpr ⟨trs, htrs, (hcombo trs htrs 6).mpr ⟨x, hx, this⟩⟩
      rw [h6] at this; cases this
    | some p => exact ⟨p.1, p.2, rfl⟩
  refine ⟨hcells, hjudge, fun i hi => ?_⟩
  rw [hS]
  constructor
  · rintro ⟨trs, htrs, hb⟩
    obtain ⟨x, hx, hb⟩ := (hcombo trs htrs i).mp hb
    cases hw : (x.Wf && readsOkB t x (expsOf trs))
    · rw [candFlags_bad hw] at hb; simp at hb
    · obtain ⟨rc, racy, hj⟩ := hjudge trs x ⟨htrs, hx, hw⟩
      rw [candFlags_eq hw hj] at hb
      exact ⟨trs, x, ⟨htrs, hx, hw⟩, rc, racy, hj, hb⟩
  · rintro ⟨trs, x, ⟨htrs, hx, hw⟩, rc, racy, hj, hb⟩
    exact ⟨trs, htrs, (hcombo trs htrs i).mpr ⟨x, hx, by rw [candFlags_eq hw hj]; exact hb⟩⟩

theorem mem_candidates_evs {t : Test} {evs : List Ev} {exps : List (List Byte)}
    {rmw : List (Nat × Nat)} {x : Exec} (h : x ∈ candidates t evs exps rmw) :
    x.evs = evs ∧ x.rmw = rmw := by
  simp only [candidates, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- **Soundness**: an enumerated candidate consistent under `M` is a behaviour. -/
theorem enum_reach {t : Test} {T : List (List XTrace)} {trs : List XTrace} {x : Exec}
    (h : IsEnum t T trs x) {M : Exec → Prop} (hM : M x) : AxReach t T M (finalAx t trs x) := by
  obtain ⟨htrs, hx, hw⟩ := h
  simp only [Bool.and_eq_true] at hw
  obtain ⟨he, hr⟩ := mem_candidates_evs hx
  exact ⟨trs, (mem_seqL _ _).mp htrs, x, he, hr, hw.1, readsOkB_iff.mp hw.2, hM, rfl⟩

/-! ## RC11 is blind to agreement -/

section Agree
variable {evs : List Ev} {rf rf' : Nat → Nat → Option Nat} {co co' : Nat → List Nat}
  {rmw : List (Nat × Nat)} {ro : Nat → Role}

theorem rc11_congr (h1 : Exec.rfR ⟨evs, rf, co, rmw⟩ = Exec.rfR ⟨evs, rf', co', rmw⟩)
    (h2 : Exec.coR ⟨evs, rf, co, rmw⟩ = Exec.coR ⟨evs, rf', co', rmw⟩)
    (h3 : Exec.frR ⟨evs, rf, co, rmw⟩ = Exec.frR ⟨evs, rf', co', rmw⟩) :
    (Consistent ro ⟨evs, rf, co, rmw⟩ ↔ Consistent ro ⟨evs, rf', co', rmw⟩) ∧
      (Racy ro ⟨evs, rf, co, rmw⟩ ↔ Racy ro ⟨evs, rf', co', rmw⟩) := by
  have hrf : Rc11.rf ro ⟨evs, rf, co, rmw⟩ = Rc11.rf ro ⟨evs, rf', co', rmw⟩ := by
    unfold Rc11.rf; rw [h1]; rfl
  have hmo : Rc11.mo ro ⟨evs, rf, co, rmw⟩ = Rc11.mo ro ⟨evs, rf', co', rmw⟩ := by
    unfold Rc11.mo; rw [h2]; rfl
  have hfr : Rc11.fr ro ⟨evs, rf, co, rmw⟩ = Rc11.fr ro ⟨evs, rf', co', rmw⟩ := by
    unfold Rc11.fr; rw [h3]; rfl
  have hcom : Exec.com ⟨evs, rf, co, rmw⟩ = Exec.com ⟨evs, rf', co', rmw⟩ := by
    unfold Exec.com; rw [h1, h2, h3]
  have hat : Exec.atomicB ⟨evs, rf, co, rmw⟩ = Exec.atomicB ⟨evs, rf', co', rmw⟩ := by
    unfold Exec.atomicB Exec.fre Exec.coe; rw [h2, h3]; rfl
  have hRs : Rc11.Rs ro ⟨evs, rf, co, rmw⟩ = Rc11.Rs ro ⟨evs, rf', co', rmw⟩ := by
    funext a b; unfold Rc11.Rs Rc11.RfRmwStar; rw [hrf]; rfl
  have hSw : Rc11.Sw ro ⟨evs, rf, co, rmw⟩ = Rc11.Sw ro ⟨evs, rf', co', rmw⟩ := by
    funext a b; unfold Rc11.Sw; rw [hRs, hrf]; rfl
  have hHb : Rc11.Hb ro ⟨evs, rf, co, rmw⟩ = Rc11.Hb ro ⟨evs, rf', co', rmw⟩ := by
    funext a b; unfold Rc11.Hb; rw [hSw]; rfl
  have hEco : Rc11.Eco ro ⟨evs, rf, co, rmw⟩ = Rc11.Eco ro ⟨evs, rf', co', rmw⟩ := by
    funext a b; unfold Rc11.Eco; rw [hrf, hmo, hfr]
  have hScb : Rc11.Scb ro ⟨evs, rf, co, rmw⟩ = Rc11.Scb ro ⟨evs, rf', co', rmw⟩ := by
    funext a b; unfold Rc11.Scb; rw [hHb, hmo, hfr]; rfl
  have hPsc : Rc11.Psc ro ⟨evs, rf, co, rmw⟩ = Rc11.Psc ro ⟨evs, rf', co', rmw⟩ := by
    funext a b; unfold Rc11.Psc Rc11.PscBase Rc11.PscF; rw [hHb, hScb, hEco]; rfl
  constructor
  · constructor
    · rintro ⟨w, c, at', s, n⟩
      exact ⟨by rw [← hcom]; exact w, by rw [← hHb, ← hEco]; exact c, by rw [← hat]; exact at',
        by rw [← hPsc]; exact s, by rw [← hrf]; exact n⟩
    · rintro ⟨w, c, at', s, n⟩
      exact ⟨by rw [hcom]; exact w, by rw [hHb, hEco]; exact c, by rw [hat]; exact at',
        by rw [hPsc]; exact s, by rw [hrf]; exact n⟩
  · unfold Racy; rw [hHb]; rfl

end Agree

/-- **RC11 consistency and raciness are blind to agreement.** -/
theorem rc11_agrees {P : Prog} {x x' : Exec} (h : Agrees x x') :
    (P.Rc11 x ↔ P.Rc11 x') ∧ (P.Rc11Racy x ↔ P.Rc11Racy x') := by
  obtain ⟨evs, rf, co, rmw⟩ := x
  obtain ⟨evs', rf', co', rmw'⟩ := x'
  have he : evs = evs' := h.evs
  have hr : rmw = rmw' := h.rmw
  subst he hr
  obtain ⟨h1, h2, h3⟩ := h.rels
  have := rc11_congr (ro := P.roles ⟨evs, rf, co, rmw⟩) h1 h2 h3
  unfold Prog.Rc11 Prog.Rc11Racy
  exact ⟨this.1, and_congr this.1 this.2⟩

theorem tame_agrees {x x' : Exec} (h : Agrees x x') : x.Tame ↔ x'.Tame := by
  obtain ⟨evs, rf, co, rmw⟩ := x
  obtain ⟨evs', rf', co', rmw'⟩ := x'
  have he : evs = evs' := h.evs
  have hr : rmw = rmw' := h.rmw
  subst he hr
  exact Iff.rfl

/-- **Completeness for one candidate**: a candidate without `com` two-cycles agrees with an
enumerated one. -/
theorem enum_of_cand {t : Test} {T : List (List XTrace)}
    (hcells : ∀ trs ∈ seqL T, cellsOk (evsOf trs) = true) {trs : List XTrace}
    (htrs : List.Forall₂ (· ∈ ·) trs T) {x : Exec} (hevs : x.evs = (units trs).map Prod.fst)
    (hrmw : x.rmw = rmwPairs ((units trs).map Prod.fst)) (hwf : x.Wf = true)
    (hro : ReadsOk t x ((units trs).map Prod.snd))
    (hn : ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False) :
    ∃ x', IsEnum t T trs x' ∧ Agrees x x' ∧ finalAx t trs x = finalAx t trs x' := by
  have hs := (mem_seqL _ _).mpr htrs
  obtain ⟨x', hx', hag⟩ := candidates_complete t (hcells trs hs) hevs hrmw hwf hro hn
  obtain ⟨-, -, -, hwf', hro', hfin⟩ := hag.models
  refine ⟨x', ⟨hs, hx', ?_⟩, hag, hfin t trs⟩
  simp only [Bool.and_eq_true]
  exact ⟨hwf'.symm.trans hwf, readsOkB_iff.mpr ((hro' t _).mp hro)⟩

/-- **Completeness**: a behaviour under a model whose executions have no `com` two-cycle is an
enumerated candidate up to agreement (when every choice of runs has its units in cells). -/
theorem reach_enum {t : Test} {T : List (List XTrace)}
    (hcells : ∀ trs ∈ seqL T, cellsOk (evsOf trs) = true) {M : Exec → Prop}
    (hn : ∀ x, M x → ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False) {f}
    (h : AxReach t T M f) :
    ∃ trs x x', IsEnum t T trs x' ∧ Agrees x x' ∧ M x ∧ f = finalAx t trs x' := by
  obtain ⟨trs, htrs, x, hevs, hrmw, hwf, hro, hM, rfl⟩ := h
  obtain ⟨x', he, hag, hfin⟩ := enum_of_cand hcells htrs hevs hrmw hwf hro (hn x hM)
  exact ⟨trs, x, x', he, hag, hM, hfin⟩

/-! ## Flags and verdicts -/

section Verdicts
variable {P : Prog} {t : Test} {T : List (List XTrace)}

/-- A flag that marks exactly the enumerated candidates consistent under `M` whose final state
satisfies the witness decides the verdict of `M`. -/
theorem bit_allowed (h6 : (progFlags P t T).testBit 6 = false) {i : Nat} (hi : i ≠ 6)
    {M : Exec → Prop}
    (hflag : ∀ trs x rc racy, IsEnum t T trs x → Rc11.judge (P.roles x) x = some (rc, racy) →
      ((flagsOf (xlB x) (decide x.Tso) rc racy (t.witness.eval (finalAx t trs x))).testBit i =
        true ↔ M x ∧ t.witness.eval (finalAx t trs x) = true))
    (hag : ∀ x x', Agrees x x' → M x → M x')
    (hn : ∀ x, M x → ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False) :
    (progFlags P t T).testBit i = true ↔ Verdict.allowed.Holds t (AxReach t T M) := by
  obtain ⟨hcells, hjudge, hbit⟩ := flags_bit h6
  rw [hbit i hi]
  constructor
  · rintro ⟨trs, x, he, rc, racy, hj, hb⟩
    obtain ⟨hM, hw⟩ := (hflag trs x rc racy he hj).mp hb
    exact ⟨_, enum_reach he hM, by rw [Silmaril.X86.MemoryModel.Litmus.Test.witness] at hw ⊢; exact hw⟩
  · rintro ⟨f, hf, hw⟩
    obtain ⟨trs, x, x', he, hagr, hM, rfl⟩ := reach_enum hcells hn hf
    obtain ⟨rc, racy, hj⟩ := hjudge trs x' he
    exact ⟨trs, x', he, rc, racy, hj, (hflag trs x' rc racy he hj).mpr ⟨hag x x' hagr hM, hw⟩⟩

theorem verdict_of_bit (h6 : (progFlags P t T).testBit 6 = false) {i : Nat} (hi : i ≠ 6)
    {M : Exec → Prop}
    (hflag : ∀ trs x rc racy, IsEnum t T trs x → Rc11.judge (P.roles x) x = some (rc, racy) →
      ((flagsOf (xlB x) (decide x.Tso) rc racy (t.witness.eval (finalAx t trs x))).testBit i =
        true ↔ M x ∧ t.witness.eval (finalAx t trs x) = true))
    (hag : ∀ x x', Agrees x x' → M x → M x')
    (hn : ∀ x, M x → ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False) :
    (bitVerdict (progFlags P t T) i).Holds t (AxReach t T M) := by
  have := bit_allowed h6 hi hflag hag hn
  unfold bitVerdict
  split
  · exact this.mp (by assumption)
  · rename_i hb
    exact fun ha => hb (this.mpr ha)

/-- The judge's Booleans together are a racy RC11-consistent execution. -/
theorem judge_racy {x : Exec} {rc racy : Bool} (hj : Rc11.judge (P.roles x) x = some (rc, racy)) :
    (rc && racy) = true ↔ P.Rc11Racy x := by
  have := Rc11.judge_spec hj
  unfold Prog.Rc11Racy
  rw [Bool.and_eq_true, this.1, this.2]

theorem judge_rc' {x : Exec} {rc racy : Bool} (hj : Rc11.judge (P.roles x) x = some (rc, racy)) :
    rc = true ↔ P.Rc11 x := (Rc11.judge_spec hj).1

theorem noTwo_rc {x : Exec} (h : P.Rc11 x) :
    ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False := h.whole

end Verdicts

/-! ## The check -/

open Silmaril.X86.Concurrency.Cir.Tv in
/-- **A passing check gives `C11Test.Holds`.** -/
theorem holds_of_check {c : C11Test} (h : c.check = true) : c.Holds := by
  unfold C11Test.check at h
  rw [Rc11.force_eq] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨⟨htv, hd⟩, T, hT⟩, -⟩, -⟩, ⟨⟨⟨⟨⟨⟨h6, h0⟩, h4⟩, hrc⟩, hxl⟩, htso⟩, hstr⟩⟩ := h
  -- notation
  set P := c.prog with hP
  set t := c.tv.test with ht
  set TT := P.traces c.dom with hTT
  have hS : c.flags = progFlags P t TT := rfl
  rw [hS] at h6 h0 h4 hrc hxl htso hstr
  obtain ⟨hcells, hjudge, hbit⟩ := flags_bit h6
  -- the RC11, XL and TSO flags
  have hRc : (progFlags P t TT).testBit 2 = true ↔ Verdict.allowed.Holds t (AxReach t TT P.Rc11) :=
    bit_allowed h6 (by decide) (fun trs x rc racy _ hj => by
      rw [(flagsOf_bit _ _ _ _ _).2.2.1, Bool.and_eq_true, judge_rc' hj])
      (fun x x' hag hx => (rc11_agrees hag).1.mp hx) (fun x hx => noTwo_rc hx)
  have hXl : (progFlags P t TT).testBit 3 = true ↔ Verdict.allowed.Holds t (AxReach t TT Exec.Xl) :=
    bit_allowed h6 (by decide) (fun trs x rc racy _ hj => by
      rw [(flagsOf_bit _ _ _ _ _).2.2.2.1, Bool.and_eq_true, xlB_iff])
      (fun x x' hag hx => (hag.models).2.2.1.mp hx)
      (fun x hx => Silmaril.X86.MemoryModel.Litmus.noTwo_of_xl hx)
  have hracy : (progFlags P t TT).testBit 1 = true ↔ ∃ f, AxReach t TT P.Rc11Racy f := by
    rw [hbit 1 (by decide)]
    constructor
    · rintro ⟨trs, x, he, rc, racy, hj, hb⟩
      rw [(flagsOf_bit _ _ _ _ _).2.1, judge_racy hj] at hb
      exact ⟨_, enum_reach he hb⟩
    · rintro ⟨f, hf⟩
      obtain ⟨trs, x, x', he, hag, hM, rfl⟩ := reach_enum hcells (fun x hx => noTwo_rc hx.1) hf
      obtain ⟨rc, racy, hj⟩ := hjudge trs x' he
      exact ⟨trs, x', he, rc, racy, hj, by
        rw [(flagsOf_bit _ _ _ _ _).2.1, judge_racy hj]; exact (rc11_agrees hag).2.mp hM⟩
  -- execution-level inclusion
  have hincl : ∀ x, c.IsCand x → x.Xl → P.Rc11 x := by
    rintro x ⟨trs, htrs, hevs, hrmw, hwf, hro⟩ hx
    obtain ⟨x', he, hag, -⟩ := enum_of_cand hcells htrs hevs hrmw hwf hro
      (Silmaril.X86.MemoryModel.Litmus.noTwo_of_xl hx)
    obtain ⟨rc, racy, hj⟩ := hjudge _ x' he
    have hx' : x'.Xl := (hag.models).2.2.1.mp hx
    have hb : (progFlags P t TT).testBit 0 = false := h0
    cases hrcb : rc
    · exfalso
      have : (progFlags P t TT).testBit 0 = true := (hbit 0 (by decide)).mpr ⟨_, x', he, rc, racy,
        hj, by rw [(flagsOf_bit _ _ _ _ _).1, hrcb, xlB_iff.mpr hx']; rfl⟩
      rw [hb] at this; cases this
    · exact (rc11_agrees hag).1.mpr ((judge_rc' hj).mp hrcb)
  have hsub : ∀ f, c.Xl f → c.Rc f := by
    rintro f ⟨trs, htrs, x, hevs, hrmw, hwf, hro, hx, rfl⟩
    exact ⟨trs, htrs, x, hevs, hrmw, hwf, hro, hincl x ⟨trs, htrs, hevs, hrmw, hwf, hro⟩ hx, rfl⟩
  have hnoRace : (progFlags P t TT).testBit 1 = false → ¬ ∃ f, c.RcRacy f := by
    intro h1 hr
    have := hracy.mpr hr
    rw [h1] at this; cases this
  refine ⟨⟨T, hT, fun M f hf => TvTest.refines htv hd hT hf⟩, hincl, hsub, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the RC11 verdict
    rw [← hrc]
    unfold rcVerdict
    split
    · exact hracy.mp (by assumption)
    · rename_i h1
      split
      · exact ⟨hnoRace (by simpa using h1), hRc.mp (by assumption)⟩
      · rename_i h2
        exact ⟨hnoRace (by simpa using h1), fun ha => h2 (hRc.mpr ha)⟩
  · -- some RC11 execution
    obtain ⟨trs, x, he, rc, racy, hj, hb⟩ := (hbit 4 (by decide)).mp h4
    rw [(flagsOf_bit _ _ _ _ _).2.2.2.2.1, judge_rc' hj] at hb
    exact ⟨_, enum_reach he hb⟩
  · -- the CIR's XL verdict
    rw [← hxl]
    exact verdict_of_bit h6 (by decide) (fun trs x rc racy _ hj => by
      rw [(flagsOf_bit _ _ _ _ _).2.2.2.1, Bool.and_eq_true, xlB_iff])
      (fun x x' hag hx => (hag.models).2.2.1.mp hx)
      (fun x hx => Silmaril.X86.MemoryModel.Litmus.noTwo_of_xl hx)
  · -- the CIR's TSO verdict
    intro v hv
    rw [← htso] at hv
    cases hv
    exact verdict_of_bit h6 (by decide) (fun trs x rc racy _ hj => by
      rw [(flagsOf_bit _ _ _ _ _).2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq])
      (fun x x' hag hx => (hag.models).2.1.mp hx)
      (fun x hx => Silmaril.X86.MemoryModel.Litmus.noTwo_of_tso hx)
  · -- transfer to the bytes
    intro hf
    refine ⟨T, hT, TvTest.forbidden_transfer htv hd hT ?_⟩
    rw [hf] at hrc
    unfold rcVerdict at hrc
    split at hrc
    · cases hrc
    · split at hrc
      · cases hrc
      · rename_i h2
        intro ⟨f, hfx, hw⟩
        exact h2 (hRc.mpr ⟨f, hsub f hfx, hw⟩)
  · -- `stronger`
    rw [hstr, Bool.and_eq_true, Bool.not_eq_true', hRc]
    constructor
    · rintro ⟨h2, h3⟩
      exact ⟨h2, fun ha => by rw [hXl.mpr ha] at h3; cases h3⟩
    · rintro ⟨h2, h3⟩
      refine ⟨h2, ?_⟩
      cases hb : (progFlags P t TT).testBit 3
      · rfl
      · exact absurd (hXl.mp hb) h3

end Silmaril.Proofs.X86.Concurrency.Cir.C11
