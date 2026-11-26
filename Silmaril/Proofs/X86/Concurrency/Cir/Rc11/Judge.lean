module

public import Silmaril.X86.Concurrency.Cir.Rc11.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Rc11.Masks

/-!
# RC11 on CIR: the decision procedure is correct

`judge_spec`: if `Rc11.judge ro x = some (c, r)` then `c` decides
RC11 consistency (`Rc11.Consistent ro x`) and `r` decides raciness (`Rc11.Racy ro x`). The proof
goes stage by stage (`judgeE`, `judgeD`, `judgeC`, `judgeB`, `judge`): each mask the procedure
builds is shown to mean the relation of the definition (`G n T a b ↔ ...`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc11

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Rc11 (force forceL forceRf forceCo forceLL rel seqR anyLt allLt
  tcN ofMask judge judgeB judgeC judgeD judgeE decode code roleCode roleOf rfTab coTab rfF coF frF
  locF poF extF C R W both po rf mo fr rmw loc RfRmwStar Rs Sw Hb Eco Scb PscBase PscF Psc
  Consistent Racy)
open Silmaril.X86.MemoryModel.Axiomatic (Exec BRel Ev before)

/-! ## Generic facts -/

theorem tg_congr {α : Type} {r s : α → α → Prop} (h : ∀ a b, r a b ↔ s a b) {a b : α} :
    Relation.TransGen r a b ↔ Relation.TransGen s a b := by
  have : r = s := funext fun a => funext fun b => propext (h a b)
  subst this; exact Iff.rfl

theorem G_rel {n : Nat} (f : Nat → Nat → Bool) (a b : Fin n) :
    G n (rel n f) a b ↔ f a.val b.val = true := by
  unfold G; rw [get_rel f a.isLt b.isLt]

theorem G_or {n T U : Nat} (a b : Fin n) : G n (T ||| U) a b ↔ G n T a b ∨ G n U a b := by
  unfold G; rw [get_or, Bool.or_eq_true]

theorem G_and {n T U : Nat} (a b : Fin n) : G n (T &&& U) a b ↔ G n T a b ∧ G n U a b := by
  unfold G; rw [get_and, Bool.and_eq_true]

theorem G_seqR {n T U : Nat} (a b : Fin n) :
    G n (seqR n T U) a b ↔ ∃ c : Fin n, G n T a c ∧ G n U c b := by
  unfold G; rw [get_seqR a.isLt b.isLt]
  constructor
  · rintro ⟨c, hc, h⟩; exact ⟨⟨c, hc⟩, h⟩
  · rintro ⟨c, h⟩; exact ⟨c.val, c.isLt, h⟩

theorem allLt2_iff {n : Nat} {p : Nat → Nat → Bool} :
    (allLt n fun a => allLt n fun b => p a b) = true ↔ ∀ a b : Fin n, p a.val b.val = true := by
  rw [allLt_iff]
  constructor
  · intro h a b; exact allLt_iff.mp (h a.val a.isLt) b.val b.isLt
  · intro h a ha; exact allLt_iff.mpr fun b hb => h ⟨a, ha⟩ ⟨b, hb⟩

theorem anyLt2_iff {n : Nat} {p : Nat → Nat → Bool} :
    (anyLt n fun a => anyLt n fun b => p a b) = true ↔ ∃ a b : Fin n, p a.val b.val = true := by
  rw [anyLt_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨b, hb, h⟩ := anyLt_iff.mp h
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩
  · rintro ⟨a, b, h⟩; exact ⟨a.val, a.isLt, anyLt_iff.mpr ⟨b.val, b.isLt, h⟩⟩

theorem brel_seq_iff {n : Nat} {r s : BRel n} {a b : Fin n} :
    r.seq s a b = true ↔ ∃ c, r a c = true ∧ s c b = true := by
  simp [BRel.seq, List.any_eq_true, List.mem_finRange]

theorem acyclic_mask_iff {n T : Nat} {P : Fin n → Fin n → Prop} (h : ∀ a b, G n T a b ↔ P a b) :
    (ofMask n T).acyclicB = true ↔ ∀ a, ¬ Relation.TransGen P a a := by
  rw [← Silmaril.X86.MemoryModel.Axiomatic.BRel.acyclic_iff]
  unfold BRel.Acyclic
  have : (ofMask n T).Holds = P := funext fun a => funext fun b => propext (h a b)
  rw [this]

theorem decode_code (c r : Bool) : force (code c r) decode = some (c, r) := by
  rw [force_eq]; cases c <;> cases r <;> rfl

theorem fin_ne_iff {n : Nat} (a b : Fin n) : (a.val != b.val) = true ↔ a ≠ b := by
  simp [Fin.ext_iff]

theorem fin_beq_iff {n : Nat} (a b : Fin n) : (a.val == b.val) = true ↔ a = b := by
  simp [Fin.ext_iff]

section
variable {ro : Nat → Role} {x : Exec}

/-! ## The last stage -/

theorem judgeE_spec {C' : Nat → Role} {isW : Nat → Bool}
    {poT rfT locT rfAll coAll frAll rmwAll extT hb eco psc : Nat} {c r : Bool}
    (hC : ∀ a : Fin x.n, C' a.val = ro a.val)
    (hW : ∀ a : Fin x.n, isW a.val = W ro x a)
    (hpo : ∀ a b, G x.n poT a b ↔ po x a b = true)
    (hrf : ∀ a b, G x.n rfT a b ↔ rf ro x a b = true)
    (hloc : ∀ a b, G x.n locT a b ↔ loc ro x a b = true)
    (hrfA : ∀ a b, G x.n rfAll a b ↔ x.rfR a b = true)
    (hcoA : ∀ a b, G x.n coAll a b ↔ x.coR a b = true)
    (hfrA : ∀ a b, G x.n frAll a b ↔ x.frR a b = true)
    (hrmw : ∀ a b, G x.n rmwAll a b ↔ x.rmwR a b = true)
    (hext : ∀ a b, G x.n extT a b ↔ x.ext a b = true)
    (hhb : ∀ a b, G x.n hb a b ↔ Hb ro x a b)
    (heco : ∀ a b, G x.n eco a b ↔ Eco ro x a b)
    (hpsc : ∀ a b, G x.n psc a b ↔ Psc ro x a b)
    (h : judgeE x.n C' isW poT rfT locT rfAll coAll frAll rmwAll extT hb eco psc = some (c, r)) :
    (c = true ↔ Consistent ro x) ∧ (r = true ↔ Racy ro x) := by
  unfold judgeE at h
  simp only [decode_code, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hcom : ∀ a b : Fin x.n, Rc11.get x.n (rfAll ||| coAll ||| frAll) a.val b.val = x.com a b := by
    intro a b
    apply Bool.eq_iff_iff.mpr
    have h1 : G x.n (rfAll ||| coAll ||| frAll) a b ↔ x.com a b = true := by
      rw [G_or, G_or, hrfA, hcoA, hfrA]
      simp [Exec.com, BRel.union, or_assoc]
    exact h1
  constructor
  · simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨hw, hco⟩, hat⟩, hsc⟩, hnt⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a b h1 h2
        have := allLt2_iff.mp hw a b
        rw [hcom, hcom, h1, h2] at this; simp at this
      · intro a b hab
        have := allLt2_iff.mp hco a b
        have hab' : Rc11.get x.n hb a.val b.val = true := (hhb a b).mpr hab
        rw [hab', Bool.not_true, Bool.false_or, Bool.and_eq_true, fin_ne_iff] at this
        refine ⟨this.1, fun he => ?_⟩
        have := this.2
        rw [show Rc11.get x.n eco b.val a.val = true from (heco b a).mpr he] at this
        simp at this
      · rw [Exec.atomicB, Silmaril.X86.MemoryModel.Axiomatic.BRel.emptyB_iff]
        intro a b
        have := allLt2_iff.mp hat a b
        apply Bool.eq_false_iff.mpr
        intro hc
        simp only [BRel.inter, Bool.and_eq_true] at hc
        obtain ⟨h1, h2⟩ := hc
        obtain ⟨m, hm1, hm2⟩ := brel_seq_iff.mp h2
        simp only [Exec.fre, Exec.coe, BRel.inter, Bool.and_eq_true] at hm1 hm2
        have hs : G x.n (seqR x.n (frAll &&& extT) (coAll &&& extT)) a b :=
          (G_seqR a b).mpr ⟨m, (G_and a m).mpr ⟨(hfrA a m).mpr hm1.1, (hext a m).mpr hm1.2⟩,
            (G_and m b).mpr ⟨(hcoA m b).mpr hm2.1, (hext m b).mpr hm2.2⟩⟩
        unfold G at hs
        rw [show Rc11.get x.n rmwAll a.val b.val = true from (hrmw a b).mpr h1, hs] at this
        simp at this
      · exact (acyclic_mask_iff hpsc).mp hsc
      · exact (acyclic_mask_iff fun a b => by rw [G_or, hpo, hrf]).mp hnt
    · rintro ⟨hw, hco, hat, hsc, hnt⟩
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · refine allLt2_iff.mpr fun a b => ?_
        rw [hcom, hcom]
        cases h1 : x.com a b <;> cases h2 : x.com b a <;> simp
        exact hw a b h1 h2
      · refine allLt2_iff.mpr fun a b => ?_
        by_cases h1 : G x.n hb a b
        · obtain ⟨hne, hne'⟩ := hco a b ((hhb a b).mp h1)
          unfold G at h1
          rw [h1, Bool.not_true, Bool.false_or, Bool.and_eq_true, fin_ne_iff]
          refine ⟨hne, ?_⟩
          cases h2 : Rc11.get x.n eco b.val a.val
          · rfl
          · exact absurd ((heco b a).mp h2) hne'
        · unfold G at h1
          simp [h1]
      · rw [Exec.atomicB, Silmaril.X86.MemoryModel.Axiomatic.BRel.emptyB_iff] at hat
        refine allLt2_iff.mpr fun a b => ?_
        cases h1 : Rc11.get x.n rmwAll a.val b.val
        · rfl
        · cases h2 : Rc11.get x.n (seqR x.n (frAll &&& extT) (coAll &&& extT)) a.val b.val
          · rfl
          · exfalso
            obtain ⟨m, hm1, hm2⟩ := (G_seqR a b).mp h2
            rw [G_and] at hm1 hm2
            have := hat a b
            simp only [BRel.inter, Bool.and_eq_false_iff] at this
            rcases this with h | h
            · rw [(hrmw a b).mp h1] at h; cases h
            · have ht : (x.fre.seq x.coe) a b = true := by
                refine brel_seq_iff.mpr ⟨m, ?_, ?_⟩
                · simp only [Exec.fre, BRel.inter, Bool.and_eq_true]
                  exact ⟨(hfrA a m).mp hm1.1, (hext a m).mp hm1.2⟩
                · simp only [Exec.coe, BRel.inter, Bool.and_eq_true]
                  exact ⟨(hcoA m b).mp hm2.1, (hext m b).mp hm2.2⟩
              rw [ht] at h; cases h
      · exact (acyclic_mask_iff hpsc).mpr hsc
      · exact (acyclic_mask_iff fun a b => by rw [G_or, hpo, hrf]).mpr hnt
  · rw [anyLt2_iff]
    constructor
    · rintro ⟨a, b, hab⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', fin_ne_iff] at hab
      obtain ⟨⟨⟨⟨⟨hne, hl⟩, hw⟩, hna⟩, h1⟩, h2⟩ := hab
      refine ⟨a, b, hne, (hloc a b).mp hl, ?_, ?_, ?_, ?_⟩
      · rw [← hW, ← hW]; exact hw
      · simpa only [C, ← hC] using hna
      · intro h; have := (hhb a b).mpr h; unfold G at this; rw [this] at h1; cases h1
      · intro h; have := (hhb b a).mpr h; unfold G at this; rw [this] at h2; cases h2
    · rintro ⟨a, b, hne, hl, hw, hna, h1, h2⟩
      refine ⟨a, b, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', fin_ne_iff]
      refine ⟨⟨⟨⟨⟨hne, (hloc a b).mpr hl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [hW, hW]; exact hw
      · simpa only [C, hC] using hna
      · cases h : Rc11.get x.n hb a.val b.val
        · rfl
        · exact absurd ((hhb a b).mp h) h1
      · cases h : Rc11.get x.n hb b.val a.val
        · rfl
        · exact absurd ((hhb b a).mp h) h2

/-! ## `psc` -/

theorem judgeD_spec {C' : Nat → Role} {isW : Nat → Bool}
    {poT rfT moT frT locT rfAll coAll frAll rmwAll extT eco hb : Nat} {c r : Bool}
    (hC : ∀ a : Fin x.n, C' a.val = ro a.val)
    (hW : ∀ a : Fin x.n, isW a.val = W ro x a)
    (hpo : ∀ a b, G x.n poT a b ↔ po x a b = true)
    (hrf : ∀ a b, G x.n rfT a b ↔ rf ro x a b = true)
    (hmo : ∀ a b, G x.n moT a b ↔ mo ro x a b = true)
    (hfr : ∀ a b, G x.n frT a b ↔ fr ro x a b = true)
    (hloc : ∀ a b, G x.n locT a b ↔ loc ro x a b = true)
    (hrfA : ∀ a b, G x.n rfAll a b ↔ x.rfR a b = true)
    (hcoA : ∀ a b, G x.n coAll a b ↔ x.coR a b = true)
    (hfrA : ∀ a b, G x.n frAll a b ↔ x.frR a b = true)
    (hrmw : ∀ a b, G x.n rmwAll a b ↔ x.rmwR a b = true)
    (hext : ∀ a b, G x.n extT a b ↔ x.ext a b = true)
    (hhb : ∀ a b, G x.n hb a b ↔ Hb ro x a b)
    (heco : ∀ a b, G x.n eco a b ↔ Eco ro x a b)
    (h : judgeD x.n C' isW poT rfT moT frT locT rfAll coAll frAll rmwAll extT eco hb = some (c, r)) :
    (c = true ↔ Consistent ro x) ∧ (r = true ↔ Racy ro x) := by
  unfold judgeD at h
  simp only [force_eq] at h
  have hhb' : ∀ a b : Fin x.n, Rc11.get x.n hb a.val b.val = true ↔ Hb ro x a b := hhb
  have hpo' : ∀ a b : Fin x.n, Rc11.get x.n poT a.val b.val = true ↔ po x a b = true := hpo
  have hloc' : ∀ a b : Fin x.n, Rc11.get x.n locT a.val b.val = loc ro x a b :=
    fun a b => Bool.eq_iff_iff.mpr (hloc a b)
  have hscb : ∀ a b, G x.n (poT ||| seqR x.n (seqR x.n (rel x.n fun a b =>
      Rc11.get x.n poT a b && !Rc11.get x.n locT a b) hb) (rel x.n fun a b =>
      Rc11.get x.n poT a b && !Rc11.get x.n locT a b) ||| (hb &&& locT) ||| moT ||| frT) a b ↔
      Scb ro x a b := by
    intro a b
    simp only [G_or, G_and, G_seqR, G_rel, hpo, hmo, hfr, hhb, hloc, Bool.and_eq_true,
      Bool.not_eq_true', hpo', hloc']
    unfold Scb
    constructor
    · rintro ((((h | ⟨d, ⟨c, ⟨h1, h2⟩, h3⟩, h4, h5⟩) | h) | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨c, d, h1, h2, h3, h4, h5⟩)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rintro (h | ⟨c, d, h1, h2, h3, h4, h5⟩ | h | h | h)
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨d, ⟨c, ⟨h1, h2⟩, h3⟩, h4, h5⟩)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  refine judgeE_spec hC hW hpo hrf hloc hrfA hcoA hfrA hrmw hext hhb heco ?_ h
  intro a b
  simp only [G_or, G_and, G_seqR, G_rel, hscb, Bool.and_eq_true, Bool.or_eq_true, hC,
    fin_beq_iff, hhb', hhb]
  unfold Psc PscBase PscF C
  constructor
  · rintro (⟨b', ⟨a', h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
    · exact Or.inl ⟨a', b', h1, h2, h3⟩
    · refine Or.inr ⟨h1, h2, ?_⟩
      rcases h3 with h3 | ⟨d, ⟨c, h4, h5⟩, h6⟩
      · exact Or.inl h3
      · exact Or.inr ⟨c, d, h4, (heco c d).mp h5, h6⟩
  · rintro (⟨a', b', h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨b', ⟨a', h1, h2⟩, h3⟩
    · refine Or.inr ⟨⟨h1, h2⟩, ?_⟩
      rcases h3 with h3 | ⟨c, d, h4, h5, h6⟩
      · exact Or.inl h3
      · exact Or.inr ⟨d, ⟨c, h4, (heco c d).mpr h5⟩, h6⟩

/-! ## `sw` and `hb` -/

theorem judgeC_spec {C' : Nat → Role} {isR isW : Nat → Bool}
    {poT rfT moT frT locT rfAll coAll frAll rmwAll extT rr eco : Nat} {c r : Bool}
    (hC : ∀ a : Fin x.n, C' a.val = ro a.val)
    (hR : ∀ a : Fin x.n, isR a.val = R ro x a)
    (hW : ∀ a : Fin x.n, isW a.val = W ro x a)
    (hpo : ∀ a b, G x.n poT a b ↔ po x a b = true)
    (hrf : ∀ a b, G x.n rfT a b ↔ rf ro x a b = true)
    (hmo : ∀ a b, G x.n moT a b ↔ mo ro x a b = true)
    (hfr : ∀ a b, G x.n frT a b ↔ fr ro x a b = true)
    (hloc : ∀ a b, G x.n locT a b ↔ loc ro x a b = true)
    (hrfA : ∀ a b, G x.n rfAll a b ↔ x.rfR a b = true)
    (hcoA : ∀ a b, G x.n coAll a b ↔ x.coR a b = true)
    (hfrA : ∀ a b, G x.n frAll a b ↔ x.frR a b = true)
    (hrmw : ∀ a b, G x.n rmwAll a b ↔ x.rmwR a b = true)
    (hext : ∀ a b, G x.n extT a b ↔ x.ext a b = true)
    (hrr : ∀ a b, G x.n rr a b ↔ Relation.TransGen ((rf ro x).seq (rmw ro x)).Holds a b)
    (heco : ∀ a b, G x.n eco a b ↔ Eco ro x a b)
    (h : judgeC x.n C' isR isW poT rfT moT frT locT rfAll coAll frAll rmwAll extT rr eco =
      some (c, r)) :
    (c = true ↔ Consistent ro x) ∧ (r = true ↔ Racy ro x) := by
  unfold judgeC at h
  simp only [force_eq] at h
  have hpo' : ∀ a b : Fin x.n, Rc11.get x.n poT a.val b.val = true ↔ po x a b = true := hpo
  have hloc' : ∀ a b : Fin x.n, Rc11.get x.n locT a.val b.val = true ↔ loc ro x a b = true := hloc
  have hrf' : ∀ a b : Fin x.n, Rc11.get x.n rfT a.val b.val = true ↔ rf ro x a b = true := hrf
  -- the release sequence
  have hrs : ∀ a b, G x.n ((rel x.n fun a c => isW a && (c == a || (Rc11.get x.n poT a c &&
      Rc11.get x.n locT a c)) && isW c && (C' c).rlx) ||| seqR x.n (rel x.n fun a c => isW a &&
      (c == a || (Rc11.get x.n poT a c && Rc11.get x.n locT a c)) && isW c && (C' c).rlx) rr) a b ↔
      Rs ro x a b := by
    intro a b
    simp only [G_or, G_seqR, G_rel, Bool.and_eq_true, Bool.or_eq_true, hW, hC, fin_beq_iff,
      hpo', hloc', hrr]
    unfold Rs RfRmwStar C
    simp only [Relation.reflTransGen_iff_eq_or_transGen]
    constructor
    · rintro (⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨c, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩)
      · exact ⟨h1, b, h2, h3, h4, Or.inl rfl⟩
      · exact ⟨h1, c, h2, h3, h4, Or.inr h5⟩
    · rintro ⟨h1, c, h2, h3, h4, rfl | h5⟩
      · exact Or.inl ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      · exact Or.inr ⟨c, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  -- synchronises-with
  have hsw : ∀ a b, G x.n (rel x.n fun a b => (C' a).rel && (C' b).acq && Rc11.get x.n
      (seqR x.n (seqR x.n (seqR x.n (rel x.n fun a a' => a' == a || ((C' a).isF &&
        Rc11.get x.n poT a a'))
        ((rel x.n fun a c => isW a && (c == a || (Rc11.get x.n poT a c && Rc11.get x.n locT a c)) &&
          isW c && (C' c).rlx) ||| seqR x.n (rel x.n fun a c => isW a && (c == a ||
          (Rc11.get x.n poT a c && Rc11.get x.n locT a c)) && isW c && (C' c).rlx) rr))
        (rel x.n fun w r => Rc11.get x.n rfT w r && isR r && (C' r).rlx))
        (rel x.n fun r b => b == r || (Rc11.get x.n poT r b && (C' b).isF))) a b) a b ↔
      Sw ro x a b := by
    intro a b
    rw [G_rel]
    simp only [Bool.and_eq_true]
    rw [show Rc11.get x.n _ a.val b.val = true ↔ _ from G_seqR a b]
    simp only [G_seqR, G_rel, Bool.and_eq_true, Bool.or_eq_true, hC, hR, fin_beq_iff, hpo',
      hrf']
    unfold Sw C
    constructor
    · rintro ⟨⟨h1, h2⟩, r', ⟨w, ⟨a', h3, h4⟩, ⟨h5, h6⟩, h7⟩, h8⟩
      exact ⟨h1, a', w, r', h3, (hrs a' w).mp h4, h5, h6, h7, h8, h2⟩
    · rintro ⟨h1, a', w, r', h3, h4, h5, h6, h7, h8, h2⟩
      exact ⟨⟨h1, h2⟩, r', ⟨w, ⟨a', h3, (hrs a' w).mpr h4⟩, ⟨h5, h6⟩, h7⟩, h8⟩
  split at h
  · rename_i hb hhbN
    refine judgeD_spec hC hW hpo hrf hmo hfr hloc hrfA hcoA hfrA hrmw hext ?_ heco h
    intro a b
    rw [tcN_spec hhbN a b]
    unfold Hb
    exact tg_congr fun a b => by rw [G_or, hpo, hsw]
  · cases h

/-! ## `(rf ; rmw)⁺` and `eco` -/

theorem judgeB_spec {C' : Nat → Role} {isR isW : Nat → Bool}
    {poT rfAll coAll frAll locAll rmwAll extT accT : Nat} {c r : Bool}
    (hC : ∀ a : Fin x.n, C' a.val = ro a.val)
    (hR : ∀ a : Fin x.n, isR a.val = R ro x a)
    (hW : ∀ a : Fin x.n, isW a.val = W ro x a)
    (hpo : ∀ a b, G x.n poT a b ↔ po x a b = true)
    (hrfA : ∀ a b, G x.n rfAll a b ↔ x.rfR a b = true)
    (hcoA : ∀ a b, G x.n coAll a b ↔ x.coR a b = true)
    (hfrA : ∀ a b, G x.n frAll a b ↔ x.frR a b = true)
    (hlocA : ∀ a b, G x.n locAll a b ↔ x.loc a b = true)
    (hrmw : ∀ a b, G x.n rmwAll a b ↔ x.rmwR a b = true)
    (hext : ∀ a b, G x.n extT a b ↔ x.ext a b = true)
    (hacc : ∀ a b, G x.n accT a b ↔ both ro x a b = true)
    (h : judgeB x.n C' isR isW poT rfAll coAll frAll locAll rmwAll extT accT = some (c, r)) :
    (c = true ↔ Consistent ro x) ∧ (r = true ↔ Racy ro x) := by
  unfold judgeB at h
  simp only at h
  have hrf : ∀ a b, G x.n (rfAll &&& accT) a b ↔ rf ro x a b = true := by
    intro a b; rw [G_and, hrfA, hacc]; simp [rf]
  have hmo : ∀ a b, G x.n (coAll &&& accT) a b ↔ mo ro x a b = true := by
    intro a b; rw [G_and, hcoA, hacc]; simp [mo]
  have hfr : ∀ a b, G x.n (frAll &&& accT) a b ↔ fr ro x a b = true := by
    intro a b; rw [G_and, hfrA, hacc]; simp [fr]
  have hloc : ∀ a b, G x.n (locAll &&& accT) a b ↔ loc ro x a b = true := by
    intro a b; rw [G_and, hlocA, hacc]; simp [loc]
  have hrm : ∀ a b, G x.n (rmwAll &&& accT) a b ↔ rmw ro x a b = true := by
    intro a b; rw [G_and, hrmw, hacc]; simp [rmw]
  split at h
  · rename_i rr eco hrrN hecoN
    refine judgeC_spec hC hR hW hpo hrf hmo hfr hloc hrfA hcoA hfrA hrmw hext ?_ ?_ h
    · intro a b
      rw [tcN_spec hrrN a b]
      exact tg_congr fun a b => by
        rw [G_seqR]
        show _ ↔ ((rf ro x).seq (rmw ro x)) a b = true
        rw [brel_seq_iff]
        simp only [hrf, hrm]
    · intro a b
      rw [tcN_spec hecoN a b]
      unfold Eco
      exact tg_congr fun a b => by
        rw [G_or, G_or, hrf, hmo, hfr]
        show _ ↔ ((rf ro x).union ((mo ro x).union (fr ro x))) a b = true
        simp [BRel.union, or_assoc]
  · cases h

/-! ## The base relations -/

theorem getD_range_map {α : Type} {n i : Nat} (f : Nat → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem evN_eq (a : Fin x.n) : x.evN a.val = x.ev a := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD]

theorem rfF_eq (a b : Fin x.n) : rfF x (rfTab x) a.val b.val = x.rfR a b := by
  unfold rfF rfTab Exec.rfR
  rw [getD_range_map _ _ b.isLt, List.any_map, evN_eq, evN_eq]
  rfl

theorem coF_eq (a b : Fin x.n) : coF x (coTab x) a.val b.val = x.coR a b := by
  unfold coF coTab Exec.coR
  rw [getD_range_map _ _ a.isLt, List.any_map, evN_eq, evN_eq]
  rfl

theorem frF_eq (a b : Fin x.n) : frF x (rfTab x) (coTab x) a.val b.val = x.frR a b := by
  unfold frF rfTab coTab Exec.frR
  rw [getD_range_map _ _ a.isLt, getD_range_map _ _ a.isLt, List.zip_map', List.any_map,
    evN_eq, evN_eq]
  rfl

theorem locF_eq (a b : Fin x.n) : locF x a.val b.val = x.loc a b := by
  unfold locF Exec.loc; rw [evN_eq, evN_eq]

theorem poF_eq (a b : Fin x.n) : poF x a.val b.val = x.po a b := by
  unfold poF Exec.po; rw [evN_eq, evN_eq]

theorem extF_eq (a b : Fin x.n) : extF x a.val b.val = x.ext a b := by
  unfold extF Exec.ext; rw [evN_eq, evN_eq]

theorem roleOf_roleCode (r : Role) : roleOf (roleCode r) = r := by
  rcases r with ⟨m⟩ | _ | _
  · cases m <;> rfl
  · rfl
  · rfl

/-- **The RC11 decision procedure is correct.** -/
theorem judge_spec {c r : Bool} (h : judge ro x = some (c, r)) :
    (c = true ↔ Consistent ro x) ∧ (r = true ↔ Racy ro x) := by
  unfold judge at h
  simp only [force_eq, forceL_eq, forceLL_eq forceRf_eq, forceLL_eq forceCo_eq] at h
  have hC : ∀ a : Fin x.n, roleOf (((List.range x.n).map fun i => roleCode (ro i)).getD a.val 0) =
      ro a.val := fun a => by rw [getD_range_map _ _ a.isLt, roleOf_roleCode]
  refine judgeB_spec hC (fun a => ?_) (fun a => ?_) (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_) (fun a b => ?_) (fun a b => ?_) (fun a b => ?_) (fun a b => ?_) h
  · rw [hC, evN_eq]; rfl
  · rw [hC, evN_eq]; rfl
  · rw [G_rel, poF_eq]; rfl
  · rw [G_rel, rfF_eq]
  · rw [G_rel, coF_eq]
  · rw [G_rel, frF_eq]
  · rw [G_rel, locF_eq]
  · rw [G_rel]; rfl
  · rw [G_rel, extF_eq]
  · rw [G_rel, hC, hC]; rfl

end

end Silmaril.Proofs.X86.Concurrency.Cir.Rc11
