module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Drf

/-!
# CSL over CIR: the owned-data-plus-shared-counter example

A non-vacuity check of the logic and the DRF theorem: the example's
CSL certificate is proved, so its finished, drained TSO/XL states hold each thread's value.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy RmwOp)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Ex
open Silmaril.Proofs.X86.Concurrency.Cir.Csl

theorem lit_toNat (rs : Regs) {n : Nat} (h : n < 2 ^ 64) : ((Expr.lit n).eval rs).toNat = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := rfl

/-- The `lock xadd` on the counter, from owning `8t ↦ t+1`. -/
theorem safe_fadd (t : Nat) (ht : t < 2) (rs : Regs) :
    Safe inv (post t) (.rmw .rax .sc 8 .fadd (.lit ctr) (.lit 1)) rs
      (Heap.single (8 * t) (t + 1)) := by
  refine safe_atomic (fun e => nomatch e) (fun _ _ st => nomatch st) fun l s' rs' st => ?_
  cases st with
  | @rmw d m sz op a arg rs0 old hv =>
    rw [lit_toNat rs (by decide : ctr < 2 ^ 64)]
    refine ⟨rfl, rfl, fun e => by simp [Lab.na] at e, fun _ hI ⟨v, hIv⟩ _ => ?_⟩
    subst hIv
    refine ⟨fun a ta => ?_, fun e => by simp [Lab.drains] at e, fun ok => ?_⟩
    · rcases ta with ⟨w, hw⟩ | hw
      · simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hw
        rw [hw.1, union_isSome]; simp [single_apply]
      · simp only [Lab.wval] at hw
        by_cases e : ctr = a
        · subst e; rw [union_isSome]; simp [single_apply]
        · simp [e] at hw
    · refine ⟨Heap.single (8 * t) (t + 1),
        Heap.single ctr (RmwOp.result rs 8 old ((Expr.lit 1).eval rs) .fadd), fun a => ?_, ?_,
        ⟨_, rfl⟩, rfl, fun e => by simp [Lab.drains] at e⟩
      · simp only [single_apply]
        by_cases e : a = ctr
        · left; simp [ctr] at e ⊢; omega
        · right; simp [e]
      · funext a
        simp only [union_apply, updH_apply, single_apply, Lab.wval]
        by_cases e : a = ctr
        · subst e
          have : 8 * t ≠ ctr := by simp [ctr]; omega
          simp [Ne.symm this]
        · have : ¬ ctr = a := Ne.symm e
          simp [this, e]

/-- **Thread `t` is safe** from owning `8t ↦ 0`. -/
theorem safe_body (t : Nat) (ht : t < 2) (rs : Regs) :
    Safe inv (post t) (body t) rs (Heap.single (8 * t) 0) := by
  have h8 : 8 * t < 2 ^ 64 := by omega
  have h1 : t + 1 < 2 ^ 64 := by omega
  refine safe_seq (safe_store_na ?_ ?_)
  · rw [lit_toNat rs h8]; simp [single_apply]
  · rw [lit_toNat rs h8, lit_toNat rs h1]
    have hv : (t + 1) % 2 ^ (8 * 8) = t + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hv]
    have : (Lab.wr .na .wb (8 * t) 8 (t + 1) : Lab).updH (Heap.single (8 * t) 0) =
        Heap.single (8 * t) (t + 1) := by
      funext a
      simp only [updH_apply, Lab.wval, single_apply]
      by_cases e : a = 8 * t
      · subst e; simp
      · simp [e, Ne.symm e]
    rw [this]; exact safe_fadd t ht rs

/-- **The example's CSL certificate.** -/
theorem ginv_start : GInv inv post 2 start own (Heap.single ctr 0) := by
  refine ⟨fun t u htu a => ?_, fun t a => ?_, fun t a v e => ?_, fun a v e => ?_, ⟨0, rfl⟩,
    fun t ht => ?_⟩
  · unfold own
    by_cases h1 : t < 2
    · by_cases h2 : u < 2
      · simp only [h1, h2, ite_true, single_apply]
        by_cases e : a = 8 * t
        · right; have : ¬ a = 8 * u := by omega
          simp [this]
        · left; simp [e]
      · simp only [h2, ite_false]; exact Or.inr rfl
    · simp only [h1, ite_false]; exact Or.inl rfl
  · unfold own
    by_cases h1 : t < 2
    · simp only [h1, ite_true, single_apply]
      by_cases e : a = 8 * t
      · right; have : ¬ a = ctr := by simp [ctr]; omega
        simp [this]
      · left; simp [e]
    · simp only [h1, ite_false]; exact Or.inl rfl
  · unfold own at e
    by_cases h1 : t < 2
    · simp only [h1, ite_true, single_apply] at e
      by_cases ea : a = 8 * t
      · simp only [ea, ite_true, Option.some.injEq] at e
        subst e
        have : 8 * t = 0 ∨ 8 * t = 8 := by omega
        simp only [start, ea]; rcases this with h | h <;> simp [h]
      · simp [ea] at e
    · simp only [h1, ite_false] at e; cases e
  · simp only [single_apply] at e
    by_cases ea : a = ctr
    · simp only [ea, ite_true, Option.some.injEq] at e
      subst e; simp [start, ea]
    · simp [ea] at e
  · simp only [start, own, ht, ite_true]; exact safe_body t ht _

/-- **Ownership ⇒ DRF ⇒ SC on the example**: every finished, drained configuration the XL (or
TSO) store-buffer machine reaches holds `1` in cell `0` and `2` in cell `8`. -/
theorem ex_buffered {M : OModel} {C : OCfg} (h : OReach M 2 start.toO C) (hd : C.Drained)
    (hfin : ∀ t < 2, (C.ts t).1 = .skip) : C.mem 0 = some 1 ∧ C.mem 8 = some 2 := by
  have r := (drf_reach ginv_start h).1
  rw [abs_drained hd] at r
  obtain ⟨hs', hI', G'⟩ := ginv_reach r ginv_start
  obtain ⟨q, -, -, -, l1, -⟩ := ginv_done G' hfin
  have e0 := q 0 (by decide); have e1 := q 1 (by decide)
  simp only [post] at e0 e1
  refine ⟨l1 0 0 1 ?_, l1 1 8 2 ?_⟩
  · rw [e0]; rfl
  · rw [e1]; rfl

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Ex

/-- **The buffered machines are weak**: TSO (hence XL) reaches the drained, finished `SB`
state where both loads returned `0`. -/
theorem sb_weak : ∃ C : OCfg, OReach .tso 2 sbStart.toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ (C.ts 0).2 .rbx = 0 ∧ (C.ts 1).2 .rbx = 0 ∧
    C.mem 0 = some 1 ∧ C.mem 8 = some 1 := by
  refine ⟨_, Star.step (OStep.buffered (t := 0) (by decide) (TStep.seq TStep.store) rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 0) (by decide) TStep.seqSkip)
    (Star.step (OStep.buffered (t := 1) (by decide) (TStep.seq TStep.store) rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.buffered (t := 0) (by decide) (TStep.load (v := 0) (by decide)) rfl rfl ?_ ?_)
    (Star.step (OStep.buffered (t := 1) (by decide) (TStep.load (v := 0) (by decide)) rfl rfl ?_ ?_)
    (Star.step (OStep.flush (t := 0) (pre := []) (e := .st 0 1 false) (post := [])
      (by decide) ?_ ?_ (Or.inr rfl))
    (Star.step (OStep.flush (t := 1) (pre := []) (e := .st 8 1 false) (post := [])
      (by decide) ?_ ?_ (Or.inr rfl))
    Star.refl))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | (intro a ta; rw [Silmaril.Proofs.X86.Concurrency.Cir.Csl.touches_wr.mp ta]; decide +kernel)
    | (intro a ta; rw [Silmaril.Proofs.X86.Concurrency.Cir.Csl.touches_rd.mp ta]; decide +kernel)
    | (intro p hp; simp only [Lab.reads, List.mem_singleton] at hp; subst hp; decide +kernel)
    | (intro p hp; simp [Lab.reads] at hp)
    | (intro t ht; have : t = 0 ∨ t = 1 := by omega
       rcases this with rfl | rfl <;> rfl)
    | (intro t
       by_cases h0 : t = 0
       · subst h0; rfl
       · by_cases h1 : t = 1
         · subst h1; rfl
         · simp [upd, h0, h1, Cfg.toO])

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex.Sb

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Ex


/-- A thread's store. -/
abbrev stA (a : Nat) : Stmt := .store .rlx 8 .wb (.lit a) (.lit 1)
/-- A thread's load. -/
abbrev ldB (b : Nat) : Stmt := .load .rbx .rlx 8 .wb (.lit b)

/-- The registers after loading `v`. -/
def Rv (v : Nat) : Regs := Regs.zero.set .rbx (BitVec.ofNat 64 v)

/-- Thread progress: before its store, before its load, done having read `v`. -/
def Stage (a b : Nat) (p : Stmt × Regs) (mem : Heap) : Prop :=
  (p = (.seq (stA a) (ldB b), Regs.zero) ∧ mem a = some 0) ∨
  ((p = (.seq .skip (ldB b), Regs.zero) ∨ p = (ldB b, Regs.zero)) ∧ mem a = some 1) ∨
  (∃ v, v ≤ 1 ∧ p = (.skip, Rv v) ∧ mem a = some 1)

/-- **The SC invariant of `SB`**: a finished thread that read `0` saw the other thread before
its store, so the other thread reads `1`. -/
def Inv (C : Cfg) : Prop :=
  Stage 0 8 (C.ts 0) C.mem ∧ Stage 8 0 (C.ts 1) C.mem ∧
  ((C.ts 0).1 = .skip → (C.ts 1).1 = .skip → (C.ts 0).2 .rbx = 1 ∨ (C.ts 1).2 .rbx = 1)

theorem stage_mem {a b p mem} (h : Stage a b p mem) : mem a = some 0 ∨ mem a = some 1 := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, -, h⟩ <;> simp [h]

theorem stage_done {a b p mem} (h : Stage a b p mem) {v} (e : p = (.skip, Rv v)) :
    mem a = some 1 := by
  rcases h with ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨-, -, -, h⟩ <;> first | exact h | (rw [e] at h; cases h)

theorem l1 (rs : Regs) : ((Expr.lit 1).eval rs).toNat % 2 ^ (8 * 8) = 1 := rfl
theorem la (rs : Regs) {a : Nat} (h : a < 2 ^ 64) : ((Expr.lit a).eval rs).toNat = a := by
  show (BitVec.ofNat 64 a).toNat = a
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- One thread's step: silent, or a label `l` with its effect. -/
theorem stage_tau {a b p mem s' rs'} (h : Stage a b p mem) (hs : TStep p.1 p.2 none s' rs') :
    Stage a b (s', rs') mem ∧ s' ≠ .skip := by
  rcases h with ⟨e, hm⟩ | ⟨e | e, hm⟩ | ⟨v, -, e, -⟩ <;> rw [e] at hs
  · cases hs with | seq h => cases h
  · cases hs with
    | seq h => cases h
    | seqSkip => exact ⟨Or.inr (Or.inl ⟨Or.inr rfl, hm⟩), fun h => nomatch h⟩
  · cases hs
  · cases hs

theorem stage_congr {a b p mem mem'} (e : mem' a = mem a) (h : Stage a b p mem) :
    Stage a b p mem' := by
  rcases h with ⟨h, hm⟩ | ⟨h, hm⟩ | ⟨v, hv, h, hm⟩
  · exact Or.inl ⟨h, e ▸ hm⟩
  · exact Or.inr (Or.inl ⟨h, e ▸ hm⟩)
  · exact Or.inr (Or.inr ⟨v, hv, h, e ▸ hm⟩)

theorem stage_lab {a b p mem l s' rs'} (hab : a ≠ b) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : Stage a b p mem) (hs : TStep p.1 p.2 (some l) s' rs') (hok : l.okH mem)
    (hbv : mem b = some 0 ∨ mem b = some 1) :
    l.updH mem b = mem b ∧ Stage a b (s', rs') (l.updH mem) ∧
      (s' ≠ .skip ∨ ∃ v, rs' = Rv v ∧ mem b = some v) := by
  rcases h with ⟨e, hm⟩ | ⟨e | e, hm⟩ | ⟨v, -, e, -⟩ <;> rw [e] at hs
  · cases hs with
    | seq h =>
      cases h
      simp only [la _ ha, l1]
      refine ⟨?_, Or.inr (Or.inl ⟨Or.inl rfl, ?_⟩), Or.inl fun h => nomatch h⟩
      · simp [Lab.updH, Lab.wval, hab]
      · simp [Lab.updH, Lab.wval]
  · cases hs with | seq h => cases h
  · cases hs with
    | @load _ _ _ _ _ _ v hv =>
      simp only [la _ hb] at hok ⊢
      have hmb := hok (b, v) (by simp [Lab.reads])
      have hu : (Lab.rd .rlx .wb b 8 v).updH mem = mem := rfl
      rw [hu]
      refine ⟨rfl, Or.inr (Or.inr ⟨v, ?_, rfl, hm⟩), Or.inr ⟨v, rfl, hmb⟩⟩
      rcases hbv with e | e <;> rw [e] at hmb <;> cases hmb <;> decide
  · cases hs

theorem done_stage {a b p mem} (h : Stage a b p mem) (e : p.1 = .skip) :
    mem a = some 1 := by
  rcases h with ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨-, -, -, h⟩ <;> first | exact h | (rw [h] at e; cases e)

theorem step_inv {C C' : Cfg} (hI : Inv C) (h : ScStep 2 C C') : Inv C' := by
  obtain ⟨h0, h1, hf⟩ := hI
  cases h with
  | @tau t s' rs' ht hs =>
    obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · obtain ⟨st, hn⟩ := stage_tau h0 hs
      exact ⟨st, h1, fun e _ => absurd e hn⟩
    · obtain ⟨st, hn⟩ := stage_tau h1 hs
      exact ⟨h0, st, fun _ e => absurd e hn⟩
  | @lab t l s' rs' ht hs hm hc hok =>
    obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · obtain ⟨hu, st, hd⟩ := stage_lab (by decide) (by decide) (by decide) h0 hs hok
        (stage_mem h1)
      refine ⟨st, stage_congr hu h1, fun e0 e1 => ?_⟩
      rcases hd with hn | ⟨v, rfl, hv⟩
      · exact absurd e0 hn
      · rw [done_stage h1 e1] at hv; cases hv; exact Or.inl rfl
    · obtain ⟨hu, st, hd⟩ := stage_lab (by decide) (by decide) (by decide) h1 hs hok
        (stage_mem h0)
      refine ⟨stage_congr hu h0, st, fun e0 e1 => ?_⟩
      rcases hd with hn | ⟨v, rfl, hv⟩
      · exact absurd e1 hn
      · rw [done_stage h0 e0] at hv; cases hv; exact Or.inr rfl

theorem reach_inv {C C' : Cfg} (h : ScReach 2 C C') (hI : Inv C) : Inv C' := by
  induction h with
  | refl => exact hI
  | step s _ ih => exact ih (step_inv hI s)

theorem init_inv : Inv sbStart := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, fun e _ => nomatch e⟩

/-- **`SB`'s both-zero outcome is not SC**: the CIR-native SC machine never reaches it. -/
theorem sb_sc : ¬ ∃ C : Cfg, ScReach 2 sbStart C ∧ C.Done 2 ∧ (C.ts 0).2 .rbx = 0 ∧
    (C.ts 1).2 .rbx = 0 := by
  rintro ⟨C, hr, hd, e0, e1⟩
  obtain ⟨-, -, hf⟩ := reach_inv hr init_inv
  rcases hf (hd 0 (by decide)) (hd 1 (by decide)) with h | h
  · rw [e0] at h; cases h
  · rw [e1] at h; cases h

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Ex.Sb
