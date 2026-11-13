module

public import Silmaril.Process.Mt.Drf.Litmus.Defs
import Silmaril.Process.Mt.Drf.Thms

/-!
# Proofs of the litmus tests

* SC invariants: `SB` and `MP` have no weak outcome on the SC machine (racy or locked).
* Weak runs: racy `SB` reaches its weak outcome on the TSO machine, racy `MP` on the XL
  machine.
* Certificates: locked `SB` and locked `MP` are race free modulo synchronisation (`Cert`).
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Drf.Litmus

open Silmaril.Process.Mt.Drf
open Silmaril.Process.Mt.Drf.Litmus

/-! ## The programs -/

theorem sb_some {lk : Bool} {t pc : Nat} {i : Ins} (h : sb lk t pc = some i) :
    (t = 0 ∧ pc = 0 ∧ i = (if lk then .xchg 9 0 1 else .st 0 1)) ∨
    (t = 0 ∧ pc = 1 ∧ i = .ld 0 8) ∨
    (t = 1 ∧ pc = 0 ∧ i = (if lk then .xchg 9 8 1 else .st 8 1)) ∨
    (t = 1 ∧ pc = 1 ∧ i = .ld 0 0) := by
  unfold sb at h
  split at h <;> simp_all

theorem mp_some {lk : Bool} {t pc : Nat} {i : Ins} (h : mp lk t pc = some i) :
    (t = 0 ∧ pc = 0 ∧ i = .stnt 0 1) ∨
    (t = 0 ∧ pc = 1 ∧ i = (if lk then .xchg 9 8 1 else .st 8 1)) ∨
    (t = 1 ∧ pc = 0 ∧ i = .ld 0 8) ∨
    (t = 1 ∧ pc = 1 ∧ i = .brz 0 3) ∨
    (t = 1 ∧ pc = 2 ∧ i = .ld 1 0) := by
  unfold mp at h
  split at h <;> simp_all

theorem write_one (m : Mem) (a v x : Nat) : m.write [(a, v)] x = if x = a then v else m x := rfl

theorem star_induct {α : Type} {r : α → α → Prop} (P : α → Prop) {a b : α} (h : Star r a b)
    (h0 : P a) (hs : ∀ x y, P x → r x y → P y) : P b := by
  induction h with
  | refl => exact h0
  | step h _ ih => exact ih (hs _ _ h0 h)

/-! ## SB on SC -/

/-- `SB`'s SC invariant. -/
def SbInv {lk : Bool} (C : Cfg (sys (sb lk))) : Prop :=
  (1 ≤ (C.ts 0).pc → C.mem 0 = 1) ∧ (1 ≤ (C.ts 1).pc → C.mem 8 = 1) ∧
  ((C.ts 0).pc = 2 → (C.ts 1).pc = 2 → (C.ts 0).reg 0 = 1 ∨ (C.ts 1).reg 0 = 1)

theorem sbInv_step {lk : Bool} {C C' : Cfg (sys (sb lk))} (hI : SbInv C)
    (h : ScStep (sys (sb lk)) 2 C C') : SbInv C' := by
  obtain ⟨i1, i2, i3⟩ := hI
  cases h with
  | plain ht hs hr =>
    cases hs with
    | st h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        cases lk <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        refine ⟨?_, ?_, ?_⟩ <;> simp_all [upd, write_one]
    | stnt h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        cases lk <;> simp at hi
    | ld x h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        cases lk <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        have hx := hr _ List.mem_cons_self <;>
        refine ⟨?_, ?_, ?_⟩ <;> simp_all [upd, Mem.write] <;> omega
    | brz h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        cases lk <;> simp at hi
  | sfence ht hs =>
    cases hs with
    | sfence h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        cases lk <;> simp at hi
  | sync ht hs hr =>
    cases hs with
    | mfence h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        cases lk <;> simp at hi
    | xchg x h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        cases lk <;> simp at hi <;> obtain ⟨rfl, rfl, rfl⟩ := hi <;>
        refine ⟨?_, ?_, ?_⟩ <;> simp_all [upd, write_one]

/-- **`SB` has no weak outcome on SC** (racy or locked). -/
theorem sb_sc {lk : Bool} {C : Cfg (sys (sb lk))} (h : ScReach (sys (sb lk)) 2 (init _) C) :
    ¬ sbWeak C.ts := by
  have hI : SbInv C := star_induct SbInv h (by simp [SbInv, init])
    (fun _ _ hI hs => sbInv_step hI hs)
  rintro ⟨h0, h1, r0, r1⟩
  rcases hI.2.2 h0 h1 with h | h <;> simp_all

/-! ## MP on SC -/

/-- `MP`'s SC invariant. -/
def MpInv {lk : Bool} (C : Cfg (sys (mp lk))) : Prop :=
  (C.mem 8 ≠ 0 → C.mem 0 = 1) ∧ (1 ≤ (C.ts 0).pc → C.mem 0 = 1) ∧
  (1 ≤ (C.ts 1).pc → (C.ts 1).reg 0 ≠ 0 → C.mem 0 = 1) ∧
  ((C.ts 1).pc = 2 → (C.ts 1).reg 0 ≠ 0) ∧
  ((C.ts 1).pc = 3 → (C.ts 1).reg 0 ≠ 0 → (C.ts 1).reg 1 = 1)

theorem mpInv_step {lk : Bool} {C C' : Cfg (sys (mp lk))} (hI : MpInv C)
    (h : ScStep (sys (mp lk)) 2 C C') : MpInv C' := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hI
  cases h with
  | plain ht hs hr =>
    cases hs with
    | st h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> cases lk <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [upd, write_one]
    | stnt h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> cases lk <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [upd, write_one]
    | ld x h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> cases lk <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        have hx := hr _ List.mem_cons_self <;>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [upd, Mem.write] <;> omega
    | brz h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> cases lk <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        by_cases hz : (C.ts 1).reg 0 = 0 <;>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [upd, Mem.write]
  | sfence ht hs =>
    cases hs with
    | sfence h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> cases lk <;> simp at hi
  | sync ht hs hr =>
    cases hs with
    | mfence h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> cases lk <;> simp at hi
    | xchg x h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> cases lk <;> simp at hi <;> obtain ⟨rfl, rfl, rfl⟩ := hi <;>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [upd, write_one]

/-- **`MP` has no weak outcome on SC** (racy or locked). -/
theorem mp_sc {lk : Bool} {C : Cfg (sys (mp lk))} (h : ScReach (sys (mp lk)) 2 (init _) C) :
    ¬ mpWeak C.ts := by
  have hI : MpInv C := star_induct MpInv h (by simp [MpInv, init])
    (fun _ _ hI hs => mpInv_step hI hs)
  rintro ⟨h0, h1, h2⟩
  have := hI.2.2.2.2 h0 (by simp [h1])
  simp_all

/-! ## Weak runs -/

/-- **Racy `SB` reaches its weak outcome on the TSO machine**, drained. -/
theorem sb_tso : ∃ C : BCfg (sys (sb false)),
    BReach .tso (sys (sb false)) 2 (init _).toB C ∧ C.Drained ∧ sbWeak C.ts := by
  refine ⟨_, Star.step (BStep.plain (t := 0) (by decide) (LLoc.st (a := 0) (v := 1) rfl)
      (by simp [Mem.Reads])) <|
    Star.step (BStep.plain (t := 1) (by decide) (LLoc.st (a := 8) (v := 1) rfl)
      (by simp [Mem.Reads])) <|
    Star.step (BStep.plain (t := 0) (by decide) (LLoc.ld (r := 0) (a := 8) 0 rfl)
      (by simp [Mem.Reads, view, upd, ents, newest, Ent.val, init, Cfg.toB])) <|
    Star.step (BStep.plain (t := 1) (by decide) (LLoc.ld (r := 0) (a := 0) 0 rfl)
      (by simp [Mem.Reads, view, upd, ents, newest, Ent.val, init, Cfg.toB])) <|
    Star.step (BStep.flush (t := 0) (pre := []) (e := .st 0 1 false) (post := [])
      (by simp [upd, ents, Cfg.toB]) (by simp [Ent.passes]) (Or.inr rfl)) <|
    Star.step (BStep.flush (t := 1) (pre := []) (e := .st 8 1 false) (post := [])
      (by simp [upd, ents, Cfg.toB]) (by simp [Ent.passes]) (Or.inr rfl)) Star.refl, ?_, ?_⟩
  · intro t
    by_cases h1 : t = 1 <;> by_cases h0 : t = 0 <;> simp [upd, h1, h0, Cfg.toB, init]
  · simp [sbWeak, upd, init, Cfg.toB]

/-- **Racy `MP` reaches its weak outcome on the XL machine**: the flag store overtakes the
non-temporal data store. -/
theorem mp_xl : ∃ C : BCfg (sys (mp false)),
    BReach .xl (sys (mp false)) 2 (init _).toB C ∧ mpWeak C.ts := by
  refine ⟨_, Star.step (BStep.plain (t := 0) (by decide) (LLoc.stnt (a := 0) (v := 1) rfl)
      (by simp [Mem.Reads])) <|
    Star.step (BStep.plain (t := 0) (by decide) (LLoc.st (a := 8) (v := 1) rfl)
      (by simp [Mem.Reads])) <|
    Star.step (BStep.flush (t := 0) (pre := [.st 0 1 true]) (e := .st 8 1 false) (post := [])
      (by simp [upd, ents, Cfg.toB]) (by simp [Ent.passes]) (Or.inl rfl)) <|
    Star.step (BStep.plain (t := 1) (by decide) (LLoc.ld (r := 0) (a := 8) 1 rfl)
      (by simp [Mem.Reads, view, upd, newest, init, Cfg.toB, Ent.apply, Mem.set])) <|
    Star.step (BStep.plain (t := 1) (by decide) (LLoc.brz (r := 0) (k := 3) rfl)
      (by simp [Mem.Reads])) <|
    Star.step (BStep.plain (t := 1) (by decide) (LLoc.ld (r := 1) (a := 0) 0 rfl)
      (by simp [Mem.Reads, view, upd, ents, newest, init, Cfg.toB, Ent.apply,
        Mem.set])) Star.refl, ?_⟩
  simp [mpWeak, upd, init, Cfg.toB]

/-! ## Certificates -/

/-- Locked `SB` is race free modulo synchronisation: nobody owns anything, and its only plain
accesses are loads. -/
theorem sbLocked_cert : Cert (sys (sb true)) 2 (fun _ o => ∀ t a, ¬ o t a) where
  disj := fun _ _ h t _ a _ h1 _ => h t a h1
  rd := fun _ _ h _ _ _ _ _ _ _ p _ => Or.inr fun u => h u p.1
  wr := by
    intro C o _ t _ rs ws w s' hs p hp
    cases hs with
    | st h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        simp at hi
    | stnt h =>
      rcases sb_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ <;>
        simp at hi
    | ld x h => cases hp
    | brz h => cases hp
  syncFp := fun _ _ h _ _ _ _ _ _ _ _ u _ => h u _
  plain := fun _ o h _ _ _ _ _ _ _ _ => ⟨o, h, fun _ _ x => x⟩
  sfence := fun _ o h _ _ _ _ => ⟨o, h, fun _ _ x => x⟩
  sync := fun _ o h _ _ _ _ _ _ _ => ⟨o, h, fun _ _ _ x => x⟩

/-- Locked `MP` is race free modulo synchronisation. -/
theorem mpLocked_cert : Cert (sys (mp true)) 2 MpR where
  disj := by
    rintro C o ⟨rfl, j1, j2, j3⟩ t u a htu ⟨rfl, h1⟩ ⟨-, h2⟩
    rcases h1 with ⟨rfl, h1⟩ | ⟨rfl, h1, h1'⟩ <;> rcases h2 with ⟨rfl, h2⟩ | ⟨rfl, h2, h2'⟩ <;>
      first | exact htu rfl | have := j2 h2 h2'; omega | have := j2 h1 h1'; omega
  rd := by
    rintro C o ⟨rfl, j1, j2, j3⟩ t ht rs ws w s' hs p hp
    cases hs with
    | st h => cases hp
    | stnt h => cases hp
    | brz h => cases hp
    | ld x h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        simp at hp <;> subst hp <;> simp_all [mpOwn]
  wr := by
    rintro C o ⟨rfl, j1, j2, j3⟩ t ht rs ws w s' hs p hp
    cases hs with
    | ld x h => cases hp
    | brz h => cases hp
    | st h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi
    | stnt h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        simp at hp <;> subst hp <;> simp_all [mpOwn]
  syncFp := by
    rintro C o ⟨rfl, j1, j2, j3⟩ t ht rs ws ts' hs p hp u hu
    cases hs with
    | mfence h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi
    | xchg x h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi <;> obtain ⟨rfl, rfl, rfl⟩ := hi <;>
        simp at hp <;> rcases hp with rfl | rfl <;> simp [mpOwn]
  plain := by
    rintro C o ⟨rfl, j1, j2, j3⟩ t ht rs ws w s' hs hr
    cases hs with
    | st h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi
    | stnt h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        refine ⟨mpOwn _, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩ <;> simp_all [mpOwn, upd, write_one] <;> omega
    | ld x h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        have hx := hr _ List.mem_cons_self <;>
        refine ⟨mpOwn _, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩ <;> simp_all [mpOwn, upd, Mem.write] <;> omega
    | brz h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
        by_cases hz : (C.ts 1).reg 0 = 0 <;>
        refine ⟨mpOwn _, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩ <;> simp_all [mpOwn, upd, Mem.write] <;> omega
  sfence := by
    rintro C o ⟨rfl, j1, j2, j3⟩ t ht s' hs
    cases hs with
    | sfence h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi
  sync := by
    rintro C o ⟨rfl, j1, j2, j3⟩ t ht rs ws ts' hs hr
    cases hs with
    | mfence h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi
    | xchg x h =>
      rcases mp_some h with ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ | ⟨rfl, hpc, hi⟩ |
        ⟨rfl, hpc, hi⟩ <;> simp at hi <;> obtain ⟨rfl, rfl, rfl⟩ := hi <;>
        refine ⟨mpOwn _, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩ <;> simp_all [mpOwn, upd, write_one] <;> omega

/-! ## The bridge on the litmus tests -/

/-- **Locked `SB` has no weak outcome under TSO or XL**, by the bridge. -/
theorem sbLocked_buffered {M : Model} {C : BCfg (sys (sb true))}
    (h : BReach M (sys (sb true)) 2 (init _).toB C) : ¬ sbWeak C.ts :=
  sb_sc (drf_sc sbLocked_cert (o := fun _ _ => False) (fun _ _ h => h) h).1

/-- **Locked `MP` has no weak outcome under TSO or XL**, by the bridge. -/
theorem mpLocked_buffered {M : Model} {C : BCfg (sys (mp true))}
    (h : BReach M (sys (mp true)) 2 (init _).toB C) : ¬ mpWeak C.ts :=
  mp_sc (drf_sc mpLocked_cert (o := mpOwn (init _)) (by simp [MpR, init]) h).1

/-- **Racy `SB` has no certificate**: the bridge's hypothesis is needed. -/
theorem sbRacy_not_cert :
    ¬ ∃ (R : Cfg (sys (sb false)) → Own → Prop) (o : Own), Cert (sys (sb false)) 2 R ∧
      R (init _) o := by
  rintro ⟨R, o, hc, h0⟩
  obtain ⟨C, hr, -, hw⟩ := sb_tso
  exact sb_sc (drf_sc hc h0 hr).1 hw

/-- **Racy `MP` has no certificate**: the bridge's hypothesis is needed. -/
theorem mpRacy_not_cert :
    ¬ ∃ (R : Cfg (sys (mp false)) → Own → Prop) (o : Own), Cert (sys (mp false)) 2 R ∧
      R (init _) o := by
  rintro ⟨R, o, hc, h0⟩
  obtain ⟨C, hr, hw⟩ := mp_xl
  exact mp_sc (drf_sc hc h0 hr).1 hw

end Silmaril.Proofs.Process.Mt.Drf.Litmus
