module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Refine
public import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Solo
public import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Example

/-!
# Process-level threads: main-thread identification, fork-join end to end

* `refines_main`: the refinement maps the main thread to CIR thread `0` (it never gets a
  `clear_child_tid`, by `ctid_stable`; `Rel`'s `ctid` clause was strengthened to pin this).
* `forkJoin_result`: in every reachable state of the lowered fork-join process, a main thread
  about to call `exit_group` has `rax = 42` (proved on CIR by the invariant `FjInv`, transferred
  by `refines_main`).
* `fj_run`: such a state is reachable (a full concrete run: clone, the child's prologue, store
  and `exit` with the clear of `ctl 1`, the main thread's join loop and load), so
  `forkJoin_result` is not vacuous.
* `fj_noJoin_run`: with `join 1` erased from the lowering, the process reaches the same point
  with `rax = 0`; the result depends on the futex join.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd Star)
open Silmaril.X86.Concurrency.Cir.Proc


section
variable {P : SProg} {L : Layout} {base : Base}

/-- Lowered code never requests `set_tid_address`. -/
theorem no_setTid {C : PCfg PSt} {A : SCfg} {g : Nat → Nat} (R : RelG P L C A g) {t : Nat}
    {r : TRec PSt} (ht : C.th t = some r) :
    ∀ s a args k ch, r.st = .run s →
      ¬ (pIsa (P.code L)).step r.tp s (.sys nrSetTid (a :: args) k ch) := by
  intro s a args k ch hr hs
  rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [nrSetTid, nrFutex, nrClone] at h
  · cases h; rcases he with h | h <;> simp [nrSetTid, nrExit, nrExitGroup] at h

/-- **The main thread is CIR thread `0`**: in every reachable lowered process, the main
thread is present, has no `clear_child_tid`, and so the refinement maps it to thread `0`. -/
theorem refines_main (hw : P.Wf) (hss : P.SyncSafe) (tid0 : Nat) (tp0 : Word)
    {C : PCfg (pIsa (P.code L)).St} (h : PReach (pIsa (P.code L)) base (P.pinit L tid0 tp0) C) :
    ∃ A g r, SReach P P.init A ∧ RelG P L C A g ∧ C.th tid0 = some r ∧ r.ctid = none ∧
      g tid0 = 0 := by
  suffices key : ∀ C0 C, PReach (pIsa (P.code L)) base C0 C → ∀ A g, SReach P P.init A →
      RelG P L C0 A g → (∃ r, C0.th tid0 = some r ∧ r.ctid = none) →
      ∃ A g r, SReach P P.init A ∧ RelG P L C A g ∧ C.th tid0 = some r ∧ r.ctid = none by
    obtain ⟨A, g, r, hA, R, ht, hc⟩ := key _ _ h _ _ .refl (relG_init hw tid0 tp0)
      ⟨_, ite_eq_left rfl, rfl⟩
    refine ⟨A, g, r, hA, R, ht, hc, ?_⟩
    rcases (R.thr _ _ ht).2.2.2 with ⟨-, h0⟩ | ⟨hc', -⟩
    · exact h0
    · rw [hc] at hc'; cases hc'
  intro C0 C hr
  induction hr with
  | refl => intro A g hA R ⟨r, ht, hc⟩; exact ⟨A, g, r, hA, R, ht, hc⟩
  | step hs _ ih =>
    intro A g hA R ⟨r, ht, hc⟩
    obtain ⟨A', g', hAA, R'⟩ := rel_step hw hss hA R hs
    obtain ⟨r', ht', hc'⟩ := ctid_stable hs ht (no_setTid R ht)
    exact ih A' g' (star_trans hA hAA) R' ⟨r', ht', hc'.trans hc⟩

end

/-! ## Fork-join: the join really orders the child's store before the main thread's load -/

/-- The main thread after `spawn 1`. -/
def fjLd : Stmt := .load .rax .na 8 .wb (.lit Ex.x)
def fjR : Stmt := .seq (.join 1) fjLd

/-- The invariant of the fork-join sync machine. -/
def FjInv (A : SCfg) : Prop :=
  (((A.ts 1).1 = Ex.child ∧ A.mem Ex.x = some 0) ∨ ((A.ts 1).1 = .skip ∧ A.mem Ex.x = some 42)) ∧
  ((A.ts 0).1 = Ex.main ∨ (A.ts 0).1 = .seq .skip fjR ∨ (A.ts 0).1 = fjR ∨
    ((A.ts 1).1 = .skip ∧ ((A.ts 0).1 = .seq .skip fjLd ∨ (A.ts 0).1 = fjLd ∨
      ((A.ts 0).1 = .skip ∧ (A.ts 0).2 .rax = 42))))

theorem fjInv_init : FjInv Ex.forkJoin.init := by
  refine ⟨Or.inl ⟨rfl, ?_⟩, Or.inl rfl⟩
  simp [SProg.init, Ex.forkJoin, Ex.heap]

theorem fjInv_step {A B : SCfg} (I : FjInv A) (h : SStep Ex.forkJoin.N A B) : FjInv B := by
  obtain ⟨h1, h0⟩ := I
  have hN : Ex.forkJoin.N = 2 := rfl
  cases h with
  | tau ht hst hs =>
    rename_i t s' rs'
    rw [hN] at ht
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rcases h0 with e | e | e | ⟨e1, e | e | ⟨e, -⟩⟩ <;> rw [e] at hs
      · cases hs; rename_i hh; cases hh
      · cases hs
        · rename_i hh; cases hh
        · exact ⟨by simpa [upd] using h1, Or.inr (Or.inr (Or.inl (by simp [upd])))⟩
      · cases hs; rename_i hh; cases hh
      · cases hs
        · rename_i hh; cases hh
        · exact ⟨by simpa [upd] using h1, Or.inr (Or.inr (Or.inr ⟨by simpa [upd] using e1,
            Or.inr (Or.inl (by simp [upd]))⟩))⟩
      · cases hs
      · cases hs
    · rcases h1 with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] at hs <;> cases hs
  | lab ht hst hs hm hc hok =>
    rename_i t l s' rs'
    rw [hN] at ht
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rcases h0 with e | e | e | ⟨e1, e | e | ⟨e, -⟩⟩ <;> rw [e] at hs
      · cases hs; rename_i hh; cases hh; cases hm
      · cases hs; rename_i hh; cases hh
      · cases hs; rename_i hh; cases hh; cases hm
      · cases hs; rename_i hh; cases hh
      · cases hs
        rename_i v hv
        rcases h1 with ⟨e2, -⟩ | ⟨e2, hx⟩
        · rw [e1] at e2; cases e2
        have := hok (Ex.x, v) (by simp [Lab.reads, Ex.x]; rfl)
        rw [hx] at this; cases this
        refine ⟨Or.inr ⟨by simpa [upd] using e1, ?_⟩, Or.inr (Or.inr (Or.inr ⟨by simpa [upd] using e1,
          Or.inr (Or.inr ⟨by simp [upd], ?_⟩)⟩))⟩
        · simp [Lab.updH, Lab.wval, hx]
        · simp [upd, Regs.set]
      · cases hs
    · rcases h1 with ⟨e, hx⟩ | ⟨e, -⟩ <;> rw [e] at hs
      · cases hs
        refine ⟨Or.inr ⟨by simp [upd], ?_⟩, ?_⟩
        · simp [Lab.updH, Lab.wval, Ex.x, Expr.eval]
        · rcases h0 with e0 | e0 | e0 | ⟨e1, -⟩
          · exact Or.inl (by simpa [upd] using e0)
          · exact Or.inr (Or.inl (by simpa [upd] using e0))
          · exact Or.inr (Or.inr (Or.inl (by simpa [upd] using e0)))
          · rw [e] at e1; cases e1
      · cases hs
  | spawn ht hst hs hu hns =>
    rename_i t u s' rs'
    rw [hN] at ht
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rcases h0 with e | e | e | ⟨e1, e | e | ⟨e, -⟩⟩ <;> rw [e] at hs
      · cases hs; rename_i hh; cases hh
        exact ⟨by simpa [upd] using h1, Or.inr (Or.inl (by simp [upd]; rfl))⟩
      · cases hs; rename_i hh; cases hh
      · cases hs; rename_i hh; cases hh
      · cases hs; rename_i hh; cases hh
      · cases hs
      · cases hs
    · rcases h1 with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] at hs <;> cases hs
  | join ht hst hs hu hd =>
    rename_i t u s' rs'
    rw [hN] at ht
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rcases h0 with e | e | e | ⟨e1, e | e | ⟨e, -⟩⟩ <;> rw [e] at hs
      · cases hs; rename_i hh; cases hh
      · cases hs; rename_i hh; cases hh
      · cases hs; rename_i hh; cases hh
        have hsk : (A.ts 1).1 = .skip := hd
        exact ⟨by simpa [upd] using h1, Or.inr (Or.inr (Or.inr ⟨by simpa [upd] using hsk,
          Or.inl (by simp [upd])⟩))⟩
      · cases hs; rename_i hh; cases hh
      · cases hs
      · cases hs
    · rcases h1 with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] at hs <;> cases hs

theorem fjInv_reach {A : SCfg} (h : SReach Ex.forkJoin Ex.forkJoin.init A) : FjInv A := by
  suffices ∀ A0 A, Star (SStep Ex.forkJoin.N) A0 A → FjInv A0 → FjInv A from
    this _ _ h fjInv_init
  intro A0 A hr
  induction hr with
  | refl => exact id
  | step hs _ ih => exact fun I => ih (fjInv_step I hs)

/-- **Fork-join, end to end on the process**: in every reachable state of the lowered
fork-join process, once the main thread has finished its body (it is about to call
`exit_group`), its `rax` holds the child's `42`. So the futex/clear-child-tid join really
orders the child's store before the main thread's load. -/
theorem forkJoin_result (base : Base) (tid0 : Nat) (tp0 : Word)
    {C : PCfg (pIsa (Ex.forkJoin.code Ex.layout)).St}
    (h : PReach (pIsa (Ex.forkJoin.code Ex.layout)) base (Ex.forkJoin.pinit Ex.layout tid0 tp0) C)
    {r : TRec PSt} {rs : Regs} (ht : C.th tid0 = some r) (hr : r.st = .run (.seq .skip exitGroupS, rs)) :
    rs .rax = 42 := by
  obtain ⟨A, g, r', hA, R, ht', -, hg⟩ :=
    refines_main forkJoin_wf (syncSafe_of_static forkJoin_static) tid0 tp0 h
  rw [ht] at ht'; cases ht'
  have hT := (R.thr _ _ ht).2.2.1
  simp only [TCorr, hr, hg] at hT
  have I := fjInv_reach hA
  generalize hx : A.ts 0 = x at hT
  obtain ⟨s0, rs0⟩ := x
  cases hT with
  | tail hc he =>
    obtain ⟨hs0, ha⟩ := corr_skip hc rfl
    obtain ⟨-, I0⟩ := I
    rw [hx] at I0
    simp only at I0 hs0
    subst hs0
    rcases I0 with e | e | e | ⟨-, e | e | ⟨-, h42⟩⟩
    · cases e
    · cases e
    · cases e
    · cases e
    · cases e
    · rw [ha .rax (by decide)]; exact h42
  | fin he => rcases he with he | he <;> cases he

/-! ## A concrete run of the lowered fork-join process -/

/-- The deterministic silent step of a PIR thread, if it has one. -/
def nextTau : PStmt → Regs → Option PSt
  | .cir (.assign d e), rs => some (.skip, rs.set d (e.eval rs))
  | .seq .skip q, rs => some (q, rs)
  | .seq p q, rs => (nextTau p rs).map fun x => (.seq x.1 q, x.2)
  | .ite c p q, rs => some (if truthy (c.eval rs) then p else q, rs)
  | .whl c b, rs => some (if truthy (c.eval rs) then .seq b (.whl c b) else .skip, rs)
  | _, _ => none

theorem nextTau_sound (code : Nat → PStmt) (tp : Word) :
    ∀ (p : PStmt) (rs : Regs) (y : PSt), nextTau p rs = some y → PTStep code tp p rs (.tau y)
  | .cir s, rs, y, h => by
    cases s <;> simp [nextTau] at h
    subst h; exact ⟨_, Or.inl ⟨.assign, rfl⟩⟩
  | .seq p q, rs, y, h => by
    cases p with
    | skip => simp [nextTau] at h; subst h; exact Or.inl ⟨rfl, rfl⟩
    | _ =>
      simp only [nextTau, Option.map_eq_some_iff] at h
      obtain ⟨y', h1, rfl⟩ := h
      exact Or.inr ⟨.tau y', nextTau_sound code tp _ rs y' h1, rfl⟩
  | .ite c p q, rs, y, h => by simp [nextTau] at h; subst h; rfl
  | .whl c b, rs, y, h => by simp [nextTau] at h; subst h; rfl
  | .skip, _, _, h | .sys .., _, _, h | .tp _, _, _, h | .loop .., _, _, h => by
    simp [nextTau] at h

/-- Run silent steps, at most `n`. -/
def runTau : Nat → PSt → PSt
  | 0, x => x
  | n + 1, x => match nextTau x.1 x.2 with
    | some y => runTau n y
    | none => x

theorem setTh_setTh {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) (r1 r2 : TRec σ) :
    setTh (setTh th t r1) t r2 = setTh th t r2 := by
  funext u; simp only [setTh, upd]; split <;> rfl

theorem setTh_self {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) (r : TRec σ)
    (h : th t = some r) : setTh th t r = th := by
  funext u; simp only [setTh, upd]; split <;> simp_all

/-- **Silent runs of one thread lift to the process.** -/
theorem tau_run {code : Nat → PStmt} {base : Base} (t : Nat) (tp : Word) (c : Option Nat) :
    ∀ (n : Nat) (C : PCfg (pIsa code).St) (x : PSt), C.status = none →
      C.th t = some ⟨.run x, tp, c⟩ →
      PReach (pIsa code) base C ⟨setTh C.th t ⟨.run (runTau n x), tp, c⟩, C.mem, C.status⟩
  | 0, C, x, _, ht => by
    show PReach (pIsa code) base C ⟨setTh C.th t ⟨.run x, tp, c⟩, C.mem, C.status⟩
    rw [setTh_self _ _ _ ht]; exact .refl
  | n + 1, C, x, hl, ht => by
    show PReach (pIsa code) base C ⟨setTh C.th t ⟨.run (match nextTau x.1 x.2 with
      | some y => runTau n y | none => x), tp, c⟩, C.mem, C.status⟩
    split
    · rename_i y hy
      have hs := PStep.tau (I := pIsa code) (base := base) hl ht rfl
        (nextTau_sound code tp x.1 x.2 y hy)
      refine .step hs ?_
      have := tau_run (base := base) t tp c n ⟨setTh C.th t ⟨.run y, tp, c⟩, C.mem, C.status⟩ y hl (setTh_same _ _ _)
      rw [setTh_setTh] at this
      exact this
    · rw [setTh_self _ _ _ ht]; exact .refl

theorem seq_lift {code : Nat → PStmt} {tp : Word} {p q : PStmt} {rs : Regs} {a : UAct PSt}
    (h : PTStep code tp p rs a) :
    PTStep code tp (.seq p q) rs (a.wrap (fun x => (.seq x.1 q, x.2))) := Or.inr ⟨a, h, rfl⟩


section FJ
open Ex

abbrev fjCode : Nat → PStmt := Ex.forkJoin.code Ex.layout

theorem ex_step {base : Base} {Q : PCfg (pIsa fjCode).St → Prop} {C0 C1 : PCfg (pIsa fjCode).St}
    (h : PStep (pIsa fjCode) base C0 C1) (k : ∃ C, PReach (pIsa fjCode) base C1 C ∧ Q C) :
    ∃ C, PReach (pIsa fjCode) base C0 C ∧ Q C :=
  let ⟨C, h1, h2⟩ := k; ⟨C, .step h h1, h2⟩

theorem ex_reach {base : Base} {Q : PCfg (pIsa fjCode).St → Prop} {C0 C1 : PCfg (pIsa fjCode).St}
    (h : PReach (pIsa fjCode) base C0 C1) (k : ∃ C, PReach (pIsa fjCode) base C1 C ∧ Q C) :
    ∃ C, PReach (pIsa fjCode) base C0 C ∧ Q C :=
  let ⟨C, h1, h2⟩ := k; ⟨C, star_trans h h1, h2⟩

def fjArgs : List Expr :=
  [.lit cloneMusl, .lit (Ex.layout.stk 1), .lit (ctlAddr 1), .lit (ctlAddr 1), .lit (Ex.layout.tls 1)]

theorem fj_run (base : Base) : ∃ C, PReach (pIsa fjCode) base (Ex.forkJoin.pinit Ex.layout 1 0) C ∧
    ∃ rs, C.th 1 = some ⟨.run (.seq .skip exitGroupS, rs), 0, none⟩ ∧ rs .rax = 42 := by
  -- 1. main: clone
  have h0 : PTStep fjCode 0 (spawnS Ex.layout 1) Regs.zero
      (.sys nrClone (fjArgs.map (·.eval Regs.zero)) (fun w => (.skip, Regs.setO Regs.zero none w))
        (fjCode 1, childRegs Regs.zero fjArgs)) := rfl
  have hsys := seq_lift (q := exitGroupS) (seq_lift (q := lower Ex.layout (.seq (.join 1) (.load .rax .na 8 .wb (.lit x))))  h0)
  have hpt : (Ex.forkJoin.pheap (BitVec.ofNat 64 (ctlAddr 1)).toNat).isSome := by
    rw [show (BitVec.ofNat 64 (ctlAddr 1)).toNat = ctlAddr 1 by decide, pheap_ctl (by decide) (by decide)]
    rfl
  refine ex_step (PStep.clone (I := pIsa fjCode) (base := base) (C := Ex.forkJoin.pinit Ex.layout 1 0)
    (t := 1) (t' := 2) rfl rfl rfl hsys (Or.inl (by decide)) rfl (by decide) (by decide) hpt) ?_
  -- 2. child: zero the registers
  refine ex_reach (tau_run 2 _ _ 60 _ (fjCode 1, childRegs Regs.zero fjArgs) rfl rfl) ?_
  have e2 : (runTau 60 (fjCode 1, childRegs Regs.zero fjArgs)).1 =
      .seq (.cir (.store .na 8 .wb (.lit x) (.lit 42))) exitS := by
    rfl
  -- 3. child: the store
  have hs2 : (pIsa fjCode).step (BitVec.ofNat 64 (Ex.layout.tls 1)) (runTau 60 (fjCode 1, childRegs Regs.zero fjArgs))
      (.mem (.wr .na .wb 4096 8 42) (.seq .skip exitS, (runTau 60 (fjCode 1, childRegs Regs.zero fjArgs)).2)) := by
    show PTStep fjCode _ (runTau 60 _).1 (runTau 60 _).2 _
    rw [e2]
    exact seq_lift (show PTStep fjCode _ (.cir (.store .na 8 .wb (.lit x) (.lit 42))) _
      (.mem (.wr .na .wb 4096 8 42) (.skip, _)) from ⟨_, Or.inr ⟨_, TStep.store, rfl⟩⟩)
  refine ex_step (PStep.mem (t := 2) rfl rfl rfl hs2 rfl (fun a ha => ?_) (fun p hp => by simp [Lab.reads] at hp)) ?_
  · simp [Lab.Touches, Lab.reads, Lab.wval] at ha; subst ha; rfl
  -- 4. child: exit, clearing `ctl 1`
  refine ex_reach (tau_run 2 _ _ 5 _ (.seq .skip exitS, (runTau 60 (fjCode 1, childRegs Regs.zero fjArgs)).2) rfl rfl) ?_
  have hs4 : (pIsa fjCode).step (BitVec.ofNat 64 (Ex.layout.tls 1))
      (runTau 5 (.seq .skip exitS, (runTau 60 (fjCode 1, childRegs Regs.zero fjArgs)).2))
      (.sys nrExit [BitVec.ofNat 64 0] (fun w => (.skip, Regs.setO (runTau 60 (fjCode 1, childRegs Regs.zero fjArgs)).2 none w))
        (fjCode 0, childRegs (runTau 60 (fjCode 1, childRegs Regs.zero fjArgs)).2 [.lit 0])) := rfl
  refine ex_step (PStep.exitClear (t := 2) (ws := []) rfl rfl rfl hs4 rfl rfl ⟨1, _, rfl, rfl⟩
    ⟨List.nodup_nil, by simp, by simp⟩) ?_
  -- 5. main: to the join loop's load of `ctl 1`
  refine ex_reach (tau_run 1 _ _ 60 _ (.seq (.seq .skip (lower Ex.layout (.seq (.join 1) fjLd))) exitGroupS,
    Regs.setO Regs.zero none (BitVec.ofNat 64 2)) rfl rfl) ?_
  have e5 : (runTau 60 (.seq (.seq .skip (lower Ex.layout (.seq (.join 1) fjLd))) exitGroupS,
      Regs.setO Regs.zero none (BitVec.ofNat 64 2))).1 =
      .seq (.seq (.seq (.seq (jLd 1) (jIt 1)) (jW 1)) (.cir fjLd)) exitGroupS := rfl
  -- 6. main: `ctl 1` reads `0`
  have hs6 : (pIsa fjCode).step 0 (runTau 60 (.seq (.seq .skip (lower Ex.layout (.seq (.join 1) fjLd))) exitGroupS,
      Regs.setO Regs.zero none (BitVec.ofNat 64 2)))
      (.mem (.rd .acq .wb (ctlAddr 1) 4 0) (.seq (.seq (.seq (.seq .skip (jIt 1)) (jW 1)) (.cir fjLd)) exitGroupS,
        (runTau 60 (.seq (.seq .skip (lower Ex.layout (.seq (.join 1) fjLd))) exitGroupS,
          Regs.setO Regs.zero none (BitVec.ofNat 64 2))).2.set scratch (BitVec.ofNat 64 0))) := by
    show PTStep fjCode _ (runTau 60 _).1 (runTau 60 _).2 _
    rw [e5]
    exact seq_lift (seq_lift (seq_lift (seq_lift (show PTStep fjCode _ (jLd 1) _
      (.mem (.rd .acq .wb (ctlAddr 1) 4 0) (.skip, _)) from ⟨_, Or.inr ⟨_, TStep.load (by decide), rfl⟩⟩))))
  refine ex_step (PStep.mem (t := 1) rfl rfl rfl hs6 rfl (fun a ha => ?_) (fun p hp => ?_)) ?_
  · simp [Lab.Touches, Lab.reads, Lab.wval] at ha; subst ha; rfl
  · simp [Lab.reads] at hp; subst hp; rfl
  -- 7. main: leave the join loop
  refine ex_reach (tau_run 1 _ _ 60 _ _ rfl rfl) ?_
  have e7 : (runTau 60 (.seq (.seq (.seq (.seq .skip (jIt 1)) (jW 1)) (.cir fjLd)) exitGroupS,
        (runTau 60 (.seq (.seq .skip (lower Ex.layout (.seq (.join 1) fjLd))) exitGroupS,
          Regs.setO Regs.zero none (BitVec.ofNat 64 2))).2.set scratch (BitVec.ofNat 64 0))).1 =
      .seq (.cir fjLd) exitGroupS := rfl
  -- 8. main: `x` reads `42`
  have hs8 : (pIsa fjCode).step 0 (runTau 60 (.seq (.seq (.seq (.seq .skip (jIt 1)) (jW 1)) (.cir fjLd)) exitGroupS,
        (runTau 60 (.seq (.seq .skip (lower Ex.layout (.seq (.join 1) fjLd))) exitGroupS,
          Regs.setO Regs.zero none (BitVec.ofNat 64 2))).2.set scratch (BitVec.ofNat 64 0)))
      (.mem (.rd .na .wb 4096 8 42) (.seq .skip exitGroupS,
        (runTau 60 (.seq (.seq (.seq (.seq .skip (jIt 1)) (jW 1)) (.cir fjLd)) exitGroupS,
        (runTau 60 (.seq (.seq .skip (lower Ex.layout (.seq (.join 1) fjLd))) exitGroupS,
          Regs.setO Regs.zero none (BitVec.ofNat 64 2))).2.set scratch (BitVec.ofNat 64 0))).2.set .rax
          (BitVec.ofNat 64 42))) := by
    show PTStep fjCode _ (runTau 60 _).1 (runTau 60 _).2 _
    rw [e7]
    exact seq_lift (show PTStep fjCode _ (.cir fjLd) _
      (.mem (.rd .na .wb 4096 8 42) (.skip, _)) from ⟨_, Or.inr ⟨_, TStep.load (by decide), rfl⟩⟩)
  refine ex_step (PStep.mem (t := 1) rfl rfl rfl hs8 rfl (fun a ha => ?_) (fun p hp => ?_)) ?_
  · simp [Lab.Touches, Lab.reads, Lab.wval] at ha; subst ha; rfl
  · simp [Lab.reads] at hp; subst hp; rfl
  exact ⟨_, .refl, _, rfl, by simp [Regs.set]⟩

/-- **Mutant**: the main thread of fork-join with `join 1` lowered to nothing. -/
def mainNoJoin : PStmt := .seq (.seq (spawnS Ex.layout 1) (.seq .skip (.cir fjLd))) exitGroupS

/-- **The mutant fails the fork-join property**: with the join erased, the lowered process
reaches the main thread's `exit_group` with `rax = 0`. So `forkJoin_result` depends on the
futex join of the lowering. -/
theorem fj_noJoin_run (base : Base) :
    ∃ C, PReach (pIsa fjCode) base (PCfg.init 1 (mainNoJoin, Regs.zero) 0 Ex.forkJoin.pheap) C ∧
      ∃ rs, C.th 1 = some ⟨.run (.seq .skip exitGroupS, rs), 0, none⟩ ∧ rs .rax = 0 := by
  have h0 : PTStep fjCode 0 (spawnS Ex.layout 1) Regs.zero
      (.sys nrClone (fjArgs.map (·.eval Regs.zero)) (fun w => (.skip, Regs.setO Regs.zero none w))
        (fjCode 1, childRegs Regs.zero fjArgs)) := rfl
  have hsys := seq_lift (q := exitGroupS) (seq_lift (q := .seq .skip (.cir fjLd)) h0)
  have hpt : (Ex.forkJoin.pheap (BitVec.ofNat 64 (ctlAddr 1)).toNat).isSome := by
    rw [show (BitVec.ofNat 64 (ctlAddr 1)).toNat = ctlAddr 1 by decide, pheap_ctl (by decide) (by decide)]
    rfl
  refine ex_step (PStep.clone (I := pIsa fjCode) (base := base)
    (C := PCfg.init 1 (mainNoJoin, Regs.zero) 0 Ex.forkJoin.pheap)
    (t := 1) (t' := 2) rfl rfl rfl hsys (Or.inl (by decide)) rfl (by decide) (by decide) hpt) ?_
  refine ex_reach (tau_run 1 _ _ 60 _ _ rfl rfl) ?_
  have e : (runTau 60 (.seq (.seq .skip (.seq .skip (.cir fjLd))) exitGroupS,
      Regs.setO Regs.zero none (BitVec.ofNat 64 2))).1 = .seq (.cir fjLd) exitGroupS := rfl
  have hs : (pIsa fjCode).step 0 (runTau 60 (.seq (.seq .skip (.seq .skip (.cir fjLd))) exitGroupS,
      Regs.setO Regs.zero none (BitVec.ofNat 64 2)))
      (.mem (.rd .na .wb 4096 8 0) (.seq .skip exitGroupS,
        (runTau 60 (.seq (.seq .skip (.seq .skip (.cir fjLd))) exitGroupS,
          Regs.setO Regs.zero none (BitVec.ofNat 64 2))).2.set .rax (BitVec.ofNat 64 0))) := by
    show PTStep fjCode _ (runTau 60 _).1 (runTau 60 _).2 _
    rw [e]
    exact seq_lift (show PTStep fjCode _ (.cir fjLd) _
      (.mem (.rd .na .wb 4096 8 0) (.skip, _)) from ⟨_, Or.inr ⟨_, TStep.load (by decide), rfl⟩⟩)
  refine ex_step (PStep.mem (t := 1) rfl rfl rfl hs rfl (fun a ha => ?_) (fun p hp => ?_)) ?_
  · simp [Lab.Touches, Lab.reads, Lab.wval] at ha; subst ha; rfl
  · simp [Lab.reads] at hp; subst hp; rfl
  exact ⟨_, .refl, _, rfl, by simp [Regs.set]⟩

end FJ

end Silmaril.Proofs.X86.Concurrency.Cir.Proc
