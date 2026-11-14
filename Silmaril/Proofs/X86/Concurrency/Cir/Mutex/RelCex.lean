module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Inst
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Client
public import Silmaril.X86.Concurrency.Cir.Robust.Thms

/-!
# Proofs: the statement of `Task.movUnlock` is false

`movUnlockIface_false : ¬ movUnlockIface`. The counterexample is one client, `cx`, with one thread and
one mutex at `0x100`. A `Client`'s body is any Lean function of its two holes, so `cx` tests
whether its unlock hole is the `mov` unlock:

* if it is not, the body is `skip`, and the goal (`[0x300] = 0`, the client's own cell) holds;
* if it is, the body is `lock; unlock; lock; [0x300] := 1`.

`cx` is proved against every `Iface` (`cx_proved`): in the second case the `Iface`'s unlock
code *is* the `mov`, and its `unlock_spec` then shows that no invariant state is disjoint from a
heap holding the lock token (the `mov` is a non-draining write of a cell the holder does not own,
which `LabOk` allows only when no such state exists). So after the first `lock` the thread
is in an inconsistent state, its later steps are vacuously safe, and the postcondition `False` is
never reached. Linked with the real spin lock and `mov` unlock, the thread finishes with
`[0x300] = 1` (`cx_run`, by the explorer on the single-thread start).

The restated Task (over `ProvedR`) excludes `cx`: `cx` is not proved against `spinMov`, where its
lock returns.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Robust

/-! ## The client -/

/-- The mutex (`Even`'s). -/
abbrev cxM : Nat := Even.m
/-- The client's cell (`Even`'s first output). -/
abbrev cxO : Nat := Even.out 0

/-- The `mov` unlock, called on the mutex. -/
def movCall : Stmt := .seq (.assign .rdi (.lit cxM)) (movUnlockCode 0)

/-- The misbehaving body: lock, unlock, lock, `[0x300] := 1`. -/
def cxBad (lk ul : Expr → Stmt) : Stmt :=
  Tv.chain [lk (.lit cxM), ul (.lit cxM), lk (.lit cxM), .store .na 8 .wb (.lit cxO) (.lit 1)]

open Classical in
/-- **The body**: misbehave exactly when the unlock hole is the `mov` unlock. -/
noncomputable def cxBody (lk ul : Expr → Stmt) (_t : Nat) : Stmt :=
  if ul (.lit cxM) = movCall then cxBad lk ul else .skip

/-- **The client**: one thread, the cell `0x300 ↦ 0`, one mutex at `0x100`, an 8-byte slot. -/
noncomputable def cx : Client := ⟨1, cxBody, Heap.single cxO 0, [cxM], 8⟩

/-- **The goal**: the client's cell still holds `0`. -/
def cxGoal (_ : Nat → Regs) (mem : Heap) : Prop := mem cxO = some 0

/-! ## Proved against every interface -/

/-- The thread's own cell. -/
def cxOwn (t : Nat) : Heap := if t = 0 then Heap.single cxO 0 else Heap.empty

theorem cxOwn_disj {t u : Nat} (h : t ≠ u) : Heap.Disjoint (cxOwn t) (cxOwn u) := by
  unfold cxOwn
  split
  · split
    · omega
    · exact disjoint_empty_right _
  · exact disjoint_empty _

theorem cxOwn_le (M : Iface) (L : Nat) (t : Nat) : Heap.Le (cxOwn t) (cx.link M L).mem := by
  intro a v e
  unfold cxOwn at e
  split at e
  · simp only [single_apply] at e
    split at e
    · rename_i ha; subst ha; cases e
      show Heap.union (Heap.single cxO 0) (Heap.union (M.init cxM) Heap.empty) cxO = _
      exact union_some (by simp [single_apply])
    · cases e
  · simp [Heap.empty] at e

theorem cxOwn_disjI (M : Iface) (hM : M.size ≤ 8) (t : Nat) :
    Heap.Disjoint (cxOwn t) (Heap.union (M.init cxM) Heap.empty) := by
  unfold cxOwn; split
  · exact disjoint_single_left (by rw [union_none (init_far M hM (Or.inr (out_far 0)))]; rfl)
  · exact disjoint_empty _

theorem cxI_le (M : Iface) (hM : M.size ≤ 8) (L : Nat) :
    Heap.Le (Heap.union (M.init cxM) Heap.empty) (cx.link M L).mem := by
  intro a v e
  show Heap.union (Heap.single cxO 0) (Heap.union (M.init cxM) Heap.empty) a = _
  have ha : a ≠ cxO := fun h => by
    subst h; rw [union_none (init_far M hM (Or.inr (out_far 0)))] at e; cases e
  rw [union_none (by simp [single_apply, ha])]; exact e

/-- With the `mov` as unlock code, no invariant state is disjoint from a token heap. -/
theorem mov_no_inv (M : Iface) (L : Nat) (hmov : M.unlockCode L = movUnlockCode 0) {hk : Heap}
    (hh : (hemp ∗ M.locked cxM) hk) :
    ∀ hI, (M.inv cxM hemp ∗ hemp) hI → ¬ Heap.Disjoint hk hI := by
  intro hI iI dI
  let rs : Regs := Regs.zero.set .rdi (BitVec.ofNat 64 cxM)
  have hrs : (rs .rdi).toNat = cxM := by simp [rs, Regs.set, Even.m]
  have S := M.unlock_spec cxM hemp hemp L rs hk hrs hh
  rw [hmov] at S
  obtain ⟨R, hR, post⟩ := S
  have F := post _ _ _ hR
  have st : TStep (movUnlockCode 0) rs (some (.wr .rel .wb cxM 4 0)) (.seq .skip .skip) rs := by
    have := TStep.seq (t := .skip) (TStep.store (m := .rel) (sz := 4) (fl := .wb)
      (a := Prim.at_ .rdi 0) (v := .lit 0) (rs := rs))
    have e1 : ((Prim.at_ .rdi 0).eval rs).toNat = cxM := by
      simp [Prim.at_, Expr.eval, BinOp.eval, hrs]
    have e2 : ((Expr.lit 0).eval rs).toNat % 2 ^ (8 * 4) = 0 := by simp [Expr.eval]
    rw [e1, e2] at this; exact this
  obtain ⟨-, -, hat⟩ := F.2.2 _ _ _ st
  obtain ⟨-, hw, hex⟩ := hat rfl hI iI dI
  have hkm : (hk cxM).isSome := hw rfl cxM (by simp [Lab.wval])
  obtain ⟨h', hI', -, -, -, hK, sur⟩ := hex (fun p hp => by simp [Lab.reads] at hp)
  have F2 := post _ _ _ hK
  have F3 := post _ _ _ (F2.2.1 _ _ TStep.seqSkip)
  have he : h' = Heap.empty := F3.1 rfl
  have := sur rfl cxM hkm
  rw [he] at this; simp [Heap.empty] at this

/-- A plain store from a heap no invariant state is disjoint from: vacuously safe. -/
theorem safe_dead {I : HProp} {Q : Regs → HProp} {h : Heap}
    (hno : ∀ hI, I hI → ¬ Heap.Disjoint h hI) {m : Mode} (hm : m ≠ .na) {sz : Nat} {fl : Flav}
    {a v : Expr} {rs : Regs} {t : Stmt} : Csl.Safe I Q (.seq (.store m sz fl a v) t) rs h := by
  apply safe_seq
  refine safe_atomic (by intro e; cases e) (fun s' rs' st => by cases st) ?_
  intro l s' rs' st
  cases st
  refine ⟨rfl, rfl, fun e => ?_, fun _ hI iI d => absurd d (hno hI iI)⟩
  cases m <;> simp_all [Lab.na]

/-- **`cx` is proved against every `Iface`.** -/
theorem cx_proved : cx.Proved cxGoal := by
  intro M hM L
  by_cases hmov : M.unlock L (.lit cxM) = movCall
  · -- the unlock is the `mov`: after the first lock the state is inconsistent
    have hcode : M.unlockCode L = movUnlockCode 0 := by
      simp only [Iface.unlock, movCall, Stmt.seq.injEq] at hmov; exact hmov.2
    refine ⟨M.inv cxM hemp ∗ hemp, fun _ _ _ => False, cxOwn,
      Heap.union (M.init cxM) Heap.empty, ⟨fun t u h => cxOwn_disj h, cxOwn_disjI M hM,
        cxOwn_le M L, cxI_le M hM L,
        sep_emp (M.init_inv cxM hemp Heap.empty rfl (disjoint_empty_right _)), fun t ht => ?_⟩,
        fun _ _ _ _ q => absurd (q 0 (by decide)) id⟩
    have ht0 : t = 0 := by simpa [cx] using ht
    subst ht0
    have hts : (cx.link M L).ts 0 = (cxBad (M.lock L) (M.unlock L), Regs.zero) := by
      simp [Client.link, Client.startWith, cx, cxBody, hmov]
    rw [hts]
    have hown : cxOwn 0 = Heap.single cxO 0 := by simp [cxOwn]
    rw [hown]
    simp only [cxBad, Tv.chain]
    apply safe_seq
    apply safe_seq
    apply safe_assign
    have H := safe_frame (F := fun h => h = Heap.single cxO 0)
      (M.lock_spec cxM hemp hemp L _ (rdi_m Regs.zero)) (disjoint_empty _) rfl
    rw [union_empty_left] at H
    refine safe_conseq (fun rs h hp => ?_) H
    obtain ⟨h12, hF, d, rfl, hRL, rfl⟩ := sep_iff.mp hp
    have hno : ∀ hI, (M.inv cxM hemp ∗ hemp) hI → ¬ Heap.Disjoint (Heap.union h12
        (Heap.single cxO 0)) hI := fun hI iI dI => mov_no_inv M L hcode hRL hI iI (fun a => by
          rcases dI a with e | e
          · exact Or.inl (union_eq_none.mp e).1
          · exact Or.inr e)
    apply safe_seq
    apply safe_seq
    apply safe_assign
    rw [hcode]
    exact safe_dead hno (by decide)
  · -- otherwise the body is `skip`
    refine ⟨fun h => h = Heap.empty, fun t _ h => h = cxOwn t, cxOwn, Heap.empty,
      ⟨fun t u h => cxOwn_disj h, fun _ => disjoint_empty_right _, cxOwn_le M L,
        fun _ _ e => by simp [Heap.empty] at e, rfl, fun t ht => ?_⟩, ?_⟩
    · have ht0 : t = 0 := by simpa [cx] using ht
      subst ht0
      have hts : (cx.link M L).ts 0 = (.skip, Regs.zero) := by
        simp [Client.link, Client.startWith, cx, cxBody, hmov]
      rw [hts]
      exact safe_skip rfl
    · intro rs mem hs' hI' q _ hle _
      have := q 0 (by decide)
      exact hle 0 cxO 0 (by rw [this]; simp [cxOwn, single_apply])

/-! ## The real `mov` unlock breaks `cx` -/

/-- `cx`'s misbehaving thread with the real holes, loop bound 2. -/
def cxC : CSt :=
  start [(cxBad (Inst.call (Prim.SpinLock.cert.body Inst.L)) (Inst.call (movUnlockCode Inst.L)),
    Regs.zero)] [(cxO, 0), (cxM, 0), (Spin.tok cxM, 0)]

theorem cx_check : (tsoStates 1 Prim.Clients.fuel cxC).any
    (fun c => c.doneB 1 && c.drainedB && (memOf c.mem cxO == some 1)) = true := by
  decide +kernel

theorem cxC_cfg : cxC.cfg = cx.startWith (Inst.call (Prim.SpinLock.cert.body Inst.L))
    (Inst.call (movUnlockCode Inst.L))
    (cx.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty) := by
  have hm : Inst.call (movUnlockCode Inst.L) (.lit cxM) = movCall := rfl
  simp only [CSt.cfg, Client.startWith]
  congr 1
  · funext t
    rcases t with _ | t
    · simp [CSt.th, cxC, start, rget_rlist, cx, cxBody, hm]
    · simp [CSt.th, cxC, start, cx]
  · funext a
    by_cases hS : a = 0x300 ∨ a = 0x100 ∨ a = 0x104
    · rcases hS with rfl | rfl | rfl <;> rfl
    · simp only [not_or] at hS
      obtain ⟨h1, h2, h3⟩ := hS
      simp [cxC, start, cx, memOf_cons, memOf_nil, Spin.init, Spin.tok, union_apply, single_apply,
        Heap.empty, Even.out, Even.m, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem cx_run : ∃ Cf : OCfg, OReach .tso cx.N (cx.startWith
      (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body Inst.L))
      (fun a => .seq (.assign .rdi a) (movUnlockCode Inst.L))
      (cx.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty)).toO Cf ∧
    Cf.Drained ∧ (∀ t < cx.N, (Cf.ts t).1 = .skip) ∧ Cf.mem cxO = some 1 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 1) (c0 := cxC) rfl rfl cx_check
  rw [cxC_cfg] at hr
  refine ⟨d.ocfg, hr, hd, hf, ?_⟩
  simpa [CSt.ocfg] using hp

/-- **The statement of `Task.movUnlock` is false.** -/
theorem movUnlockIface_false : ¬ movUnlockIface := by
  intro H
  obtain ⟨Cf, hr, hd, hf, hm⟩ := cx_run
  have := H cx cxGoal cx_proved (Nat.le_refl 8) Inst.L Cf hr hd hf
  simp only [cxGoal, hm] at this
  cases this

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
