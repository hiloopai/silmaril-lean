module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.TicketCex
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.FutexRel

/-!
# Proofs: the earlier statement of `Task.decUnlock` is false

`decUnlockIface_false : ¬ Futex.decUnlockIface`. As for `movUnlockIface_false` and
`ticketIfaceFirst_false`, the counterexample is one client, `dx`, with one thread and one mutex at
`0x100`, whose body tests its holes:

* if the lock hole is not `fmutex_lock` (at some loop bound) or the unlock hole is not
  `fmutex_unlock_dec`, the body is `skip`, and the goal (`[0x300] = 0`, the client's own cell)
  holds;
* otherwise the body is `lock; unlock; [0x300] := 1`.

`dx` is proved against every base-CSL `Iface` (`dx_proved`). In the second case the
`Iface`'s lock and unlock codes are Drepper's, and the `Iface`'s own specs exclude every invariant
state with a 32-bit lock word that is disjoint from a token heap:

1. `dl_inv_has`: the lock's first locked access (`cas`) reads the word in every invariant state,
   so every invariant state maps the word;
2. `dl_not_held`: a word `v ≠ 1` makes the `lock sub` a real step on the contended path. Its
   re-split leaves the word in the invariant (step 1), and the `mov` of `0` that follows is a
   non-draining write, which the base CSL allows only to an owned
   cell: contradiction. (The futex wake that follows the `mov` drains and could hand ownership
   back, but the `mov` comes first.)
3. `dl_one_two`: a word `1` lets another thread's lock run its `cas` (fails, writes `1`) and its
   `xchg 2` from an empty heap; the re-split gives an invariant state with word `2`, inside the
   old one's cells, so still disjoint from the token heap. Step 2 excludes it.

So after the first `lock` the unlock's `lock sub` reads no 32-bit value consistently with any
invariant state (`dl_dead`), and the rest of the body is vacuously safe (`safe_dead_rmw`).
Linked with the real futex lock and the dec unlock, the single thread takes the fast paths
(`cas 0 → 1`, then `lock sub` from `1` to `0`) and finishes with `[0x300] = 1` (`dx_run`, by the
explorer on the single-thread start).

The futex wake does drain, so in the base CSL a thread *could* hand the word back at the wake.
That does not save the statement: the base CSL rule for the non-draining `mov` already needs the
word owned, and no base-CSL invariant can let a thread own the word while other threads' locks
read it (step 1). The
restated Task (over `ProvedR`, `decUnlock_holds`) excludes `dx`: `dx_not_provedR`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Futex
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Prim (at_ zCmpI zTest)
open Silmaril.X86.Concurrency.Cir.TvCfg (notE)
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (casZ subZ)

/-! ## Every base-CSL `Iface` with Drepper's codes is inconsistent once locked -/

/-- The registers of a call on the mutex. -/
def dlRs : Regs := Regs.zero.set .rdi (BitVec.ofNat 64 cxM)

theorem dlRs_rdi : (dlRs .rdi).toNat = cxM := by simp [dlRs, Regs.set, Even.m]

theorem dl_at0' (rs : Regs) : ((at_ .rdi 0).eval rs).toNat = (rs .rdi).toNat := by
  simp [at_, Expr.eval, BinOp.eval]

theorem dl_at0 {rs : Regs} (h : rs .rdi = dlRs .rdi) : ((at_ .rdi 0).eval rs).toNat = cxM := by
  simp [at_, Expr.eval, BinOp.eval, h, dlRs, Regs.set, Even.m]

/-- **Step 1**: with `fmutex_lock` as lock code, every invariant state maps the lock word. -/
theorem dl_inv_has (M : Iface) {L L' : Nat} (hlk : M.lockCode L = Lock.cert.body L')
    {hI : Heap} (iI : (M.inv cxM hemp ∗ hemp) hI) : ∃ v, hI cxM = some v := by
  have S := M.lock_spec cxM hemp hemp L dlRs dlRs_rdi
  rw [hlk, fm_lock_body] at S
  obtain ⟨Rr, hR, post⟩ := S
  have F0 := post _ _ _ hR
  have F1 := post _ _ _ (F0.2.1 _ _ (TStep.seq TStep.assign))
  have F2 := post _ _ _ (F1.2.1 _ _ TStep.seqSkip)
  have F3 := post _ _ _ (F2.2.1 _ _ (TStep.seq TStep.assign))
  have F4 := post _ _ _ (F3.2.1 _ _ TStep.seqSkip)
  obtain ⟨-, -, hat⟩ := F4.2.2 _ _ _ (TStep.seq (TStep.rmw (old := 0) (by decide)))
  obtain ⟨ht, -, -⟩ := hat rfl hI iI (disjoint_empty _)
  have := ht _ (Or.inl ⟨0, List.mem_singleton_self _⟩)
  rw [dl_at0 (by simp [Regs.set]), union_empty_left] at this
  exact Option.isSome_iff_exists.mp this

/-- **Step 2**: with Drepper's codes, no invariant state disjoint from a token heap has a 32-bit
lock word other than `1`. -/
theorem dl_not_held (M : Iface) {L L' : Nat} (hlk : M.lockCode L = Lock.cert.body L')
    (hcode : M.unlockCode L = UnlockDec.cert.body 0) {hk : Heap}
    (hh : (hemp ∗ M.locked cxM) hk) {hI : Heap} (iI : (M.inv cxM hemp ∗ hemp) hI)
    (dI : Heap.Disjoint hk hI) {v : Nat} (hv : hI cxM = some v) (hv32 : v < 2 ^ 32)
    (hv1 : v ≠ 1) : False := by
  have S := M.unlock_spec cxM hemp hemp L dlRs hk dlRs_rdi hh
  rw [hcode, dec_body] at S
  obtain ⟨Rr, hR, post⟩ := S
  have F0 := post _ _ _ hR
  have hkn : hk cxM = none := by
    rcases dI cxM with e | e
    · exact e
    · rw [hv] at e; cases e
  obtain ⟨-, -, hat⟩ := F0.2.2 _ _ _ (TStep.seq (TStep.rmw (old := v) (by omega)))
  obtain ⟨-, -, hex⟩ := hat rfl hI iI dI
  obtain ⟨h', hI', d', -, iI', hK, -⟩ := hex (fun p hp => by
    simp only [Lab.reads, List.mem_singleton] at hp
    subst hp
    rw [dl_at0 rfl, union_none hkn, hv])
  have F1 := post _ _ _ hK
  have F2 := post _ _ _ (F1.2.1 _ _ TStep.seqSkip)
  have F3 := post _ _ _ (F2.2.1 _ _ (TStep.seq (TStep.iteT (by
    rw [truthy_subZ1 hv32 (by simp [Regs.set])]; simpa using hv1))))
  have F4 := post _ _ _ (F3.2.1 _ _ (TStep.seq (TStep.seq TStep.assign)))
  have F5 := post _ _ _ (F4.2.1 _ _ (TStep.seq TStep.seqSkip))
  have F6 := post _ _ _ (F5.2.1 _ _ (TStep.seq (TStep.seq TStep.assign)))
  have F7 := post _ _ _ (F6.2.1 _ _ (TStep.seq TStep.seqSkip))
  have F8 := post _ _ _ (F7.2.1 _ _ (TStep.seq (TStep.seq TStep.assign)))
  have F9 := post _ _ _ (F8.2.1 _ _ (TStep.seq TStep.seqSkip))
  obtain ⟨-, -, hat2⟩ := F9.2.2 _ _ _ (TStep.seq (TStep.seq TStep.store))
  obtain ⟨-, hw, -⟩ := hat2 rfl hI' iI' d'
  have hk' : (h' cxM).isSome := by
    have q := hw rfl cxM
    simpa [Lab.wval, dl_at0', Regs.set, dlRs_rdi] using q
  obtain ⟨w, hw'⟩ := dl_inv_has M hlk iI'
  rcases d' cxM with e | e
  · rw [e] at hk'; cases hk'
  · rw [hw'] at e; cases e

/-- **Step 3**: with `fmutex_lock` as lock code, an invariant state with lock word `1` leads (by
another thread's failed `cas` and its `xchg 2`) to one with word `2` inside the same cells. -/
theorem dl_one_two (M : Iface) {L L' : Nat} (hlk : M.lockCode L = Lock.cert.body L')
    {hI : Heap} (iI : (M.inv cxM hemp ∗ hemp) hI) (h1 : hI cxM = some 1) :
    ∃ hI2, (M.inv cxM hemp ∗ hemp) hI2 ∧ hI2 cxM = some 2 ∧ ∀ a, hI a = none → hI2 a = none := by
  have S := M.lock_spec cxM hemp hemp L dlRs dlRs_rdi
  rw [hlk, fm_lock_body] at S
  obtain ⟨Rr, hR, post⟩ := S
  have F0 := post _ _ _ hR
  have F1 := post _ _ _ (F0.2.1 _ _ (TStep.seq TStep.assign))
  have F2 := post _ _ _ (F1.2.1 _ _ TStep.seqSkip)
  have F3 := post _ _ _ (F2.2.1 _ _ (TStep.seq TStep.assign))
  have F4 := post _ _ _ (F3.2.1 _ _ TStep.seqSkip)
  obtain ⟨-, -, hat⟩ := F4.2.2 _ _ _ (TStep.seq (TStep.rmw (old := 1) (by decide)))
  obtain ⟨-, -, hex⟩ := hat rfl hI iI (disjoint_empty _)
  obtain ⟨h1', hI1, d1, e1, iI1, hK1, -⟩ := hex (fun p hp => by
    simp only [Lab.reads, List.mem_singleton] at hp
    subst hp
    rw [dl_at0 (by simp [Regs.set]), union_empty_left, h1])
  have hn1 : h1' cxM = none := by
    obtain ⟨w, hw⟩ := dl_inv_has M hlk iI1
    rcases d1 cxM with e | e
    · exact e
    · rw [hw] at e; cases e
  have hI1v : hI1 cxM = some 1 := by
    have := congrFun e1 cxM
    rw [union_none hn1] at this
    rw [this]
    simp [Lab.updH, Lab.wval, dl_at0', dlRs_rdi, RmwOp.result, Expr.eval, Regs.set, Prim.op32,
      TvCfg.mask32, BinOp.eval]
  have F5 := post _ _ _ hK1
  have F6 := post _ _ _ (F5.2.1 _ _ TStep.seqSkip)
  have F7 := post _ _ _ (F6.2.1 _ _ (TStep.seq (TStep.iteT (by
    rw [truthy_casZ0 (old := 1) (by decide) (by simp [Regs.set])]; decide))))
  have F8 := post _ _ _ (F7.2.1 _ _ (TStep.seq (TStep.seq (TStep.iteF (by
    rw [truthy_zCmp2 (old := 1) (by decide) (by simp [Regs.set])]; decide)))))
  have F9 := post _ _ _ (F8.2.1 _ _ (TStep.seq (TStep.seq (TStep.seq TStep.assign))))
  have F10 := post _ _ _ (F9.2.1 _ _ (TStep.seq (TStep.seq TStep.seqSkip)))
  obtain ⟨-, -, hat2⟩ := F10.2.2 _ _ _
    (TStep.seq (TStep.seq (TStep.seq (TStep.rmw (old := 1) (by decide)))))
  obtain ⟨-, -, hex2⟩ := hat2 rfl hI1 iI1 d1
  obtain ⟨h2, hI2, d2, e2, iI2, -, -⟩ := hex2 (fun p hp => by
    simp only [Lab.reads, List.mem_singleton] at hp
    subst hp
    rw [dl_at0 (by simp [Regs.set]), union_none hn1, hI1v])
  obtain ⟨w2, hw2⟩ := dl_inv_has M hlk iI2
  have hn2 : h2 cxM = none := by
    rcases d2 cxM with e | e
    · exact e
    · rw [hw2] at e; cases e
  refine ⟨hI2, iI2, ?_, fun a ha => ?_⟩
  · have := congrFun e2 cxM
    rw [union_none hn2] at this
    rw [this]
    simp [Lab.updH, Lab.wval, dl_at0', dlRs_rdi, RmwOp.result, Expr.eval, Regs.set]
  · have hac : a ≠ cxM := fun e => by subst e; rw [h1] at ha; cases ha
    have q1 := congrFun e1 a
    have q2 := congrFun e2 a
    simp only [Lab.updH, Lab.wval, dl_at0', Regs.set, dlRs_rdi, reduceCtorEq, ite_false,
      Ne.symm hac, Option.none_or, union_empty_left, ha] at q1 q2
    rw [q1] at q2
    exact (union_eq_none.mp q2).2

/-- **With Drepper's codes**, every invariant state disjoint from a token heap puts a value of at
least `2 ^ 32` in the lock word. -/
theorem dl_dead (M : Iface) {L L' : Nat} (hlk : M.lockCode L = Lock.cert.body L')
    (hcode : M.unlockCode L = UnlockDec.cert.body 0) {hk : Heap}
    (hh : (hemp ∗ M.locked cxM) hk) :
    ∀ hI, (M.inv cxM hemp ∗ hemp) hI → Heap.Disjoint hk hI →
      ∃ v0, Heap.union hk hI cxM = some v0 ∧ 2 ^ 32 ≤ v0 := by
  intro hI iI dI
  obtain ⟨v0, hv0⟩ := dl_inv_has M hlk iI
  have hkn : hk cxM = none := by
    rcases dI cxM with e | e
    · exact e
    · rw [hv0] at e; cases e
  refine ⟨v0, by rw [union_none hkn, hv0], ?_⟩
  by_contra hlt
  have hv32 : v0 < 2 ^ 32 := by omega
  by_cases h1 : v0 = 1
  · subst h1
    obtain ⟨hI2, iI2, h2, hsub⟩ := dl_one_two M hlk iI hv0
    exact dl_not_held M hlk hcode hh iI2 (fun a => by
      rcases dI a with e | e
      · exact Or.inl e
      · exact Or.inr (hsub a e)) h2 (by decide) (by decide)
  · exact dl_not_held M hlk hcode hh iI dI hv0 hv32 h1

/-- A 4-byte locked read-modify-write whose cell holds no 32-bit value in any invariant state:
vacuously safe. -/
theorem safe_dead_rmw {I : HProp} {Q : Regs → HProp} {h : Heap} {d : Reg} {m : Mode}
    {op : RmwOp} {a arg : Expr} {rs : Regs} {t : Stmt}
    (hno : ∀ hI, I hI → Heap.Disjoint h hI →
      ∃ v0, Heap.union h hI (a.eval rs).toNat = some v0 ∧ 2 ^ 32 ≤ v0) :
    Csl.Safe I Q (.seq (.rmw d m 4 op a arg) t) rs h := by
  apply safe_seq
  refine safe_atomic (by intro e; cases e) (fun s' rs' st => by cases st) ?_
  intro l s' rs' st
  cases st with
  | rmw hv =>
    rename_i old
    refine ⟨rfl, rfl, fun e => by simp [Lab.na] at e, fun _ hI iI dI => ?_⟩
    obtain ⟨v0, hv0, hge⟩ := hno hI iI dI
    refine ⟨fun x hx => ?_, fun e => by simp [Lab.drains] at e, fun hok => ?_⟩
    · have hx' : x = (a.eval rs).toNat := by
        rcases hx with ⟨w, hw⟩ | hw
        · simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hw
          exact hw.1
        · simp only [Lab.wval] at hw
          split at hw
          · rename_i e; exact e.symm
          · cases hw
      rw [hx', hv0]; rfl
    · have := hok _ (List.mem_singleton_self _)
      rw [hv0] at this
      injection this with e
      omega

/-! ## The client -/

/-- Drepper's lock (loop bound `L`), called on the mutex. -/
def dlLockCall (L : Nat) : Stmt := .seq (.assign .rdi (.lit cxM)) (Lock.cert.body L)

/-- Drepper's original unlock, called on the mutex. -/
def decCall : Stmt := .seq (.assign .rdi (.lit cxM)) (UnlockDec.cert.body 0)

/-- The misbehaving body: lock, unlock, `[0x300] := 1`. -/
def dxBad (lk ul : Expr → Stmt) : Stmt :=
  Tv.chain [lk (.lit cxM), ul (.lit cxM), .store .na 8 .wb (.lit cxO) (.lit 1)]

open Classical in
/-- **The body**: misbehave exactly when the holes are Drepper's lock and original unlock. -/
noncomputable def dxBody (lk ul : Expr → Stmt) (_t : Nat) : Stmt :=
  if (∃ L, lk (.lit cxM) = dlLockCall L) ∧ ul (.lit cxM) = decCall then dxBad lk ul else .skip

/-- **The client**: one thread, the cell `0x300 ↦ 0`, one mutex at `0x100`, an 8-byte slot. -/
noncomputable def dx : Client := ⟨1, dxBody, Heap.single cxO 0, [cxM], 8⟩

/-- **`dx` is proved against every base-CSL `Iface`.** -/
theorem dx_proved : dx.Proved cxGoal := by
  intro M hM L
  by_cases hdr : (∃ L', M.lock L (.lit cxM) = dlLockCall L') ∧ M.unlock L (.lit cxM) = decCall
  · obtain ⟨⟨L', hL'⟩, hdc⟩ := hdr
    have hlk : M.lockCode L = Lock.cert.body L' := by
      simp only [Iface.lock, dlLockCall, Stmt.seq.injEq] at hL'; exact hL'.2
    have hcode : M.unlockCode L = UnlockDec.cert.body 0 := by
      simp only [Iface.unlock, decCall, Stmt.seq.injEq] at hdc; exact hdc.2
    refine ⟨M.inv cxM hemp ∗ hemp, fun _ _ _ => False, cxOwn,
      Heap.union (M.init cxM) Heap.empty, ⟨fun t u h => cxOwn_disj h, cxOwn_disjI M hM,
        cxOwn_le M L, cxI_le M hM L,
        sep_emp (M.init_inv cxM hemp Heap.empty rfl (disjoint_empty_right _)), fun t ht => ?_⟩,
        fun _ _ _ _ q => absurd (q 0 (by decide)) id⟩
    have ht0 : t = 0 := by simpa [dx] using ht
    subst ht0
    have hts : (dx.link M L).ts 0 = (dxBad (M.lock L) (M.unlock L), Regs.zero) := by
      simp [Client.link, Client.startWith, dx, dxBody, hdc, hL']
    rw [hts]
    have hown : cxOwn 0 = Heap.single cxO 0 := by simp [cxOwn]
    rw [hown]
    simp only [dxBad, Tv.chain]
    apply safe_seq
    apply safe_seq
    apply safe_assign
    have H := safe_frame (F := fun h => h = Heap.single cxO 0)
      (M.lock_spec cxM hemp hemp L _ (rdi_m Regs.zero)) (disjoint_empty _) rfl
    rw [union_empty_left] at H
    refine safe_conseq (fun rs h hp => ?_) H
    obtain ⟨h12, hF, d, rfl, hRL, rfl⟩ := sep_iff.mp hp
    apply safe_seq
    apply safe_seq
    apply safe_assign
    rw [hcode, dec_body]
    refine safe_dead_rmw (fun hI iI dI => ?_)
    have dI' : Heap.Disjoint h12 hI := fun a => by
      rcases dI a with e | e
      · exact Or.inl (union_eq_none.mp e).1
      · exact Or.inr e
    obtain ⟨v0, hv0, hge⟩ := dl_dead M hlk hcode hRL hI iI dI'
    have ea : ((at_ .rdi 0).eval (rs.set .rdi ((Expr.lit cxM).eval rs))).toNat = cxM := by
      simp [at_, Expr.eval, BinOp.eval, Regs.set, Even.m]
    refine ⟨v0, ?_, hge⟩
    rw [ea, ← hv0]
    have hne : cxM ≠ cxO := by simp [Even.m, Even.out]
    simp only [union_apply, single_apply, hne, ite_false]
    cases h12 cxM <;> rfl
  · refine ⟨fun h => h = Heap.empty, fun t _ h => h = cxOwn t, cxOwn, Heap.empty,
      ⟨fun t u h => cxOwn_disj h, fun _ => disjoint_empty_right _, cxOwn_le M L,
        fun _ _ e => by simp [Heap.empty] at e, rfl, fun t ht => ?_⟩, ?_⟩
    · have ht0 : t = 0 := by simpa [dx] using ht
      subst ht0
      have hts : (dx.link M L).ts 0 = (.skip, Regs.zero) := by
        simp [Client.link, Client.startWith, dx, dxBody, hdr]
      rw [hts]
      exact safe_skip rfl
    · intro rs mem hs' hI' q _ hle _
      have := q 0 (by decide)
      exact hle 0 cxO 0 (by rw [this]; simp [cxOwn, single_apply])

/-! ## The real futex lock and dec unlock break `dx` -/

/-- `dx`'s misbehaving thread with the real holes, loop bound 2. -/
def dxC : CSt :=
  start [(dxBad (Inst.call (Lock.cert.body Inst.L)) (Inst.call (UnlockDec.cert.body Inst.L)),
    Regs.zero)] [(cxO, 0), (cxM, 0), (Spin.tok cxM, 0)]

theorem dx_check : (tsoStates 1 Prim.Clients.fuel dxC).any
    (fun c => c.doneB 1 && c.drainedB && (memOf c.mem cxO == some 1)) = true := by
  decide +kernel

theorem dxC_cfg : dxC.cfg = dx.startWith (Inst.call (Lock.cert.body Inst.L))
    (Inst.call (UnlockDec.cert.body Inst.L))
    (dx.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty) := by
  have hd : Inst.call (UnlockDec.cert.body Inst.L) (.lit cxM) = decCall := rfl
  have hl : ∃ L, Inst.call (Lock.cert.body Inst.L) (.lit cxM) = dlLockCall L := ⟨Inst.L, rfl⟩
  simp only [CSt.cfg, Client.startWith]
  congr 1
  · funext t
    rcases t with _ | t
    · simp [CSt.th, dxC, start, rget_rlist, dx, dxBody, hd, hl]
    · simp [CSt.th, dxC, start, dx]
  · funext a
    by_cases hS : a = 0x300 ∨ a = 0x100 ∨ a = 0x104
    · rcases hS with rfl | rfl | rfl <;> rfl
    · simp only [not_or] at hS
      obtain ⟨h1, h2, h3⟩ := hS
      simp [dxC, start, dx, memOf_cons, memOf_nil, Spin.init, Spin.tok, union_apply, single_apply,
        Heap.empty, Even.out, Even.m, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem dx_run : ∃ Cf : OCfg, OReach .tso dx.N (dx.startWith
      (fun a => .seq (.assign .rdi a) (Lock.cert.body Inst.L))
      (fun a => .seq (.assign .rdi a) (UnlockDec.cert.body Inst.L))
      (dx.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty)).toO Cf ∧
    Cf.Drained ∧ (∀ t < dx.N, (Cf.ts t).1 = .skip) ∧ Cf.mem cxO = some 1 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 1) (c0 := dxC) rfl rfl dx_check
  rw [dxC_cfg] at hr
  refine ⟨d.ocfg, hr, hd, hf, ?_⟩
  simpa [CSt.ocfg] using hp

/-- **The earlier statement of `Task.decUnlock` is false.** -/
theorem decUnlockIface_false : ¬ Futex.decUnlockIface := by
  intro H
  obtain ⟨Cf, hr, hd, hf, hm⟩ := dx_run
  have := H dx cxGoal dx_proved (Nat.le_refl 8) Inst.L Cf hr hd hf
  simp only [cxGoal, hm] at this
  cases this

/-- **The restatement excludes `dx`**: `dx` is not proved against the
release-store interface, since `Task.decUnlock` (over `ProvedR`, `decUnlock_holds`) would then
give its goal `[0x300] = 0` on the run `dx_run`, which ends with `[0x300] = 1`. So the
restatement is not met by the counterexample client. -/
theorem dx_not_provedR : ¬ dx.ProvedR cxGoal := by
  intro hR
  obtain ⟨Cf, hr, hd, hf, hm⟩ := dx_run
  have := decUnlock_holds dx cxGoal hR (Nat.le_refl 8) Inst.L Cf hr hd hf
  simp only [cxGoal, hm] at this
  cases this

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
