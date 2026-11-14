module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.RelCex
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Defs

/-!
# Proofs: the statement of `Task.ticketIface` is false

`ticketIfaceFirst_false : ¬ Futex.ticketIfaceFirst`. As `movUnlockIface_false`, the counterexample
is one client, `tx`, with one thread and one mutex at `0x100`, whose body tests its unlock hole:

* if the hole is not `ticket_unlock`, the body is `skip`, and the goal (`[0x300] = 0`, the
  client's own cell) holds;
* if it is, the body is `lock; unlock; [0x300] := 1`.

`tx` is proved against every `Iface` (`tx_proved`). In the second case `tk_no_unlock` shows,
from the `Iface`'s own `unlock_spec`, that in every invariant state disjoint from a token heap
the `serving` cell `l + 4` holds a value of `2 ^ 32` or more: if it held a 32-bit value `v`, the
unlock's load of `v` would be a real step, the logic would then force the holder to own
`l + 4` (the `mov` that follows writes it and is not draining), and the holder could never give
it up, contradicting the unlock's postcondition `emp`. So after the first `lock` the unlock's
first load reads no 32-bit value consistently with any invariant state, and the rest of the
body is vacuously safe (`safe_dead_ld`). Linked with the real ticket lock, the thread finishes
with `[0x300] = 1` (`tx_run`, by the explorer on the single-thread start).

The restated Task (over `ProvedG`) excludes `tx`: `tx` is not proved against `ticketMutexG`, where
its lock returns and its unlock is a real release.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Robust

/-! ## Every `Iface` with the ticket unlock is inconsistent once locked -/

theorem tunl_eq : Prim.TicketUnlock.cert.body 0 =
    .seq Prim.TicketUnlock.ld (.seq Prim.TicketUnlock.inc (.seq Prim.TicketUnlock.st .skip)) := rfl

/-- **With `ticket_unlock` as unlock code**, every invariant state disjoint from a token heap
puts a value of at least `2 ^ 32` in `serving`. -/
theorem tk_no_unlock (M : Iface) (L : Nat)
    (hcode : M.unlockCode L = Prim.TicketUnlock.cert.body 0) {hk : Heap}
    (hh : (hemp ∗ M.locked cxM) hk) :
    ∀ hI, (M.inv cxM hemp ∗ hemp) hI → Heap.Disjoint hk hI →
      ∃ v0, Heap.union hk hI (cxM + 4) = some v0 ∧ 2 ^ 32 ≤ v0 := by
  intro hI iI dI
  let rs : Regs := Regs.zero.set .rdi (BitVec.ofNat 64 cxM)
  have hrs : (rs .rdi).toNat = cxM := by simp [rs, Regs.set, Even.m]
  have S := M.unlock_spec cxM hemp hemp L rs hk hrs hh
  rw [hcode, tunl_eq] at S
  obtain ⟨Rr, hR, post⟩ := S
  have F := post _ _ _ hR
  have e4 : ∀ rs' : Regs, rs' .rdi = rs .rdi → ((Prim.at_ .rdi 4).eval rs').toNat = cxM + 4 := by
    intro rs' e; simp [Prim.at_, Expr.eval, BinOp.eval, e, rs, Regs.set, Even.m]
  have st0 : ∀ v, v < 2 ^ (8 * 4) → TStep (.seq Prim.TicketUnlock.ld
      (.seq Prim.TicketUnlock.inc (.seq Prim.TicketUnlock.st .skip))) rs
      (some (.rd .rlx .wb (cxM + 4) 4 v))
      (.seq .skip (.seq Prim.TicketUnlock.inc (.seq Prim.TicketUnlock.st .skip)))
      (rs.set .rax (BitVec.ofNat 64 v)) := fun v hv => by
    have := TStep.seq (t := .seq Prim.TicketUnlock.inc (.seq Prim.TicketUnlock.st .skip))
      (TStep.load (d := .rax) (m := .rlx) (sz := 4) (fl := .wb) (a := Prim.at_ .rdi 4)
        (rs := rs) hv)
    rw [e4 rs rfl] at this; exact this
  obtain ⟨-, -, hat⟩ := F.2.2 _ _ _ (st0 0 (by decide))
  obtain ⟨htouch, -, -⟩ := hat rfl hI iI dI
  have hsome := htouch (cxM + 4) (Or.inl ⟨0, by simp [Lab.reads]⟩)
  obtain ⟨v0, hv0⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨v0, hv0, ?_⟩
  by_contra hlt
  have hlt' : v0 < 2 ^ (8 * 4) := by omega
  obtain ⟨-, -, hat⟩ := F.2.2 _ _ _ (st0 v0 hlt')
  obtain ⟨-, -, hex⟩ := hat rfl hI iI dI
  obtain ⟨h', hI', d', -, iI', hK, -⟩ := hex (fun p hp => by
    simp only [Lab.reads, List.mem_singleton] at hp; subst hp; exact hv0)
  have F2 := post _ _ _ hK
  have F3 := post _ _ _ (F2.2.1 _ _ TStep.seqSkip)
  have F4 := post _ _ _ (F3.2.1 _ _ (TStep.seq TStep.assign))
  have F5 := post _ _ _ (F4.2.1 _ _ TStep.seqSkip)
  obtain ⟨-, -, hat5⟩ := F5.2.2 _ _ _ (TStep.seq TStep.store)
  obtain ⟨-, hw, hex5⟩ := hat5 rfl hI' iI' d'
  have hk4 : (h' (cxM + 4)).isSome := by
    have := hw rfl ((Prim.at_ .rdi 4).eval ((rs.set .rax (BitVec.ofNat 64 v0)).set .rax
      ((Prim.op32 .add .rax (.lit 1)).eval (rs.set .rax (BitVec.ofNat 64 v0))))).toNat
      (by simp [Lab.wval])
    rwa [e4 _ (by simp [Regs.set])] at this
  obtain ⟨h'', -, -, -, -, hK5, sur5⟩ := hex5 (fun p hp => by simp [Lab.reads] at hp)
  have F6 := post _ _ _ hK5
  have F7 := post _ _ _ (F6.2.1 _ _ TStep.seqSkip)
  have he : h'' = Heap.empty := F7.1 rfl
  have := sur5 rfl _ hk4
  rw [he] at this; simp [Heap.empty] at this

/-- A 4-byte load whose cell holds no 32-bit value in any invariant state: vacuously safe. -/
theorem safe_dead_ld {I : HProp} {Q : Regs → HProp} {h : Heap} {d : Reg} {m : Mode}
    (hm : m ≠ .na) {fl : Flav} {a : Expr} {rs : Regs} {t : Stmt}
    (hno : ∀ hI, I hI → Heap.Disjoint h hI →
      ∃ v0, Heap.union h hI (a.eval rs).toNat = some v0 ∧ 2 ^ 32 ≤ v0) :
    Csl.Safe I Q (.seq (.load d m 4 fl a) t) rs h := by
  apply safe_seq
  refine safe_atomic (by intro e; cases e) (fun s' rs' st => by cases st) ?_
  intro l s' rs' st
  cases st with
  | load hv =>
    rename_i v
    refine ⟨rfl, rfl, fun e => ?_, fun _ hI iI dI => ?_⟩
    · cases m <;> simp_all [Lab.na]
    · obtain ⟨v0, hv0, hge⟩ := hno hI iI dI
      refine ⟨fun x hx => ?_, fun _ x hx => by simp [Lab.wval] at hx, fun hok => ?_⟩
      · simp only [Lab.Touches, Lab.reads, Lab.wval, List.mem_singleton, Prod.mk.injEq,
          Option.isSome_none, Bool.false_eq_true, or_false] at hx
        obtain ⟨_, rfl, -⟩ := hx
        rw [hv0]; rfl
      · have := hok _ (List.mem_singleton_self _)
        rw [hv0] at this
        injection this with e
        omega

/-! ## The client -/

/-- The ticket unlock, called on the mutex. -/
def tkCall : Stmt := .seq (.assign .rdi (.lit cxM)) (Prim.TicketUnlock.cert.body 0)

/-- The misbehaving body: lock, unlock, `[0x300] := 1`. -/
def txBad (lk ul : Expr → Stmt) : Stmt :=
  Tv.chain [lk (.lit cxM), ul (.lit cxM), .store .na 8 .wb (.lit cxO) (.lit 1)]

open Classical in
/-- **The body**: misbehave exactly when the unlock hole is the ticket unlock. -/
noncomputable def txBody (lk ul : Expr → Stmt) (_t : Nat) : Stmt :=
  if ul (.lit cxM) = tkCall then txBad lk ul else .skip

/-- **The client**: one thread, the cell `0x300 ↦ 0`, one mutex at `0x100`, an 8-byte slot. -/
noncomputable def tx : Client := ⟨1, txBody, Heap.single cxO 0, [cxM], 8⟩

/-- **`tx` is proved against every `Iface`.** -/
theorem tx_proved : tx.Proved cxGoal := by
  intro M hM L
  by_cases htk : M.unlock L (.lit cxM) = tkCall
  · have hcode : M.unlockCode L = Prim.TicketUnlock.cert.body 0 := by
      simp only [Iface.unlock, tkCall, Stmt.seq.injEq] at htk; exact htk.2
    refine ⟨M.inv cxM hemp ∗ hemp, fun _ _ _ => False, cxOwn,
      Heap.union (M.init cxM) Heap.empty, ⟨fun t u h => cxOwn_disj h, cxOwn_disjI M hM,
        cxOwn_le M L, cxI_le M hM L,
        sep_emp (M.init_inv cxM hemp Heap.empty rfl (disjoint_empty_right _)), fun t ht => ?_⟩,
        fun _ _ _ _ q => absurd (q 0 (by decide)) id⟩
    have ht0 : t = 0 := by simpa [tx] using ht
    subst ht0
    have hts : (tx.link M L).ts 0 = (txBad (M.lock L) (M.unlock L), Regs.zero) := by
      simp [Client.link, Client.startWith, tx, txBody, htk]
    rw [hts]
    have hown : cxOwn 0 = Heap.single cxO 0 := by simp [cxOwn]
    rw [hown]
    simp only [txBad, Tv.chain]
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
    rw [hcode, tunl_eq]
    refine safe_dead_ld (m := .rlx) (by decide) (fun hI iI dI => ?_)
    have dI' : Heap.Disjoint h12 hI := fun a => by
      rcases dI a with e | e
      · exact Or.inl (union_eq_none.mp e).1
      · exact Or.inr e
    obtain ⟨v0, hv0, hge⟩ := tk_no_unlock M L hcode hRL hI iI dI'
    have ea : ((Prim.at_ .rdi 4).eval (rs.set .rdi ((Expr.lit cxM).eval rs))).toNat = cxM + 4 := by
      simp [Prim.at_, Expr.eval, BinOp.eval, Regs.set, Even.m]
    refine ⟨v0, ?_, hge⟩
    rw [ea, ← hv0]
    have hne : cxM + 4 ≠ cxO := by simp [Even.m, Even.out]
    simp only [union_apply, single_apply, hne, ite_false]
    cases h12 (cxM + 4) <;> rfl
  · refine ⟨fun h => h = Heap.empty, fun t _ h => h = cxOwn t, cxOwn, Heap.empty,
      ⟨fun t u h => cxOwn_disj h, fun _ => disjoint_empty_right _, cxOwn_le M L,
        fun _ _ e => by simp [Heap.empty] at e, rfl, fun t ht => ?_⟩, ?_⟩
    · have ht0 : t = 0 := by simpa [tx] using ht
      subst ht0
      have hts : (tx.link M L).ts 0 = (.skip, Regs.zero) := by
        simp [Client.link, Client.startWith, tx, txBody, htk]
      rw [hts]
      exact safe_skip rfl
    · intro rs mem hs' hI' q _ hle _
      have := q 0 (by decide)
      exact hle 0 cxO 0 (by rw [this]; simp [cxOwn, single_apply])

/-! ## The real ticket lock breaks `tx` -/

/-- `tx`'s misbehaving thread with the real holes, loop bound 2. -/
def txC : CSt :=
  start [(txBad (Inst.call (Prim.TicketLock.cert.body Inst.L))
    (Inst.call (Prim.TicketUnlock.cert.body Inst.L)), Regs.zero)]
    [(cxO, 0), (cxM, 0), (cxM + 4, 0)]

theorem tx_check : (tsoStates 1 Prim.Clients.fuel txC).any
    (fun c => c.doneB 1 && c.drainedB && (memOf c.mem cxO == some 1)) = true := by
  decide +kernel

theorem txC_cfg : txC.cfg = tx.startWith (Inst.call (Prim.TicketLock.cert.body Inst.L))
    (Inst.call (Prim.TicketUnlock.cert.body Inst.L))
    (tx.locks.foldr (fun l h => Heap.union (Futex.ticketInit l) h) Heap.empty) := by
  have hm : Inst.call (Prim.TicketUnlock.cert.body Inst.L) (.lit cxM) = tkCall := rfl
  simp only [CSt.cfg, Client.startWith]
  congr 1
  · funext t
    rcases t with _ | t
    · simp [CSt.th, txC, start, rget_rlist, tx, txBody, hm]
    · simp [CSt.th, txC, start, tx]
  · funext a
    by_cases hS : a = 0x300 ∨ a = 0x100 ∨ a = 0x104
    · rcases hS with rfl | rfl | rfl <;> rfl
    · simp only [not_or] at hS
      obtain ⟨h1, h2, h3⟩ := hS
      simp [txC, start, tx, memOf_cons, memOf_nil, Futex.ticketInit, union_apply, single_apply,
        Heap.empty, Even.out, Even.m, Ne.symm h1, Ne.symm h2, Ne.symm h3, h1, h2, h3]

theorem tx_run : ∃ Cf : OCfg, OReach .tso tx.N (tx.startWith
      (fun a => .seq (.assign .rdi a) (Prim.TicketLock.cert.body Inst.L))
      (fun a => .seq (.assign .rdi a) (Prim.TicketUnlock.cert.body Inst.L))
      (tx.locks.foldr (fun l h => Heap.union (Futex.ticketInit l) h) Heap.empty)).toO Cf ∧
    Cf.Drained ∧ (∀ t < tx.N, (Cf.ts t).1 = .skip) ∧ Cf.mem cxO = some 1 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 1) (c0 := txC) rfl rfl tx_check
  rw [txC_cfg] at hr
  refine ⟨d.ocfg, hr, hd, hf, ?_⟩
  simpa [CSt.ocfg] using hp

/-- **The statement of `Task.ticketIface` is false.** -/
theorem ticketIfaceFirst_false : ¬ Futex.ticketIfaceFirst := by
  intro H
  obtain ⟨Cf, hr, hd, hf, hm⟩ := tx_run
  have := H tx cxGoal tx_proved (Nat.le_refl 8) Inst.L Cf hr hd hf
  simp only [cxGoal, hm] at this
  cases this

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
