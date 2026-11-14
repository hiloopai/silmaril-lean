module

public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.FutexCsl
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.FutexRel
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.FutexChecks
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.TicketCex
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.DecCex

/-!
# Drepper's futex mutex behind `Mutex.Iface`: what is proved

All statements are PROVED with the standard
axioms. The x86 side enters only through the checker (`TvCfg.Fx.tvFx`) and its soundness
theorem, which assumes the futex system-call convention (`TvCfg.Fx.SysStep`).

* `tv_ok`, `refines`: the three pinned functions are their CIR programs. Every x86 run is a
  run of the CIR program, with the same memory actions and the registers equal outside `rax`,
  `rcx`, `r11`, for every loop bound at least the run's length.
* `tv_rejects_mutants`, `shapes`: the checker rejects three wrong certificates; the lock and the
  exchange unlock have the C11 shapes of a futex lock and unlock, and Drepper's original unlock
  (a release store) does not.
* `fmutex : Iface` (in `Proofs/…/Mutex/FutexCsl`, re-exported here): `fmutex_lock` and
  `fmutex_unlock` meet the interface. The futex wait is an atomic read of the invariant's lock
  word, and the wake touches nothing.
* `even_fmutex`, `even_fmutex_sc`: the `Even` client, proved once against the interface, gets
  its goal with the futex mutex on SC, TSO and XL, at every loop bound (`link_any_mutex`).
* `fm_one_finishes`: non-vacuity. One thread running `lock; unlock` on an unlocked mutex has a
  finished, drained TSO run that leaves the lock word `0`.

## Drepper's original unlock

* `fmutexR : IfaceR` (the mutex, through `IfaceR.ofIface`) and **`fmutexDec : IfaceR`**:
  `fmutex_lock` with `fmutex_unlock_dec`, whose `mov` of `0` is a release (`dec_release`).
* **`decUnlock_holds : Task.decUnlock`** (over `ProvedR`); `even_fmutexDec`:
  `Even` with it, on TSO, at every loop bound.
* **`decUnlockIface_false : ¬ decUnlockIface`**: the original statement over
  `Client.Proved` is false. A client that tests its holes for `fmutex_lock` and
  `fmutex_unlock_dec` is vacuously proved against every `Iface` (the lock's `cas` puts the word
  in every invariant state; the unlock's non-draining `mov` would then need it owned; and a word
  `1` leads by another lock's `xchg 2` to a word `2`), and writes its forbidden value when linked
  with the real codes (the explorer gives the run).

## The ticket lock

* **`ticketIfaceFirst_false : ¬ ticketIfaceFirst`**: the statement over `Client.Proved` is false
  (a client that tests its unlock hole for `ticket_unlock`; the explorer gives the bad run).
* **`ticketIface_holds : Task.ticketIface`** (restated over `ProvedG`, with `N < 2 ^ 32`), from
  `Mutex.ticketMutexG` and `Mutex.link_any_mutexG`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex.Futex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.TvCfg (TRun regsOf)
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx
open Silmaril.X86.Concurrency.Cir.Robust (CSt memOf)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-! ## Translation validation -/

/-- **The three certificates check against the pinned bytes.** -/
theorem tv_ok : ∀ p ∈ all, tvFx (Prim.thr p.2.1) p.2.2 = true := by
  intro p hp
  simp only [all, List.mem_cons, List.not_mem_nil, or_false] at hp
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  rcases hp with rfl | rfl | rfl
  · exact tv_fmLock
  · exact tv_fmUnlock
  · exact tv_fmUnlockDec

/-- **The binaries are their CIR programs**: every x86 run of each pinned function (futex calls
by the convention `SysStep`) is a run of its CIR program for every loop bound at least the run's
length, with the same memory actions, registers equal outside `rax`, `rcx`, `r11`, and a
finished CIR program when the function has returned. -/
theorem refines {name : String} {code : List (BitVec 8)} {c : FCert} (hp : (name, code, c) ∈ all)
    {t : Tv.XThread} (htc : t.code = code) {s0 s : Silmaril.X86.State} (h0 : s0.rip = t.base)
    {acc : List (List XAct)} (hr : FRun t s0 acc s) {L : Nat} (hL : acc.length ≤ L) :
    ∃ σ rs labs, TRun (c.body L) (regsOf s0) labs σ rs ∧ acc.flatten = labs.flatMap Lab.acts ∧
      (∀ r, r ∉ clob → regsOf s r = rs r) ∧ (Returned t s → σ = .skip) := by
  have h := tv_ok _ hp
  rw [tvFx_code (t' := t) (by simp [Prim.thr, htc])] at h
  exact tvFx_sound h h0 hr hL

/-- **The checker rejects wrong certificates**: a wake in place of the wait, the lock certificate
without known register values, and the exchange release claimed to be a plain store. -/
theorem tv_rejects_mutants :
    tvFx (Prim.thr Code.fmutexLock) Mutants.lockWake = false ∧
    tvFx (Prim.thr Code.fmutexLock) Mutants.lockNoKn = false ∧
    tvFx (Prim.thr Code.fmutexUnlock) Mutants.unlockStore = false :=
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  ⟨tv_fmLockWake, tv_fmLockNoKn, tv_fmUnlockStore⟩

/-- **The checker rejects mutated code**: eight one-byte mutants of the pinned functions
(wake op `128`, `mov` for `xchg`, compare with `1`, system call `203`, no `lock` prefix, wait
value `1`, `je` for `jne`, `lock sub 2`), each against the unchanged certificate. -/
theorem tv_rejects_code_mutants :
    tvFx (Prim.thr Mutants.unlockWaitOp) Unlock.cert = false ∧
    tvFx (Prim.thr Mutants.unlockMov) Unlock.cert = false ∧
    tvFx (Prim.thr Mutants.unlockCmp1) Unlock.cert = false ∧
    tvFx (Prim.thr Mutants.lockNr203) Lock.cert = false ∧
    tvFx (Prim.thr Mutants.lockNoLock) Lock.cert = false ∧
    tvFx (Prim.thr Mutants.lockVal1) Lock.cert = false ∧
    tvFx (Prim.thr Mutants.lockJe) Lock.cert = false ∧
    tvFx (Prim.thr Mutants.decSub2) UnlockDec.cert = false :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.tv_codeMutants

/-- **Non-vacuity of the x86 side**: a concrete x86 run of the pinned `fmutex_unlock`,
from its entry to its end, in which the `xchg` reads `2` and the run takes the futex wake
through `SysStep`. By `refines` it is a finished CIR run of `fmutex_unlock`'s program whose
actions end with the wake's. So `FRun` with `SysStep` is satisfiable on the real bytes, and
`refines` is not vacuous for runs that make futex calls. -/
theorem x86_unlock_wakes : FRun Wit.thread Wit.thread.init Wit.acts Wit.fin ∧
    Returned Wit.thread Wit.fin ∧
    ∃ σ rs labs, TRun (Unlock.cert.body 9) (regsOf Wit.thread.init) labs σ rs ∧ σ = .skip ∧
      ∃ pre, labs.flatMap Lab.acts = pre ++ (Lab.fwake 0x2000 1 0).acts := by
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  refine ⟨wit_run, wit_ret, ?_⟩
  have hp : ("fmutex_unlock", Code.fmutexUnlock, Unlock.cert) ∈ all := by simp [all]
  obtain ⟨σ, rs, labs, h1, h2, _, h4⟩ :=
    refines hp (t := Wit.thread) rfl rfl
      Silmaril.Proofs.X86.Concurrency.Cir.Mutex.wit_run (L := 9) (by simp [Wit.acts])
  refine ⟨σ, rs, labs, h1, h4 Silmaril.Proofs.X86.Concurrency.Cir.Mutex.wit_ret,
    ((List.range 8).map (fun k => (Wit.nxt (Wit.core k)).1)).flatten, ?_⟩
  rw [← h2, Wit.acts, List.flatten_append]
  simp

/-- **C11 shapes**: the lock is a futex lock (atomic accesses, acquire read-modify-writes,
waits), the exchange unlock a futex unlock (release read-modify-writes, wakes); Drepper's
original unlock, with its release store, is not. -/
theorem shapes :
    c11FLockB (Tv.chain Lock.cert.start) = true ∧ c11FUnlockB (Tv.chain Unlock.cert.start) = true ∧
    c11FUnlockB (Tv.chain UnlockDec.cert.start) = false :=
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  ⟨shape_fmLock, shape_fmUnlock, shape_fmUnlockDec⟩

/-! ## The interface and its clients -/

/-- The futex mutex's lock code is the validated program of `fmutex_lock`. -/
theorem fmutex_lockCode (L : Nat) : fmutex.lockCode L = Lock.cert.body L := rfl

/-- The futex mutex's unlock code is the validated program of `fmutex_unlock`. -/
theorem fmutex_unlockCode (L : Nat) : fmutex.unlockCode L = Unlock.cert.body L := rfl

/-- **`Even` linked with the futex mutex**: on TSO and XL, every finished, drained state has
even outputs, at every loop bound. -/
theorem even_fmutex (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (Mutex.Even.client.link fmutex L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Mutex.Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  Mutex.link_any_mutex Mutex.even_proved fmutex (Nat.le_refl _) L hr hd hf

/-- The same on the SC machine. -/
theorem even_fmutex_sc (L : Nat) {Cf : Cfg} (hr : ScReach 2 (Mutex.Even.client.link fmutex L) Cf)
    (hf : Cf.Done 2) : Mutex.Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  Mutex.link_any_mutex_sc Mutex.even_proved fmutex (Nat.le_refl _) L hr hf

/-- **Non-vacuity**: one thread running `lock; unlock` on an unlocked futex mutex (loop bound 2)
has a finished, drained TSO run, which leaves the lock word `0`. -/
theorem fm_one_finishes : ∃ Cf : OCfg, OReach .tso 1 Inst.one.cfg.toO Cf ∧ Cf.Drained ∧
    (Cf.ts 0).1 = .skip ∧ Cf.mem Mutex.Even.m = some 0 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 1) (c0 := Inst.one) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Cir.Mutex.fm_one_fin
  refine ⟨d.ocfg, hr, hd, hf 0 (by decide), ?_⟩
  simpa [Inst.unlockedB, Robust.CSt.ocfg] using hp

/-- **A contended two-thread TSO run** (kernel-checked by schedule, not by the
explorer). `Even` linked with the futex mutex at loop bound `2`: thread 0 takes the lock;
thread 1 fails the `cas`, sets the word to `2` and reaches its futex wait; thread 0's unlock
sees `2` and reaches its futex wake; both finish, the buffers drain, the lock word is `0`, and
both outputs are even. So the slow path, the wait and the wake all lie on finished runs, and
`even_fmutex` is not vacuously true of the contended protocol. -/
theorem fm_contended :
    ∃ C1 C2 C3 : OCfg, OReach .tso 2 Inst.evenC.cfg.toO C1 ∧
      Inst.atWait (C1.ts 1).1 = true ∧ C1.mem Mutex.Even.m = some 2 ∧
      OReach .tso 2 C1 C2 ∧ Inst.atWake (C2.ts 0).1 = true ∧ Inst.atWait (C2.ts 1).1 = true ∧
      OReach .tso 2 C2 C3 ∧ C3.Drained ∧ (∀ t < 2, (C3.ts t).1 = .skip) ∧
      C3.mem Mutex.Even.m = some 0 ∧ Mutex.Even.goal (fun t => (C3.ts t).2) C3.mem := by
  have h := Silmaril.Proofs.X86.Concurrency.Cir.Mutex.cont_checks
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he, -⟩, hw1⟩, hm1⟩, hk2⟩, hw2⟩, hs0⟩, hs1⟩, hb⟩, ho0⟩, ho1⟩, hm3⟩ := h
  have hr := @Silmaril.Proofs.X86.Concurrency.Cir.Mutex.walk_reach 2
  refine ⟨Inst.cont1.ocfg, Inst.cont2.ocfg, Inst.cont3.ocfg, ?_, hw1, hm1, hr _ _, hk2,
    hw2, hr _ _, ?_, ?_, hm3, ?_⟩
  · rw [Robust.start_toO he]; exact hr _ _
  · intro t
    simp only [Robust.CSt.ocfg, hb]
    rcases t with _ | _ | t <;> simp
  · intro t ht
    rcases t with _ | _ | t
    · exact TvCfg.sbeq_eq hs0
    · exact TvCfg.sbeq_eq hs1
    · omega
  · intro t ht
    rcases t with _ | _ | t
    · exact ⟨0, ho0, rfl⟩
    · exact ⟨0, ho1, rfl⟩
    · omega

/-! ## Drepper's original unlock -/

/-- **`fmutex_unlock_dec` is a release** of `R ∗ locked l`, from either pending flag. -/
theorem dec_release (l : Nat) (R J : Csl.HProp) (L : Nat) (rs : Regs) (p : Bool) (h : Csl.Heap)
    (hl : (rs .rdi).toNat = l) (hh : (Csl.hsep R (Spin.locked l)) h) :
    Csl.Rel.SafeR (Csl.Rel.liftI (Csl.hsep (Spin.inv l R) J))
      (fun _ _ h g => h = Csl.Heap.empty ∧ g = Csl.Heap.empty) p (UnlockDec.cert.body L) rs h
      Csl.Heap.empty :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.dec_release l R J L rs p h hl hh

/-- **`Task.decUnlock` holds** (as restated over `ProvedR`). -/
theorem decUnlock_holds : Task.decUnlock :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.decUnlock_holds

/-- **`Even` with Drepper's original unlock**: on TSO, for every loop bound, every finished,
drained state has even outputs. -/
theorem even_fmutexDec (L : Nat) {Cf : Csl.OCfg}
    (hr : Csl.OReach .tso 2 (Even.client.linkR fmutexDec L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexR even_provedR fmutexDec (Nat.le_refl _) L hr hd hf

/-! ## The ticket lock behind the interface -/

theorem initAllG_ticket (ls : List Nat) :
    initAllG ticketMutexG ls = ls.foldr (fun l h => Csl.Heap.union (ticketInit l) h) Csl.Heap.empty := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    show Csl.Heap.union (ticketMutexG.init l) (initAllG ticketMutexG ls) = _
    rw [ih]; rfl

/-- **The statement over `Client.Proved` is false**: the client `tx` tests
its unlock hole for `ticket_unlock`, is vacuously proved against every `Iface`, and writes its
forbidden value when linked with the real ticket lock. -/
theorem ticketIfaceFirst_false : ¬ ticketIfaceFirst :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.ticketIfaceFirst_false

/-- **The original statement of `Task.decUnlock` over `Client.Proved` is false**: the client
`dx` tests its holes for `fmutex_lock` and `fmutex_unlock_dec`, is vacuously
proved against every `Iface` with those codes (no invariant state disjoint from a lock token
has a 32-bit lock word), and writes its forbidden value when linked with the real codes. -/
theorem decUnlockIface_false : ¬ decUnlockIface :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.decUnlockIface_false

/-- **`Task.ticketIface` holds** (as restated over `ProvedG`). -/
theorem ticketIface_holds : Task.ticketIface := by
  intro C goal hC hslot hN L Cf hr hd hf
  have e : C.startWith (fun a => .seq (.assign .rdi a) (Prim.TicketLock.cert.body L))
      (fun a => .seq (.assign .rdi a) (Prim.TicketUnlock.cert.body L))
      (C.locks.foldr (fun l h => Csl.Heap.union (ticketInit l) h) Csl.Heap.empty) =
      C.linkG ticketMutexG L := by
    rw [Client.linkG, initAllG_ticket]; rfl
  rw [e] at hr
  exact link_any_mutexG hC ticketMutexG hslot hN L hr hd hf

end Silmaril.X86.Concurrency.Cir.Mutex.Futex
