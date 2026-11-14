module

public import Silmaril.X86.Concurrency.Cir.Mutex.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Spin
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Rel
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Ghost
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Frame
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Client
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Checks
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Inst
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Review
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.RelCex
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.RelClient
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.GhostClient
import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.GhostInst

/-!
# The CIR Mutex interface: theorems

PROVED (standard axioms; proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Mutex/`), except where a statement names a Task.

## The logic

* `safe_inv_frame`: a thread safe under the invariant `I` is safe under `I ∗ J`. This is what
  makes the interface's "every frame invariant" specs implementable and composable (several
  mutexes, other shared state).

## The implementation (`spinMutex`, `spinMutexSc`: definitions in the proofs module `Spin`)

* `tv_ok`, `refines`: `mutex_lock`, `mutex_unlock` and `mutex_unlock_sc` (gcc 13.3.0 `-O2`,
  `examples/litmus-c/mutex/`) validate into their CIR programs (the CFG checker), so every x86
  run of the bytes is a run of the CIR program; `lock_bytes`: `mutex_lock` is the `spin_lock`.
* `modes_ok`: every C11 mode of the three certificates is implemented by its instruction
  (`modeOk1`); `movSc_rejected`: a `seq_cst` claim on a plain `mov` store passes TV but fails the
  mode check. `shapes`: the lock has the C11 shape of an acquire, the unlocks of a release; the
  `mov` unlock and a relaxed-exchange lock do not.
* `spinMutex`, `spinMutexSc : Iface`: the CSL specs of lock (from `spinLock_acquire`) and
  unlock (new: the releasing exchange hands `R` and the token back).

## Linking

* **`link_any_mutex`**: a client proved against the interface (`C.Proved goal`), linked with any
  `M : Iface` that fits its slots, satisfies `goal` in every finished, drained state of the
  CIR-native TSO and XL store-buffer machines. `link_any_mutex_sc`: the same on the SC machine.
  `link_no_race`: the linked program has no race in any SC-reachable state.
* `Link.link_any_mutex_obj` (`Mutex/Link/Thms.lean`): the object-level statement, generic in the
  link logic, through `Link/Env`.

## The `Even` client

* `even_proved`: `Even.client` is proved against the interface (for every `M`).
* `even_spin`, `even_spinSc`: so on TSO and XL, linked with either spin mutex, both outputs
  are even.
* Non-vacuity: `even_spin_finishes` (the linked program finishes, explorer witness);
  `racy_odd` (with the holes empty, a finished TSO state has an odd output: the goal needs the
  mutex).
* `movUnlock_even` (instance of `Task.movUnlock`): with the `mov`-release unlock, every
  finished, drained TSO state at loop bound 2 has even outputs, and one exists. This is a
  closed-instance explorer result; `even_spinMov` is the same for every loop bound.

## Release by a plain store

* **`link_any_mutexR`**: a client proved against the interface with release stores
  (`C.ProvedR goal`), linked with any `M : IfaceR` that fits its slots, satisfies `goal` in every
  finished, drained state of the CIR-native TSO machine (`Csl.Rel.rel_tso`).
* `IfaceR.ofIface`, `spinMutexR`, `spinMutexScR`: `Iface`s whose lock and unlock drain
  first are `IfaceR`s.
* **`spinMov : IfaceR`**: the spin lock with the `mov` unlock (`mov_release`: the plain store is
  a release of `R ∗ locked l` by the release rule).
* **`movUnlock_holds : Task.movUnlock`** (restated over `ProvedR`).
* **`movUnlockIface_false : ¬ movUnlockIface`**: the statement over `Client.Proved` is false
  (a client that tests its unlock hole for the `mov` code).
* `even_provedR`, `even_spinMov`: `Even` is proved against `IfaceR`, so with the `mov` unlock
  both outputs are even on TSO for every loop bound.

## The interface with ghost state

* **`link_any_mutexG`**: a client proved against `IfaceG` (`C.ProvedG goal`), linked with any
  `M : IfaceG` that fits its slots and supports its thread count, satisfies `goal` in every
  finished, drained TSO state.
* `IfaceG.ofIfaceR`: every `IfaceR` is an `IfaceG` (`spinMovG`).
* **`ticketMutexG : IfaceG`**: the ticket lock, ghost tokens in `Csl.Rel`'s ghost heaps.
* `even_provedG`, **`even_ticket`**, `even_spinMovG`: `Even` is proved against `IfaceG`, so with
  the ticket lock both outputs are even on TSO for every loop bound; `even_ticket_finishes`:
  the linked program has such a run (loop bound 2, the explorer).

## Further checks

* `tv_rejects_mutants`: the checker rejects the exchange certificate on the `mov` bytes, the
  `mov` certificate on the exchange bytes, and `xchg` → `mov` byte mutants of `mutex_lock` and
  `mutex_unlock` against their own certificates.
* `lockCode_ne_skip`: the interface constrains its code; no `Iface` lock is `skip`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.TvCfg (tvCfg GCert TRun XRun regsOf tvCfg_sound tvCfg_code)
open Silmaril.X86.Concurrency.Cir.Robust (CSt memOf)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-! ## The logic -/

/-- **The invariant frame rule.** -/
theorem safe_inv_frame {I J : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Csl.Safe I Q s rs h) : Csl.Safe (I ∗ J) Q s rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.safe_inv_frame H

/-- `Safe` respects equivalent invariants. -/
theorem safe_inv_eq {I I' : HProp} (hI : ∀ h, I h ↔ I' h) {Q : Regs → HProp} {s : Stmt}
    {rs : Regs} {h : Heap} (H : Csl.Safe I Q s rs h) : Csl.Safe I' Q s rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.safe_inv_eq hI H

/-! ## Translation validation and modes -/

/-- `mutex_lock` is byte-identical to the `spin_lock`. -/
theorem lock_bytes : Code.mutexLock = Prim.Code.spinLock :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.lock_bytes

/-- **The three certificates check against the pinned bytes.** -/
theorem tv_ok : ∀ p ∈ Spin.all, tvCfg (Prim.thr p.2.1) p.2.2 = true := by
  intro p hp
  simp only [Spin.all, List.mem_cons, List.not_mem_nil, or_false] at hp
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  rcases hp with rfl | rfl | rfl
  · exact tv_lock
  · exact tv_unlock
  · exact tv_unlockSc

/-- **The binaries are their CIR programs**: every x86 run of each pinned function is a run of
its CIR program, for every loop bound at least the run's length (`tvCfg_sound`). -/
theorem refines {name : String} {code : List (BitVec 8)} {c : GCert}
    (hp : (name, code, c) ∈ Spin.all)
    {t : Tv.XThread} (htc : t.code = code) {s0 s : Silmaril.X86.State} (h0 : s0.rip = t.base)
    {acc : List (List XAct)} (hr : XRun t s0 acc s) {L : Nat} (hL : acc.length ≤ L) :
    ∃ σ rs labs, TRun (c.body L) (regsOf s0) labs σ rs ∧ acc.flatten = labs.flatMap Lab.acts ∧
      regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) := by
  have h := tv_ok _ hp
  rw [tvCfg_code (t' := t) (by simp [Prim.thr, htc])] at h
  exact tvCfg_sound h h0 hr hL

/-- **The C11 modes are implemented by the instructions** (`modeOk1`). -/
theorem modes_ok : ∀ p ∈ Spin.all, cfgModesOk (Prim.thr p.2.1) p.2.2 = true := by
  intro p hp
  simp only [Spin.all, List.mem_cons, List.not_mem_nil, or_false] at hp
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  rcases hp with rfl | rfl | rfl
  · exact modes_lock
  · exact modes_unlock
  · exact modes_unlockSc

/-- **The mode check is not vacuous**: `spin_unlock` claimed `seq_cst` passes TV (modes are
compared away) and fails the mode check (a `seq_cst` store needs a locked instruction). -/
theorem movSc_rejected : tvCfg (Prim.thr Prim.Code.spinUnlock) ModeMutants.movSc = true ∧
    cfgModesOk (Prim.thr Prim.Code.spinUnlock) ModeMutants.movSc = false :=
  ⟨Silmaril.Proofs.X86.Concurrency.Cir.Mutex.movSc_tv,
    Silmaril.Proofs.X86.Concurrency.Cir.Mutex.movSc_modes⟩

/-- **C11 shapes**, at every loop bound: the lock is an acquire, both unlocks are releases; the
`mov` release store and a relaxed-exchange lock are not. -/
theorem shapes (L : Nat) : c11LockB (spinMutex.lockCode L) = true ∧
    c11UnlockB (spinMutex.unlockCode L) = true ∧ c11UnlockB (spinMutexSc.unlockCode L) = true ∧
    c11UnlockB (Tv.chain Prim.SpinUnlock.cert.start) = false ∧
    c11LockB ModeMutants.lockRlx = false := by
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  refine ⟨?_, ?_, ?_, shape_mov, shape_lockRlx⟩
  · show c11LockB (Prim.SpinLock.cert.body L) = true
    rw [GCert.body, c11LockB, accessesOf_setB]; exact shape_lock
  · show c11UnlockB (Spin.unlockCert.body L) = true
    rw [GCert.body, c11UnlockB, accessesOf_setB]; exact shape_unlock
  · show c11UnlockB (Spin.unlockScCert.body L) = true
    rw [GCert.body, c11UnlockB, accessesOf_setB]; exact shape_unlockSc

/-! ## Linking any mutex -/

/-- **`link_any_mutex`**: a client proved against the interface, linked with **any** mutex `M`
meeting it (and fitting the client's slots), satisfies its goal in every finished, drained state
of the CIR-native TSO or XL store-buffer machine, for every loop bound. -/
theorem link_any_mutex {C : Client} {goal : (Nat → Regs) → Heap → Prop} (hC : C.Proved goal)
    (M : Iface) (hM : M.size ≤ C.slot) (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model C.N (C.link M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < C.N, (Cf.ts t).1 = .skip) : goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨I, Q, hs, hI, G, hgoal⟩ := hC M hM L
  obtain ⟨hs', hI', q, i, -, -, l1, l2⟩ := csl_buffered G hr hd hf
  exact hgoal _ _ hs' hI' q i l1 l2

/-- **`link_any_mutex` on the SC machine.** -/
theorem link_any_mutex_sc {C : Client} {goal : (Nat → Regs) → Heap → Prop} (hC : C.Proved goal)
    (M : Iface) (hM : M.size ≤ C.slot) (L : Nat) {Cf : Cfg} (hr : ScReach C.N (C.link M L) Cf)
    (hf : Cf.Done C.N) : goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨I, Q, hs, hI, G, hgoal⟩ := hC M hM L
  obtain ⟨hs', hI', q, i, -, -, l1, l2⟩ := (csl_sc G hr).2 hf
  exact hgoal _ _ hs' hI' q i l1 l2

/-- **The linked program is race-free** (`no_race`). -/
theorem link_no_race {C : Client} {goal : (Nat → Regs) → Heap → Prop} (hC : C.Proved goal)
    (M : Iface) (hM : M.size ≤ C.slot) (L : Nat) {Cf : Cfg} (hr : ScReach C.N (C.link M L) Cf) :
    ¬ Race C.N Cf := by
  obtain ⟨I, Q, hs, hI, G, -⟩ := hC M hM L
  exact no_race G hr

/-! ## The `Even` client -/

/-- **`Even` is proved against the interface.** -/
theorem even_proved : Even.client.Proved Even.goal :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.even_proved

/-- **`Even` linked with the spin mutex**: on TSO and XL, every finished, drained state has
even outputs. -/
theorem even_spin (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (Even.client.link spinMutex L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutex even_proved spinMutex (Nat.le_refl _) L hr hd hf

/-- The same with `mutex_unlock_sc` (C11 `store(seq_cst)`). -/
theorem even_spinSc (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (Even.client.link spinMutexSc L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutex even_proved spinMutexSc (Nat.le_refl _) L hr hd hf

theorem evenOuts_goal {c : CSt} (h : Inst.evenOuts c = true) (rs : Nat → Regs) :
    Even.goal rs (memOf c.mem) := by
  simp only [Inst.evenOuts, Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨v0, e0, h0⟩, ⟨v1, e1, h1⟩⟩ := h
  intro t ht
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
  · exact ⟨v0, e0, h0⟩
  · exact ⟨v1, e1, h1⟩

theorem goal_evenOuts {c : CSt} {rs : Nat → Regs} (h : Even.goal rs (memOf c.mem)) :
    Inst.evenOuts c = true := by
  obtain ⟨v0, e0, h0⟩ := h 0 (by omega)
  obtain ⟨v1, e1, h1⟩ := h 1 (by omega)
  simp [Inst.evenOuts, e0, e1, h0, h1]

/-- **Non-vacuity: the linked program finishes** (loop bound 2, TSO), with even outputs. -/
theorem even_spin_finishes : ∃ Cf : OCfg, OReach .tso 2 (Even.client.link spinMutex Inst.L).toO Cf ∧
    Cf.Drained ∧ (∀ t < 2, (Cf.ts t).1 = .skip) ∧ Even.goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 2) (c0 := Inst.linkC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Cir.Mutex.link_fin
  rw [Silmaril.Proofs.X86.Concurrency.Cir.Mutex.linkC_cfg] at hr
  exact ⟨d.ocfg, hr, hd, hf, evenOuts_goal hp _⟩

/-- **Non-vacuity: the goal needs the mutex.** With both holes empty, a finished, drained TSO
state has an odd output. -/
theorem racy_odd : ∃ Cf : OCfg,
    OReach .tso 2 (Even.client.startWith Inst.noOp Inst.noOp Heap.empty).toO Cf ∧ Cf.Drained ∧
    (∀ t < 2, (Cf.ts t).1 = .skip) ∧ ¬ Even.goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 2) (c0 := Inst.racyC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Cir.Mutex.racy_odd
  rw [Silmaril.Proofs.X86.Concurrency.Cir.Mutex.racyC_cfg] at hr
  refine ⟨d.ocfg, hr, hd, hf, fun hg => ?_⟩
  have := goal_evenOuts (c := d) hg
  simp [this] at hp

/-- **An instance of `Task.movUnlock`** (explorer, loop bound 2): `Even` with the spin lock and
the `mov`-release unlock has even outputs in every finished, drained TSO state, and finishes. -/
theorem movUnlock_even :
    (∀ Cf : OCfg, OReach .tso 2 (Even.client.startWith
        (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body Inst.L))
        (fun a => .seq (.assign .rdi a) (movUnlockCode Inst.L))
        (Even.client.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty)).toO Cf →
      Cf.Drained → (∀ t < 2, (Cf.ts t).1 = .skip) → Even.goal (fun t => (Cf.ts t).2) Cf.mem) ∧
    ∃ Cf : OCfg, OReach .tso 2 (Even.client.startWith
        (fun a => .seq (.assign .rdi a) (Prim.SpinLock.cert.body Inst.L))
        (fun a => .seq (.assign .rdi a) (movUnlockCode Inst.L))
        (Even.client.locks.foldr (fun l h => Heap.union (Spin.init l) h) Heap.empty)).toO Cf ∧
      Cf.Drained ∧ (∀ t < 2, (Cf.ts t).1 = .skip) := by
  refine ⟨fun Cf hr hd hf => ?_, ?_⟩
  · rw [← Silmaril.Proofs.X86.Concurrency.Cir.Mutex.movC_cfg] at hr
    obtain ⟨d, hp, rfl⟩ := Robust.tsoCheck_sound
      Silmaril.Proofs.X86.Concurrency.Cir.Mutex.mov_even hr hd hf
    exact evenOuts_goal hp _
  · obtain ⟨d, hr, hd, hf, -⟩ := Robust.witness_of_any (N := 2) (c0 := Inst.movC) rfl rfl
      Silmaril.Proofs.X86.Concurrency.Cir.Mutex.mov_fin
    rw [Silmaril.Proofs.X86.Concurrency.Cir.Mutex.movC_cfg] at hr
    exact ⟨d.ocfg, hr, hd, hf⟩

/-! ## Further checks -/

/-- **TV rejects mutated code**. -/
theorem tv_rejects_mutants :
    tvCfg (Prim.thr Prim.Code.spinUnlock) Spin.unlockCert = false ∧
    tvCfg (Prim.thr Code.mutexUnlock) Prim.SpinUnlock.cert = false ∧
    tvCfg (Prim.thr (Code.mutexLock.set 10 0x89)) Prim.SpinLock.cert = false ∧
    tvCfg (Prim.thr (Code.mutexUnlock.set 2 0x89)) Spin.unlockCert = false :=
  open Silmaril.Proofs.X86.Concurrency.Cir.Mutex in
  ⟨rev_tv_xchgCert_movBytes, rev_tv_movCert_xchgBytes, rev_tv_lockMovMut, rev_tv_unlockMovMut⟩

/-- **The interface constrains its code**: no `Iface` lock is `skip`. -/
theorem lockCode_ne_skip (M : Iface) (L : Nat) : M.lockCode L ≠ .skip :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.rev_lockCode_ne_skip M L

/-! ## Release by a plain store -/

/-- **`link_any_mutexR`**: a client proved against the interface with release stores, linked with
any `IfaceR` mutex fitting its slots, gets its goal in every finished, drained TSO state. -/
theorem link_any_mutexR {C : Client} {goal : (Nat → Regs) → Heap → Prop} (hC : C.ProvedR goal)
    (M : IfaceR) (hM : M.size ≤ C.slot) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso C.N (C.linkR M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < C.N, (Cf.ts t).1 = .skip) : goal (fun t => (Cf.ts t).2) Cf.mem :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.link_any_mutexR hC M hM L hr hd hf

/-- **`spin_unlock` (a plain `mov`) is a release** of `R ∗ locked l`, from either flag. -/
theorem mov_release (l : Nat) (R J : HProp) (L : Nat) (rs : Regs) (p : Bool) (h : Heap)
    (hl : (rs .rdi).toNat = l) (hh : (R ∗ Spin.locked l) h) :
    Rel.SafeR (Rel.liftI (Spin.inv l R ∗ J)) (fun _ _ h g => h = Heap.empty ∧ g = Heap.empty) p
      (movUnlockCode L) rs h Heap.empty :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.mov_release l R J L rs p h hl hh

/-- **`Task.movUnlock` holds** (as restated over `ProvedR`). -/
theorem movUnlock_holds : Task.movUnlock :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.movUnlock_holds

/-- **The statement over `Client.Proved` is false.** -/
theorem movUnlockIface_false : ¬ movUnlockIface :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.movUnlockIface_false

/-- **`Even` is proved against the interface with release stores.** -/
theorem even_provedR : Even.client.ProvedR Even.goal :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.even_provedR

/-- **`Even` with the spin lock and the `mov` unlock**: on TSO, for every loop bound, every
finished, drained state has even outputs (`movUnlock_even` was loop bound 2 only). -/
theorem even_spinMov (L : Nat) {Cf : OCfg}
    (hr : OReach .tso 2 (Even.client.linkR spinMov L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexR even_provedR spinMov (Nat.le_refl _) L hr hd hf

/-- `Even` with the exchange-unlock spin mutex, through `IfaceR` (the same guarantee as
`even_spin` on TSO, now from the logic with release stores). -/
theorem even_spinR (L : Nat) {Cf : OCfg}
    (hr : OReach .tso 2 (Even.client.linkR spinMutexR L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexR even_provedR spinMutexR (Nat.le_refl _) L hr hd hf

/-! ## The interface with ghost state -/

/-- **`link_any_mutexG`**: a client proved against the interface with ghost state, linked with
any `IfaceG` mutex fitting its slots and supporting its number of threads, gets its goal in every
finished, drained TSO state. -/
theorem link_any_mutexG {C : Client} {goal : (Nat → Regs) → Heap → Prop} (hC : C.ProvedG goal)
    (M : IfaceG) (hM : M.size ≤ C.slot) (hN : M.thrOk C.N) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso C.N (C.linkG M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < C.N, (Cf.ts t).1 = .skip) : goal (fun t => (Cf.ts t).2) Cf.mem :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.link_any_mutexG hC M hM hN L hr hd hf

/-- **`Even` is proved against the interface with ghost state.** -/
theorem even_provedG : Even.client.ProvedG Even.goal :=
  Silmaril.Proofs.X86.Concurrency.Cir.Mutex.even_provedG

/-- **`Even` with the ticket lock**: on TSO, for every loop bound, every finished, drained state
has even outputs. -/
theorem even_ticket (L : Nat) {Cf : OCfg}
    (hr : OReach .tso 2 (Even.client.linkG ticketMutexG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexG even_provedG ticketMutexG (Nat.le_refl _) (by show 2 < 2 ^ 32; decide) L hr hd hf

/-- **Non-vacuity of `even_ticket`**: `Even` linked with the ticket lock (loop
bound 2) reaches a finished, drained TSO state, which has even outputs by `even_ticket`. -/
theorem even_ticket_finishes : ∃ Cf : OCfg,
    OReach .tso 2 (Even.client.linkG ticketMutexG Inst.L).toO Cf ∧
    Cf.Drained ∧ (∀ t < 2, (Cf.ts t).1 = .skip) ∧ Even.goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨d, hr, hd, hf, -⟩ := Robust.witness_of_any (N := 2) (c0 := Inst.ticketC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Cir.Mutex.ticket_fin
  rw [Silmaril.Proofs.X86.Concurrency.Cir.Mutex.ticketC_cfg] at hr
  exact ⟨d.ocfg, hr, hd, hf, even_ticket Inst.L hr hd hf⟩

/-- `Even` with the `mov`-unlock spin lock, through `IfaceG` (`IfaceG.ofIfaceR spinMov`). -/
theorem even_spinMovG (L : Nat) {Cf : OCfg}
    (hr : OReach .tso 2 (Even.client.linkG spinMovG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexG even_provedG spinMovG (Nat.le_refl _) trivial L hr hd hf

end Silmaril.X86.Concurrency.Cir.Mutex
