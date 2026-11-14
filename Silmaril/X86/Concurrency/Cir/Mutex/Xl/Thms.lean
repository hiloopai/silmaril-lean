module

public import Silmaril.X86.Concurrency.Cir.Mutex.Xl.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Thms
public import Silmaril.X86.Concurrency.Cir.Prim.Xl.Thms

/-!
# The release-store mutex interfaces on every buffered model: proofs

PROVED (standard axioms only):

* `startWith_wb`: a tame client with tame holes has a tame start.
* **`link_any_mutexR_wb`, `link_any_mutexG_wb`**: `link_any_mutexR` and `link_any_mutexG` on
  every buffered model `M` (`.tso`, `.xl`), for a tame client (`Client.WbIn`) and a tame mutex
  (`IfaceR.WbCode`, `IfaceG.WbCode`).
* Tame mutexes: `spinMov_wb`, `spinMutexR_wb`, `spinMutexScR_wb`, `fmutexDec_wb`,
  `fmutexR_wb` (`IfaceR`);
  `ticketMutexG_wb`, `spinMovG_wb`, and `IfaceG.ofIfaceR` of any tame `IfaceR`
  (`ofIfaceR_wb`).
* **`movUnlockXl_holds`, `decUnlockXl_holds`, `ticketIfaceXl_holds`**: the three restated
  mutex Tasks on every buffered model, for tame clients.
* `even_wb`; `even_spinMov_any`, `even_fmutexDec_any`, `even_ticket_any`, `even_spinMovG_any`:
  the `Even` client with the release-store mutexes on every buffered model, every loop bound.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Tame (wbStores_gcert wbStores_chain reach_tso_of_wb)

/-- **A tame client with tame holes has a tame start.** -/
theorem startWith_wb {C : Client} (hC : C.WbIn) {lk ul : Expr → Stmt}
    (hl : ∀ a, (lk a).wbStores = true) (hu : ∀ a, (ul a).wbStores = true) (m : Heap) :
    (C.startWith lk ul m).WbStores C.N := by
  intro t ht
  simp [Client.startWith, ht, hC lk ul hl hu t]

theorem derived_wb {code : Stmt} (h : code.wbStores = true) (a : Expr) :
    (Stmt.seq (.assign .rdi a) code).wbStores = true := by
  simp [Stmt.wbStores, h]

/-- **`link_any_mutexR` on every buffered model**, for tame clients and mutexes. -/
theorem link_any_mutexR_wb {C : Client} {goal : (Nat → Regs) → Heap → Prop}
    (hC : C.ProvedR goal) (hW : C.WbIn) (M : IfaceR) (hMw : M.WbCode) (hM : M.size ≤ C.slot)
    (L : Nat) {model : OModel} {Cf : OCfg} (hr : OReach model C.N (C.linkR M L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < C.N, (Cf.ts t).1 = .skip) :
    goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexR hC M hM L (reach_tso_of_wb (startWith_wb hW (derived_wb (hMw L).1)
    (derived_wb (hMw L).2) _) hr) hd hf

/-- **`link_any_mutexG` on every buffered model**, for tame clients and mutexes. -/
theorem link_any_mutexG_wb {C : Client} {goal : (Nat → Regs) → Heap → Prop}
    (hC : C.ProvedG goal) (hW : C.WbIn) (M : IfaceG) (hMw : M.WbCode) (hM : M.size ≤ C.slot)
    (hN : M.thrOk C.N) (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model C.N (C.linkG M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < C.N, (Cf.ts t).1 = .skip) : goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexG hC M hM hN L (reach_tso_of_wb (startWith_wb hW (derived_wb (hMw L).1)
    (derived_wb (hMw L).2) _) hr) hd hf

/-! ### Tame mutexes -/

theorem movUnlockCode_wb (L : Nat) : (movUnlockCode L).wbStores = true :=
  Prim.Clients.spinUnlock_wb 0

theorem spinMov_wb : spinMov.WbCode := fun L =>
  ⟨Prim.Clients.spinLock_wb L, movUnlockCode_wb L⟩

theorem spinMutexR_wb : spinMutexR.WbCode := fun L => by
  refine ⟨Prim.Clients.spinLock_wb L, ?_⟩
  show (TvCfg.GCert.body Spin.unlockCert L).wbStores = true
  rw [wbStores_gcert]; decide

theorem spinMutexScR_wb : spinMutexScR.WbCode := fun L => by
  refine ⟨Prim.Clients.spinLock_wb L, ?_⟩
  show (TvCfg.GCert.body Spin.unlockScCert L).wbStores = true
  rw [wbStores_gcert]; decide

theorem fmutexDec_wb : Futex.fmutexDec.WbCode := fun L => by
  show (TvCfg.Fx.FCert.body Futex.Lock.cert L).wbStores = true ∧
    (TvCfg.Fx.FCert.body Futex.UnlockDec.cert L).wbStores = true
  simp only [TvCfg.Fx.FCert.body, Csl.Tame.wbStores_setB]
  decide

theorem fmutexR_wb : Futex.fmutexR.WbCode := fun L => by
  show (TvCfg.Fx.FCert.body Futex.Lock.cert L).wbStores = true ∧
    (TvCfg.Fx.FCert.body Futex.Unlock.cert L).wbStores = true
  simp only [TvCfg.Fx.FCert.body, Csl.Tame.wbStores_setB]
  decide

theorem ofIfaceR_wb {M : IfaceR} (h : M.WbCode) :
    (Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceG.ofIfaceR M).WbCode := h

theorem spinMovG_wb : spinMovG.WbCode := ofIfaceR_wb spinMov_wb

theorem ticketMutexG_wb : ticketMutexG.WbCode := fun L =>
  ⟨Prim.Clients.ticketLock_wb L, Prim.Clients.ticketUnlock_wb L⟩

/-! ### The restated Tasks on every buffered model -/

/-- **`movUnlockXl` is proved.** -/
theorem movUnlockXl_holds : movUnlockXl := by
  intro C goal hC hW h8 L M Cf hr hd hf
  exact movUnlock_holds C goal hC h8 L Cf (reach_tso_of_wb
    (startWith_wb hW (derived_wb (Prim.Clients.spinLock_wb L)) (derived_wb (movUnlockCode_wb L))
      _) hr) hd hf

/-! ### `Even` -/

/-- **`Even` is a tame client.** -/
theorem even_wb : Even.client.WbIn := by
  intro lk ul hl hu t
  simp [Even.client, Even.body, Even.cs, Stmt.wbStores, wbStores_chain, hl, hu]

/-- `Even` with the spin lock and the `mov` unlock, **on every buffered model**. -/
theorem even_spinMov_any (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (Even.client.linkR spinMov L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexR_wb even_provedR even_wb spinMov spinMov_wb (Nat.le_refl _) L hr hd hf

/-- `Even` with Drepper's original unlock, **on every buffered model**. -/
theorem even_fmutexDec_any (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (Even.client.linkR Futex.fmutexDec L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexR_wb even_provedR even_wb Futex.fmutexDec fmutexDec_wb (Nat.le_refl _) L hr hd hf

/-- `Even` with the ticket lock, **on every buffered model**. -/
theorem even_ticket_any (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (Even.client.linkG ticketMutexG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexG_wb even_provedG even_wb ticketMutexG ticketMutexG_wb (Nat.le_refl _)
    (by show 2 < 2 ^ 32; decide) L hr hd hf

/-- `Even` with the `mov`-unlock spin lock through `IfaceG`, **on every buffered model**. -/
theorem even_spinMovG_any (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 (Even.client.linkG spinMovG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Even.goal (fun t => (Cf.ts t).2) Cf.mem :=
  link_any_mutexG_wb even_provedG even_wb spinMovG spinMovG_wb (Nat.le_refl _) trivial L hr hd hf

/-- **Non-vacuity on XL**: `Even` with the ticket lock reaches a finished, drained XL state
(the TSO witness `even_ticket_finishes`, which is an XL run by `Csl.tso_reach_xl`). -/
theorem even_ticket_finishes_xl : ∃ Cf : OCfg,
    OReach .xl 2 (Even.client.linkG ticketMutexG Inst.L).toO Cf ∧
    Cf.Drained ∧ (∀ t < 2, (Cf.ts t).1 = .skip) ∧ Even.goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨Cf, hr, hd, hf, hg⟩ := even_ticket_finishes
  exact ⟨Cf, tso_reach_xl hr, hd, hf, hg⟩

end Silmaril.X86.Concurrency.Cir.Mutex

namespace Silmaril.X86.Concurrency.Cir.Mutex.Futex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Csl.Tame (reach_tso_of_wb)

/-- **`decUnlockXl` is proved.** -/
theorem decUnlockXl_holds : decUnlockXl := by
  intro C goal hC hW h8 L M Cf hr hd hf
  obtain ⟨h1, h2⟩ := fmutexDec_wb L
  exact decUnlock_holds C goal hC h8 L Cf (reach_tso_of_wb
    (startWith_wb hW (derived_wb h1) (derived_wb h2) _) hr) hd hf

/-- **`ticketIfaceXl` is proved.** -/
theorem ticketIfaceXl_holds : ticketIfaceXl := by
  intro C goal hC hW h8 hN L M Cf hr hd hf
  exact ticketIface_holds C goal hC h8 hN L Cf (reach_tso_of_wb
    (startWith_wb hW (derived_wb (Prim.Clients.ticketLock_wb L))
      (derived_wb (Prim.Clients.ticketUnlock_wb L)) _) hr) hd hf

end Silmaril.X86.Concurrency.Cir.Mutex.Futex
