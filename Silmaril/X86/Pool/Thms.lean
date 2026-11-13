module

public import Silmaril.X86.Pool.Defs
import Silmaril.Proofs.X86.Pool.Split
import Silmaril.Proofs.X86.Pool.Par
import Silmaril.Proofs.X86.Pool.Tso
import Silmaril.Proofs.X86.Pool.Drf
import Silmaril.Proofs.X86.Pool.RightRotLocal
public import Silmaril.Proofs.X86.Pool.Example
public import Silmaril.Proofs.X86.Pool.RightRot
public import Silmaril.Proofs.X86.Pool.Counter

/-!
# Thread pools: what is proved

Every theorem here is PROVED with the standard axioms
(proofs in `Silmaril/Proofs/X86/Pool/{Split,Par,Tso,Fetch,Drf,Example,RightRot,
RightRotLocal,Counter}.lean`). Both Tasks are proved: `drfTso_holds : Task.drfTso` and
`RightRot.rightRotLocal_holds : Task.rightRotLocal`.

**DRF** (`Drf.lean`). `drfTso_holds`: every TSO-reachable pool of a footprint-ownership-safe
pool is simulated by an SC-reachable pool with the same threads, whose memory holds, on each
thread's owned cells, what that thread sees (its buffer over memory), and elsewhere the memory's
bytes; at a drained state the two pools are equal. `Task.drfTso`'s hypothesis gained a
conjunct (`FetchStable` in `LSafeEv`); the earlier version is false (`drfTso_noFetch_false`,
`Counter.lean`). `openFetch_stable`: every `Ext` fetch of `openEv` is stable.

**Split.** `toFrag_split`: a single-thread fragment is its local half (registers, `rip`,
flags) next to its shared half (byte cells, `regions`). `proj_poolFrag`: a thread's view of
the pool fragment is the fragment of its single-thread state.

**Frame-requantified triples.** `LTriple.toSTripleS`: with no read-only context, an `LTriple`
is an `STripleS`, so the stronger notion used for parallel composition still gives the
sequential stable triple. `LTriple.of_chain`: an `LTriple` from a chain of one-step rules
(`Step1`), the entry point for machine proofs (`Task.rightRotLocal` reduces to fifteen of
them).

`LTripleEv.toLTriple`, `OwnershipSafeEv.toOwnershipSafe`: the footprint notions used by
`Task.drfTso` forget to the frame-requantified ones.

**Parallel composition** (partial correctness, every schedule, no other thread running).
* `par_shared_ro`: two threads with `LTriple`s over the same read-only context `C`;
  `C` and the frame `F` hold again when both have finished.
* `par_disjoint`: the case `C = emp`.

**Ownership safety is an SC invariant.** `OwnershipSafe.step`, `OwnershipSafe.reach`,
`OwnershipSafe.progress`.

**TSO pools against the access lists and store buffers.** `overlay_getElem?` (a thread's view is
`viewMem`),
`tsoFlush_toX` (a pool flush is an `XFlush`), `openEv_step`/`open9Ev_step`/`atomic9Ev_step`
(the access-list machines are `Open.step`/`Open9.step`/`Atomic9.step`), `tsoStep_sync_sc`
(a synchronising step on an empty buffer is an SC step), `ofPool_drained`, `forget_ofPool`.

**Non-vacuity** (`Example`): two threads run the same `ret` byte at `0x400000` (shared
read-only) on disjoint stacks. `ret_ltriple`, `ret_ltripleEv`; `two_ownershipSafe`;
`two_ownershipSafeEv` (the hypothesis of `Task.drfTso` holds); `two_poolSafe`
(`par_shared_ro` applied: every schedule safe, both postconditions at the end); `drfTso_two`
(every drained TSO state of the pool is SC-reachable).

**The `RightRot` leaf in a pool.** `rightRotLocal_holds : Task.rightRotLocal`: `right_rot`
meets the footprint triple `LTripleEv` with its code as read-only context, its fifteen steps
replayed one at a time on an arbitrary consistent memory (`RightRotLocal.lean`).
`rightRot_two_ownershipSafeEv`, `rightRot_two_ownershipSafe`: two threads running `right_rot`
(shared code at `0x400000`) on disjoint stacks form an ownership-safe pool.
`drfTso_rightRot`: the TSO pool of that pool reaches only SC-reachable drained states.
-/

@[expose] public section

namespace Silmaril.X86.Pool

open Silmaril.X86 (State MState Word)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Le)

variable {Tid : Type}

/-! ## Split -/

/-- **The local/shared split of a machine-state fragment.** -/
theorem toFrag_split (m : MState) :
    toFrag m = Frag.union (localFrag m.core) (sharedFrag m.memory) :=
  Silmaril.Proofs.X86.Pool.toFrag_split m

theorem proj_poolFrag [DecidableEq Tid] {p : Pool Tid} {t : Tid} {c : State}
    (ht : p.threads t = some c) : proj t (poolFrag p) = toFrag ⟨c, p.memory⟩ :=
  Silmaril.Proofs.X86.Pool.proj_poolFrag ht

/-! ## Triples -/

/-- **A frame-requantified triple is a stable triple.** -/
theorem LTriple.toSTripleS {step : MState → Option MState} {Fin : State → Prop}
    {P Q : SProp} {n : Nat} (h : LTriple step Fin emp P Q n) :
    Silmaril.X86.Safe.STripleS step n P Q :=
  Silmaril.Proofs.X86.Pool.LTriple.toSTripleS h

/-- **A frame-requantified triple from a chain of one-step rules.** -/
theorem LTriple.of_chain {step : MState → Option MState} {Fin : State → Prop} {R Q : SProp}
    {I : Nat → SProp} {N : Nat}
    (hstep : ∀ k < N, Step1 step R (I k) (I (k + 1)))
    (hrun : ∀ k < N, ∀ c mem h r, R r → I k h → Frag.Disjoint h r →
      Le (union h r) (toFrag ⟨c, mem⟩) → ¬ Fin c)
    (hfin : ∀ c mem h r, R r → I N h → Frag.Disjoint h r → Le (union h r) (toFrag ⟨c, mem⟩) →
      Fin c ∧ Q h) (n : Nat) :
    LTriple step Fin R (I 0) Q n :=
  Silmaril.Proofs.X86.Pool.LTriple.of_chain hstep hrun hfin n

/-- **Footprint safety forgets to frame-requantified safety.** -/
theorem LTripleEv.toLTriple {M : EvMachine} {Fin : State → Prop} {R P Q : SProp} {n : Nat}
    (h : LTripleEv M Fin R P Q n) : LTriple M.step Fin R P Q n :=
  Silmaril.Proofs.X86.Pool.LTripleEv.toLTriple h

theorem OwnershipSafeEv.toOwnershipSafe [DecidableEq Tid] {M : EvMachine}
    {Fin : Tid → State → Prop} {p : Pool Tid} (h : OwnershipSafeEv M Fin p) :
    OwnershipSafe M.step Fin p :=
  Silmaril.Proofs.X86.Pool.OwnershipSafeEv.toOwnershipSafe h

/-! ## Parallel composition -/

section Par
variable [DecidableEq Tid] (step : MState → Option MState) (Fin : Tid → State → Prop)
  (t₁ t₂ : Tid) (C P₁ Q₁ P₂ Q₂ : SProp) (F : PProp Tid)

/-- **Disjoint parallel composition with read-only sharing**. -/
theorem par_shared_ro (ht : t₁ ≠ t₂) {n : Nat}
    (h₁ : LTriple step (Fin t₁) C P₁ Q₁ n) (h₂ : LTriple step (Fin t₂) C P₂ Q₂ n)
    {p : Pool Tid} (hr₁ : ∃ c, p.threads t₁ = some c) (hr₂ : ∃ c, p.threads t₂ = some c)
    (hothers : ∀ t, t ≠ t₁ → t ≠ t₂ → p.threads t = none)
    (hpre : (atThread t₁ P₁ ∗ₚ atThread t₂ P₂ ∗ₚ atShared C ∗ₚ F) (poolFrag p)) :
    PoolSafe step Fin
      (fun p' => (atThread t₁ Q₁ ∗ₚ atThread t₂ Q₂ ∗ₚ atShared C ∗ₚ F) (poolFrag p')) n p :=
  Silmaril.Proofs.X86.Pool.par_shared_ro step Fin t₁ t₂ C P₁ Q₁ P₂ Q₂ F ht h₁ h₂ hr₁ hr₂
    hothers hpre

/-- **Disjoint parallel composition** (CSL without shared resources). -/
theorem par_disjoint (ht : t₁ ≠ t₂) {n : Nat}
    (h₁ : LTriple step (Fin t₁) emp P₁ Q₁ n) (h₂ : LTriple step (Fin t₂) emp P₂ Q₂ n)
    {p : Pool Tid} (hr₁ : ∃ c, p.threads t₁ = some c) (hr₂ : ∃ c, p.threads t₂ = some c)
    (hothers : ∀ t, t ≠ t₁ → t ≠ t₂ → p.threads t = none)
    (hpre : (atThread t₁ P₁ ∗ₚ atThread t₂ P₂ ∗ₚ F) (poolFrag p)) :
    PoolSafe step Fin (fun p' => (atThread t₁ Q₁ ∗ₚ atThread t₂ Q₂ ∗ₚ F) (poolFrag p')) n p :=
  Silmaril.Proofs.X86.Pool.par_disjoint step Fin t₁ t₂ P₁ Q₁ P₂ Q₂ F ht h₁ h₂ hr₁ hr₂
    hothers hpre

end Par

/-! ## Ownership safety -/

section Own
variable [DecidableEq Tid] {st : MState → Option MState} {Fin : Tid → State → Prop}

theorem OwnershipSafe.step {p p' : Pool Tid} {t : Tid} (hown : OwnershipSafe st Fin p)
    (hst : SCStepF st Fin p t p') : OwnershipSafe st Fin p' :=
  Silmaril.Proofs.X86.Pool.OwnershipSafe.step hown hst

/-- **Ownership safety holds at every SC-reachable pool.** -/
theorem OwnershipSafe.reach {p p' : Pool Tid} (hown : OwnershipSafe st Fin p)
    (hr : SCReach st Fin p p') : OwnershipSafe st Fin p' :=
  Silmaril.Proofs.X86.Pool.OwnershipSafe.reach hown hr

/-- No running, unfinished thread of an ownership-safe pool is stuck. -/
theorem OwnershipSafe.progress {p : Pool Tid} (hown : OwnershipSafe st Fin p) {t : Tid}
    {c : State} (ht : p.threads t = some c) (hnf : ¬ Fin t c) :
    ∃ p', SCStepF st Fin p t p' :=
  Silmaril.Proofs.X86.Pool.OwnershipSafe.progress hown ht hnf

end Own

/-! ## TSO pools against the access lists and store buffers -/

/-- **A thread's view is `viewMem`.** -/
theorem overlay_getElem? (p : TPool Tid) (t : Tid) (x : Nat) :
    (overlay p.memory (p.buffer t)).bytes[x]? = Silmaril.X86.MemoryModel.Tso.viewMem p.toX t x :=
  Silmaril.Proofs.X86.Pool.overlay_getElem? p t x

/-- **A pool flush is a store-buffer flush.** -/
theorem tsoFlush_toX [DecidableEq Tid] {p p' : TPool Tid} (h : TsoFlush p p') :
    Silmaril.X86.MemoryModel.Tso.XFlush p.toX p'.toX :=
  Silmaril.Proofs.X86.Pool.tsoFlush_toX h

theorem openEv_step : openEv.step = Silmaril.X86.Open.step :=
  Silmaril.Proofs.X86.Pool.openEv_step

theorem open9Ev_step : open9Ev.step = Silmaril.X86.Open9.step :=
  Silmaril.Proofs.X86.Pool.open9Ev_step

theorem atomic9Ev_step : atomic9Ev.step = Silmaril.X86.Atomic9.step :=
  Silmaril.Proofs.X86.Pool.atomic9Ev_step

theorem ofPool_drained (p : Pool Tid) : Drained (TPool.ofPool p) :=
  Silmaril.Proofs.X86.Pool.ofPool_drained p

theorem forget_ofPool (p : Pool Tid) : forget (TPool.ofPool p) = p :=
  Silmaril.Proofs.X86.Pool.forget_ofPool p

/-- **A synchronising TSO step on an empty buffer is an SC step.** -/
theorem tsoStep_sync_sc [DecidableEq Tid] {M : EvMachine} {Fin : Tid → State → Prop}
    {p : TPool Tid} {t : Tid} {c c' : State} {i : M.Instr} {n : Nat} {mem' : Memory}
    (ht : p.threads t = some c) (hnf : ¬ Fin t c)
    (hf : M.fetch (overlay p.memory (p.buffer t)) c.rip.toNat = some (i, n))
    (he : p.buffer t = []) (hx : M.exec i c p.memory n = .ok c' mem') :
    SCStepF M.step Fin (forget p) t
      (forget { p with threads := Function.update p.threads t (some c'), memory := mem' }) :=
  Silmaril.Proofs.X86.Pool.tsoStep_sync_sc ht hnf hf he hx

/-! ## DRF -/

/-- **An `Ext` fetch of `openEv` depends only on its own bytes** (`FetchStable`). -/
theorem openFetch_stable {mem : Memory} {pc : Nat} {i : Silmaril.X86.Ext.Instr} {k : Nat}
    (h : Silmaril.X86.MemEvent.openFetch mem pc = some (.base i, k)) :
    FetchStable openEv mem pc (.base i) k :=
  Silmaril.Proofs.X86.Pool.openFetch_stable h

/-- **`Task.drfTso` holds**: a footprint-ownership-safe pool reaches, under the TSO pool
built from the access lists and the buffers, only drained states that the SC pool reaches. -/
theorem drfTso_holds : Task.drfTso :=
  Silmaril.Proofs.X86.Pool.drfTso

/-- **`Task.drfTso` without `FetchStable` is false** (the counterexample, `Pool/Counter.lean`).
`Counter.TaskFetch` is the frozen statement, whose footprint condition (`Counter.LSafeEvK`) has no
`FetchStable` conjunct. A machine whose fetch at one thread's second instruction reads a byte
the other thread owns, two threads `st x; set (fetched from y)` and `st y; set (fetched from x)`,
satisfies that hypothesis; under TSO both stores are buffered, both `set`s read `0`, and the
drained state with `rax = 0` in both threads is reached by no SC run. -/
theorem drfTso_noFetch_false : ¬ Silmaril.Proofs.X86.Pool.Counter.TaskFetch :=
  Silmaril.Proofs.X86.Pool.Counter.not_taskK

/-! ## Non-vacuity -/

namespace Example

open Silmaril.Proofs.X86.Pool.Example (retCode retPre retPost retFin codeAt spT spF retT retF
  pool fin)

/-- `ret` as a frame-requantified triple, the code as read-only context, every index. -/
theorem ret_ltriple (e s ret : Word) (hne : e ≠ ret) (n : Nat) :
    LTriple Silmaril.X86.Open.step (retFin ret) (codePt e.toNat retCode) (retPre e s ret)
      (retPost s ret) n :=
  Silmaril.Proofs.X86.Pool.Example.ret_ltriple e s ret hne n

/-- **The two-thread `ret` pool is ownership-safe.** -/
theorem two_ownershipSafe : OwnershipSafe Silmaril.X86.Open.step fin pool :=
  Silmaril.Proofs.X86.Pool.Example.two_ownershipSafe

/-- `ret` as a footprint triple on `openEv`: it fetches only the code and pops only its owned
return slot. -/
theorem ret_ltripleEv (e s ret : Word) (hne : e ≠ ret) (n : Nat) :
    LTripleEv openEv (retFin ret) (codePt e.toNat retCode) (retPre e s ret)
      (retPost s ret) n :=
  Silmaril.Proofs.X86.Pool.Example.ret_ltripleEv e s ret hne n

/-- **The two-thread `ret` pool is footprint-ownership-safe** (the hypothesis of
`Task.drfTso`). -/
theorem two_ownershipSafeEv : OwnershipSafeEv openEv fin pool :=
  Silmaril.Proofs.X86.Pool.Example.two_ownershipSafeEv

/-- **`par_shared_ro` on the two-thread `ret` pool.** -/
theorem two_poolSafe : ∃ F : PProp Bool,
    (atThread true (retPre codeAt spT retT) ∗ₚ atThread false (retPre codeAt spF retF) ∗ₚ
      atShared (codePt codeAt.toNat retCode) ∗ₚ F) (poolFrag pool) ∧
    ∀ n, PoolSafe Silmaril.X86.Open.step fin
      (fun p' => (atThread true (retPost spT retT) ∗ₚ atThread false (retPost spF retF) ∗ₚ
        atShared (codePt codeAt.toNat retCode) ∗ₚ F) (poolFrag p')) n pool :=
  Silmaril.Proofs.X86.Pool.Example.two_poolSafe

/-- **`Task.drfTso`, instantiated**: every drained state that the TSO pool over `Open.step`'s
access lists reaches from the two-thread `ret` pool is SC-reachable. -/
theorem drfTso_two (p : TPool Bool)
    (hr : TsoReach openEv fin (TPool.ofPool pool) p) (hd : Drained p) :
    SCReach Silmaril.X86.Open.step fin pool (forget p) := by
  have := @drfTso_holds Bool _ openEv fin pool two_ownershipSafeEv p hr hd
  rwa [openEv_step] at this

end Example

/-! ## The `right_rot` pool -/

namespace RightRot

open Silmaril.X86.Decompile.RightRot (code)
open Silmaril.Proofs.X86.Pool.Example (retFin)
open Silmaril.Proofs.X86.Pool.RightRotPool (rrPre rrPost pool fin)

/-- **`right_rot` as a footprint triple** (proved: `rightRotLocal_holds`). With its 37 code bytes
as the read-only context, the side conditions (`16 ≤ sp`, the frame apart from the code,
`0 < esi < 32`) and a return address outside the code, `right_rot` meets `LTripleEv` on `openEv`
(whose step is `Open.step`) for every step index, owning `RightRot.pre` without the code. The
stable triple `rightRot_tripleS` fixes the frame for the whole run; this statement
quantifies the unowned memory at every one of the fifteen steps and requires every fetch and
access to lie in the owned fragment or the code (and every fetch to be `FetchStable`). -/
def Task.rightRotLocal : Prop :=
  ∀ (e ret sp bp vdi vsi : Word), 16 ≤ sp.toNat →
    (e.toNat + 37 ≤ sp.toNat - 16 ∨ sp.toNat ≤ e.toNat) →
    0 < (vsi.setWidth 32).toNat → (vsi.setWidth 32).toNat < 32 →
    (ret.toNat < e.toNat ∨ e.toNat + 37 ≤ ret.toNat) →
    ∀ n, LTripleEv openEv (retFin ret) (codePt e.toNat code)
      (rrPre e ret sp bp vdi vsi) (rrPost ret sp bp vdi vsi) n

/-- **`Task.rightRotLocal` holds**: `right_rot` meets the footprint triple on `openEv`,
its code the read-only context, for every step index. The fifteen steps are replayed one at a
time on an arbitrary memory consistent with the owned fragment and the code
(`Pool/RightRotLocal.lean`). -/
theorem rightRotLocal_holds : Task.rightRotLocal :=
  Silmaril.Proofs.X86.Pool.RightRotLocal.rightRotLocal

/-- **Two `right_rot` threads on disjoint stacks are footprint-ownership-safe.** -/
theorem rightRot_two_ownershipSafeEv : OwnershipSafeEv openEv fin pool :=
  Silmaril.Proofs.X86.Pool.RightRotPool.rightRot_two_ownershipSafeEv rightRotLocal_holds

/-- **Two `right_rot` threads on disjoint stacks are ownership-safe.** -/
theorem rightRot_two_ownershipSafe : OwnershipSafe Silmaril.X86.Open.step fin pool :=
  Silmaril.Proofs.X86.Pool.RightRotPool.rightRot_two_ownershipSafe rightRotLocal_holds

/-- **DRF for the two-thread `right_rot` pool**: every drained state its TSO pool reaches is
SC-reachable. -/
theorem drfTso_rightRot (p : TPool Bool)
    (hreach : TsoReach openEv fin (TPool.ofPool pool) p) (hdr : Drained p) :
    SCReach Silmaril.X86.Open.step fin pool (forget p) := by
  have := @drfTso_holds Bool _ openEv fin pool rightRot_two_ownershipSafeEv p hreach hdr
  rwa [openEv_step] at this

end RightRot

end Silmaril.X86.Pool
