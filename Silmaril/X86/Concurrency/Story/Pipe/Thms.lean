module

public import Silmaril.X86.Concurrency.Story.Pipe.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Xl.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Thms
import Silmaril.Proofs.X86.Concurrency.Story.Pipe.Client
import Silmaril.Proofs.X86.Concurrency.Story.Pipe.Wit

/-!
# A producer-consumer pipeline: theorems

PROVED, standard axioms only. Definitions and the protocol: `Story.Pipe.Defs`. Proofs:
`Silmaril/Proofs/X86/Concurrency/Story/Pipe/{Rules,Chan,Client}.lean`.

* **The channel's specification** (`send_spec`, `recv_spec`): `SafeR` triples of `send k vs[k]`
  and `recv k` under the channel invariant `Chan vs` framed with any other invariant `P`, from
  any pending flag. The producer's tokens go from `prodG k k` to `prodG (k + 1) (k + 1)`; the
  consumer's from `consG k k` to `consG (k + 1) (k + 1)`, and it ends with `out k = vs[k]` and
  the running sum advanced by `vs[k]`.
* **The ghost frame rule** (`safeR_gframe`), which composing these with the mutex interface
  needs.
* **The pipeline, proved once against the interface** (`pipe_any_mutexG`): for every tame mutex
  meeting the ghost-aware interface `Mutex.IfaceG` that fits an 8-byte slot and supports two
  threads, every loop bound, every spin bound and every list of values (`|vs| < 2 ^ 32`), every
  finished, drained state of CIR's TSO **and XL** store-buffer machines has `out k = vs[k]` for
  every `k` and `acc = |vs| + Σ vs` (mod `2 ^ 64`).
* **Instances**: the ticket lock (`pipe_ticket`), the spin lock with a plain-`mov` unlock
  (`pipe_spinMov`), and Drepper's futex mutex with its original unlock (`pipe_fmutexDec`).
* **Not vacuous** (`pipe_ticket_finishes`): with `vs = [5]` and the ticket lock, the explorer
  finds a finished, drained TSO run, which ends with `out 0 = 5` and `acc = 6`;
  `pipe_ticket_finishes2` does the same for `vs = [3, 4]`.

The composition is CSL's parallel composition: one `GInvR` certificate whose invariant is the
separating conjunction `gsep (M.inv m (R vs)) (Chan vs)` of the mutex's and the channel's
invariants, with each thread proved against the two specifications it uses (the channel's by
the invariant frame rule, the mutex's by the physical and ghost frame rules).

Scope: CIR's native operational machines (`OModel.tso`, `.xl`), not every axiomatic `M ⊑ XL`
(the mutex bodies address the lock through `rdi`, so no linked client is `uniformB`, which
`Csl.drf_behav` needs; as for `Story.Counter`). The `mfence` before each spin is needed by
`SafeR`'s side condition; that x86 does not need it is argued, not proved here.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Story.Pipe

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex

/-- **The ghost frame rule** for `SafeR`: ghost cells the thread never re-splits stay with it. -/
theorem safeR_gframe {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {p : Bool} {s : Stmt}
    {rs : Regs} {h g gF : Heap} (H : SafeR I Q p s rs h g) (hd : Heap.Disjoint g gF) :
    SafeR I (fun p rs h' g' => ∃ g1, Q p rs h' g1 ∧ Heap.Disjoint g1 gF ∧
      g' = Heap.union g1 gF) p s rs h (Heap.union g gF) :=
  Silmaril.Proofs.X86.Concurrency.Story.Pipe.safeR_gframe H hd

/-- **The channel's send**: `send k vs[k]` from the producer's tokens `prodG k k` and no channel
cells, under the channel invariant next to any `P`, from any flag; it ends with
`prodG (k + 1) (k + 1)` and no channel cells (and a pending release). -/
theorem send_spec {vs : List Nat} {P : GProp} {k B : Nat} {p : Bool} (hk : k + 1 < 2 ^ 64)
    (hv : vs.getD k 0 < 2 ^ 64) {rs : Regs} {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : ∀ rs', Q true rs' Heap.empty (prodG (k + 1) (k + 1))) :
    SafeR (gsep P (Chan vs)) Q p (send B k (vs.getD k 0)) rs Heap.empty (prodG k k) :=
  Silmaril.Proofs.X86.Concurrency.Story.Pipe.chan_lift
    (Silmaril.Proofs.X86.Concurrency.Story.Pipe.send_chan hk hv hQ)

/-- **The channel's receive**: `recv k` from the consumer's tokens `consG k k` and cells `hO`
(with `out k` and `sm`, without the payload), under the channel invariant next to any `P`, from
any flag; it ends with `out k = vs[k]`, `sm` and `rbx` advanced by `vs[k]`, and
`consG (k + 1) (k + 1)`. -/
theorem recv_spec {vs : List Nat} {P : GProp} {k B : Nat} {p : Bool} (hk : k + 1 < 2 ^ 64)
    (hx : vs.getD k 0 < 2 ^ 64) (hko : out k < 2 ^ 64) {rs : Regs} {hO : Heap}
    (hOd : hO cdat = none) (ho : (hO (out k)).isSome) (hs : (hO sm).isSome)
    {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : Q true (((rs.set .rax (BitVec.ofNat 64 (k + 1))).set .rcx
        (BitVec.ofNat 64 (vs.getD k 0))).set .rbx (rs .rbx + BitVec.ofNat 64 (vs.getD k 0)))
      (fun y => if y = sm then some (rs .rbx + BitVec.ofNat 64 (vs.getD k 0)).toNat
        else if y = out k then some (vs.getD k 0) else hO y)
      (consG (k + 1) (k + 1))) :
    SafeR (gsep P (Chan vs)) Q p (recv B k) rs hO (consG k k) :=
  Silmaril.Proofs.X86.Concurrency.Story.Pipe.chan_lift
    (Silmaril.Proofs.X86.Concurrency.Story.Pipe.recv_chan hk hx hko hOd ho hs hQ)

/-- **The pipeline is tame** (every store write-back). -/
theorem pipe_wb (vs : List Nat) (B : Nat) : (client vs B).WbIn :=
  Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipe_wb vs B

/-- **The pipeline, proved once against the ghost-aware mutex interface**, on CIR's TSO and XL
store-buffer machines: every message arrives in order (`out k = vs[k]`) and the mutex-protected
result is `|vs| + Σ vs`. -/
theorem pipe_any_mutexG (M : IfaceG) (hMw : M.WbCode) (hM : M.size ≤ 8) (hN : M.thrOk 2)
    {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length < 2 ^ 32) (B L : Nat)
    {model : OModel} {Cf : OCfg} (hr : OReach model 2 ((client vs B).linkG M L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Goal vs Cf.mem :=
  Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipe_linkG M hM hN hvs hn B L
    (Csl.Tame.reach_tso_of_wb
      (startWith_wb (pipe_wb vs B) (derived_wb (hMw L).1) (derived_wb (hMw L).2) _) hr) hd hf

/-- **With the ticket lock**, on TSO and XL. -/
theorem pipe_ticket {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length < 2 ^ 32)
    (B L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 ((client vs B).linkG ticketMutexG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Goal vs Cf.mem :=
  pipe_any_mutexG ticketMutexG ticketMutexG_wb (Nat.le_refl _) (show (2 : Nat) < 2 ^ 32 by decide)
    hvs hn B L hr hd hf

/-- **With the spin lock and its plain-`mov` unlock**, on TSO and XL. -/
theorem pipe_spinMov {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length < 2 ^ 32)
    (B L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 ((client vs B).linkG spinMovG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Goal vs Cf.mem :=
  pipe_any_mutexG spinMovG spinMovG_wb (Nat.le_refl _) trivial hvs hn B L hr hd hf

/-- **With Drepper's futex mutex and its original `fetch_sub` unlock**, on TSO and XL. -/
theorem pipe_fmutexDec {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length < 2 ^ 32)
    (B L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model 2 ((client vs B).linkG
      (Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceG.ofIfaceR Futex.fmutexDec) L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Goal vs Cf.mem :=
  pipe_any_mutexG _ (ofIfaceR_wb fmutexDec_wb) (Nat.le_refl _) trivial hvs hn B L hr hd hf

/-- **Non-vacuity**: the pipeline for `[5]` with the ticket lock (spin and loop bounds 2) has a
finished, drained TSO run (the explorer), ending with `out 0 = 5` and `acc = 1 + 5`. -/
theorem pipe_ticket_finishes : ∃ Cf : OCfg,
    OReach .tso 2 ((client [5] 2).linkG ticketMutexG 2).toO Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) ∧ Cf.mem acc = some 6 ∧ Cf.mem (out 0) = some 5 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 2)
    (c0 := Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipeC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipe_fin
  rw [Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipeC_cfg] at hr
  refine ⟨d.ocfg, hr, hd, hf, ?_⟩
  simpa [Silmaril.Proofs.X86.Concurrency.Story.Pipe.outsOk, Robust.CSt.ocfg] using hp

/-- **Non-vacuity with two messages**: the pipeline for `[3, 4]` with the ticket
lock (spin and loop bounds 2) has a finished, drained TSO run, ending with `out 0 = 3`,
`out 1 = 4` and `acc = 2 + 3 + 4`. The second send waits for the first acknowledgement. -/
theorem pipe_ticket_finishes2 : ∃ Cf : OCfg,
    OReach .tso 2 ((client [3, 4] 2).linkG ticketMutexG 2).toO Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) ∧ Cf.mem acc = some 9 ∧ Cf.mem (out 0) = some 3 ∧
      Cf.mem (out 1) = some 4 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 2)
    (c0 := Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipeC2) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipe_fin2
  rw [Silmaril.Proofs.X86.Concurrency.Story.Pipe.pipeC2_cfg] at hr
  refine ⟨d.ocfg, hr, hd, hf, ?_⟩
  simpa [Silmaril.Proofs.X86.Concurrency.Story.Pipe.outsOk2, Robust.CSt.ocfg, and_assoc]
    using hp

end Silmaril.X86.Concurrency.Story.Pipe
