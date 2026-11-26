module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Refine
import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Solo
import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Static
import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Example
import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Review

/-!
# Process-level threads for CIR: theorems

Everything here is PROVED
with the standard axioms only; proofs are in `Silmaril/Proofs/X86/Concurrency/Cir/Proc/`.

## CIR sync is implemented by the thread syscalls

* **`refines`**: for a well-formed (`SProg.Wf`), sync-safe (`SProg.SyncSafe`) CIR program,
  every configuration the lowered process reaches (any main tid, thread pointer and base
  syscall relation) is related by `Rel` to a configuration the CIR sync machine reaches: the
  heaps agree outside the control cells, every process thread implements a started CIR thread
  (`Corr`/`Top`), and a control word is `0` only once its thread has finished. So `spawn` is
  `clone` (with musl's flag word, `CLONE_SETTLS`, `CLONE_PARENT_SETTID`,
  `CLONE_CHILD_CLEARTID`), `join` is the futex-wait loop on the cleared `ctl` word, and
  `futexWait`/`futexWake` are `FUTEX_WAIT_PRIVATE`/`FUTEX_WAKE_PRIVATE`.
* **`safety_transfer`**: user-heap invariants of the sync machine hold of the process.
* **`join_rule`**: a control word that reads `0` means its thread has finished.
* **`syncSafe_of_static`**: the syntactic conditions `SProg.Static` imply `SyncSafe`.
* `forkJoin_wf`, `forkJoin_static`, `forkJoin_refines`, `forkJoin_clone`: the hypotheses hold
  for `Ex.forkJoin`, and its lowered process takes the `clone` step.
* Further results: `forkJoin_result` (every reachable lowered fork-join process whose main
  thread is about to `exit_group` has `rax = 42`: proved on CIR, transferred by the
  refinement), `forkJoin_run` (such a state is reachable: the result is not vacuous) and
  `forkJoin_noJoin` (with `join 1` erased, `rax = 0` is reachable: the result depends on the
  futex join).

## Process rules (any user ISA)

* `clone_tp`: the `clone` rule (new thread, its thread pointer is `tls`, `ptid` written);
* `tp_stable`: thread pointers are per-thread constants of the run (the TLS reading);
* `ctid_stable`: `clear_child_tid` changes only at `set_tid_address`;
* `exited_stuck`: an exited process does not step.

## The single-threaded view

* `solo_init`, `solo_fwd`, `solo_bwd`, `solo_reach`: a one-thread process that never requests
  `clone`/`futex` is exactly the single-threaded machine `SoloStep`. With `Proc/Lps`, this is
  the bridge to LPS's single task.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap Star)

/-! ## Refinement -/

/-- **The lowered process refines the CIR sync semantics.** -/
theorem refines {P : SProg} {L : Layout} {base : Base} (hw : P.Wf) (hss : P.SyncSafe)
    (tid0 : Nat) (tp0 : Word) {C : PCfg (pIsa (P.code L)).St}
    (h : PReach (pIsa (P.code L)) base (P.pinit L tid0 tp0) C) :
    ∃ A, SReach P P.init A ∧ Rel P L C A :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.refines hw hss tid0 tp0 h

/-- **Safety transfer** for user-heap properties. -/
theorem safety_transfer {P : SProg} {L : Layout} {base : Base} (hw : P.Wf) (hss : P.SyncSafe)
    (tid0 : Nat) (tp0 : Word) (Q : Heap → Prop) (hQ : ∀ A, SReach P P.init A → Q (userHeap A.mem))
    {C : PCfg (pIsa (P.code L)).St} (h : PReach (pIsa (P.code L)) base (P.pinit L tid0 tp0) C) :
    Q (userHeap C.mem) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.safety_transfer hw hss tid0 tp0 Q hQ h

/-- **The join rule.** -/
theorem join_rule {P : SProg} {L : Layout} {base : Base} (hw : P.Wf) (hss : P.SyncSafe)
    (tid0 : Nat) (tp0 : Word) {C : PCfg (pIsa (P.code L)).St}
    (h : PReach (pIsa (P.code L)) base (P.pinit L tid0 tp0) C)
    {u : Nat} (h0 : 0 < u) (hu : u < P.N) (hz : C.mem (ctlAddr u) = some 0) :
    ∃ A, SReach P P.init A ∧ Rel P L C A ∧ A.started u = true ∧ (A.ts u).1 = .skip :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.join_rule hw hss tid0 tp0 h h0 hu hz

/-- **Static sync safety.** -/
theorem syncSafe_of_static {P : SProg} {D : List Nat} (hs : P.Static D) : P.SyncSafe :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.syncSafe_of_static hs

/-! ## Process rules -/

/-- **The `clone` rule.** -/
theorem clone_tp {I : UIsa} {base : Base} {C : PCfg I.St} {t : Nat} {r : TRec I.St} {s : I.St}
    {fl sp ptid ctid tls : Word} {args : List Word} {k : Word → I.St} {ch : I.St} {t' : Nat}
    (hl : C.status = none) (ht : C.th t = some r) (hr : r.st = .run s)
    (hs : I.step r.tp s (.sys nrClone (fl :: sp :: ptid :: ctid :: tls :: args) k ch))
    (hf : CloneOk fl) (hfresh : C.th t' = none) (h0 : 0 < t') (hmax : t' < pidMax)
    (hpt : (C.mem ptid.toNat).isSome) :
    ∃ C', PStep I base C C' ∧ C'.th t' = some ⟨.run ch, tls, some ctid.toNat⟩ ∧
      C'.mem ptid.toNat = some t' ∧
      (∃ r', C'.th t = some r' ∧ r'.st = .run (k (BitVec.ofNat 64 t'))) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.clone_tp hl ht hr hs hf hfresh h0 hmax hpt

/-- **Thread pointers are per-thread constants.** -/
theorem tp_stable {I : UIsa} {base : Base} {C C' : PCfg I.St} (h : PStep I base C C') {t : Nat}
    {r : TRec I.St} (ht : C.th t = some r) : ∃ r', C'.th t = some r' ∧ r'.tp = r.tp :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.tp_stable h ht

/-- **`clear_child_tid` changes only at `set_tid_address`.** -/
theorem ctid_stable {I : UIsa} {base : Base} {C C' : PCfg I.St} (h : PStep I base C C') {t : Nat}
    {r : TRec I.St} (ht : C.th t = some r)
    (hns : ∀ s a args k ch, r.st = .run s → ¬ I.step r.tp s (.sys nrSetTid (a :: args) k ch)) :
    ∃ r', C'.th t = some r' ∧ r'.ctid = r.ctid :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.ctid_stable h ht hns

/-- An exited process does not step. -/
theorem exited_stuck {I : UIsa} {base : Base} {C C' : PCfg I.St} {c : Nat}
    (hc : C.status = some c) (h : PStep I base C C') : False :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.exited_stuck hc h

/-! ## The single-threaded view -/

theorem solo_init {I : UIsa} (tid : Nat) (s : I.St) (tp : Word) (h : Heap) :
    SoloRel tid ⟨s, tp, h, none⟩ (PCfg.init tid s tp h) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.solo_init tid s tp h

theorem solo_fwd {I : UIsa} {base : Base} {tid : Nat} {x y : SoloCfg I.St} {C : PCfg I.St}
    (h : SoloRel tid x C) (hs : SoloStep I base tid x y) :
    ∃ C', PStep I base C C' ∧ SoloRel tid y C' :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.solo_fwd h hs

theorem solo_bwd {I : UIsa} {base : Base} {tid : Nat} {x : SoloCfg I.St} {C C' : PCfg I.St}
    (h : SoloRel tid x C) (hn : NoThreadSys I x.tp x.st) (hs : PStep I base C C') :
    ∃ y, SoloStep I base tid x y ∧ SoloRel tid y C' :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.solo_bwd h hn hs

/-- **Single-threaded processes are their single-threaded view.** -/
theorem solo_reach {I : UIsa} {base : Base} {tid : Nat} {x0 : SoloCfg I.St} {C0 : PCfg I.St}
    (h0 : SoloRel tid x0 C0)
    (hn : ∀ x, Star (SoloStep I base tid) x0 x → NoThreadSys I x.tp x.st) {C : PCfg I.St}
    (hr : Star (PStep I base) C0 C) : ∃ x, Star (SoloStep I base tid) x0 x ∧ SoloRel tid x C :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.solo_reach h0 hn hr

/-! ## The example -/

theorem forkJoin_wf : Ex.forkJoin.Wf := Silmaril.Proofs.X86.Concurrency.Cir.Proc.forkJoin_wf

theorem forkJoin_static : Ex.forkJoin.Static [Ex.x] :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.forkJoin_static

theorem forkJoin_refines (base : Base) (tid0 : Nat) (tp0 : Word)
    {C : PCfg (pIsa (Ex.forkJoin.code Ex.layout)).St}
    (h : PReach (pIsa (Ex.forkJoin.code Ex.layout)) base (Ex.forkJoin.pinit Ex.layout tid0 tp0) C) :
    ∃ A, SReach Ex.forkJoin Ex.forkJoin.init A ∧ Rel Ex.forkJoin Ex.layout C A :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.forkJoin_refines base tid0 tp0 h

theorem forkJoin_clone (base : Base) (tid0 : Nat) (h0 : tid0 + 1 < pidMax) (tp0 : Word) :
    ∃ C', PStep (pIsa (Ex.forkJoin.code Ex.layout)) base (Ex.forkJoin.pinit Ex.layout tid0 tp0) C' ∧
      (∃ r, C'.th (tid0 + 1) = some r ∧ r.tp = BitVec.ofNat 64 (Ex.layout.tls 1) ∧
        r.ctid = some (ctlAddr 1)) ∧ C'.mem (ctlAddr 1) = some (tid0 + 1) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.forkJoin_clone base tid0 h0 tp0

/-- **Fork-join, end to end**: once the main thread is about to call `exit_group`, its `rax`
holds the child's `42`. -/
theorem forkJoin_result (base : Base) (tid0 : Nat) (tp0 : Word)
    {C : PCfg (pIsa (Ex.forkJoin.code Ex.layout)).St}
    (h : PReach (pIsa (Ex.forkJoin.code Ex.layout)) base (Ex.forkJoin.pinit Ex.layout tid0 tp0) C)
    {r : TRec PSt} {rs : Regs} (ht : C.th tid0 = some r)
    (hr : r.st = .run (.seq .skip exitGroupS, rs)) : rs .rax = 42 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.forkJoin_result base tid0 tp0 h ht hr

/-- **Non-vacuity of `forkJoin_result`**: the lowered process does reach that point. -/
theorem forkJoin_run (base : Base) :
    ∃ C, PReach (pIsa (Ex.forkJoin.code Ex.layout)) base (Ex.forkJoin.pinit Ex.layout 1 0) C ∧
      ∃ rs, C.th 1 = some ⟨.run (.seq .skip exitGroupS, rs), 0, none⟩ ∧ rs .rax = 42 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.fj_run base

/-- **Mutant**: with `join 1` erased from the main thread's lowered code, `rax = 0` is
reachable at the same point. -/
theorem forkJoin_noJoin (base : Base) :
    ∃ C, PReach (pIsa (Ex.forkJoin.code Ex.layout)) base
        (PCfg.init 1 (.seq (.seq (spawnS Ex.layout 1)
          (.seq .skip (.cir (.load .rax .na 8 .wb (.lit Ex.x))))) exitGroupS, Regs.zero) 0
          Ex.forkJoin.pheap) C ∧
      ∃ rs, C.th 1 = some ⟨.run (.seq .skip exitGroupS, rs), 0, none⟩ ∧ rs .rax = 0 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.fj_noJoin_run base

end Silmaril.X86.Concurrency.Cir.Proc
