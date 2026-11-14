module

public import Silmaril.X86.MemoryModel.Tso.Defs
import Silmaril.Proofs.X86.MemoryModel.Tso.Litmus

/-!
# x86-TSO store-buffer models: theorems

PROVED (standard axioms only; byte-model proofs in `Silmaril.Proofs.X86.MemoryModel.Tso.Litmus`):

* Word-granular: `of_sc_execution` (SC embeds into
  FIFO TSO with empty buffers at observable boundaries), `store_buffering_allowed` (TSO admits
  the SB outcome that SC forbids, `sc_store_buffering_forbidden`) and `weak_fence_empty`.
* Byte-granular (new):
  - `sb_allowed`: SB without fences, both loads may read zero;
  - `sb_mfence_forbidden`: SB with `mfence` after each store, from **any** state with empty
    buffers and `x = y = 0`, no interleaving and no choice of flushes makes both loads read
    zero; `sb_mfence_r1_allowed` shows the fenced programs are executable (outcome
    `r0 = 0, r1 = 1`), so the prohibition is not vacuous;
  - `rmw_atomic` / `weak_rmw_atomic`: a locked RMW is one transition that reads and writes
    the same memory with the issuing buffer drained; around it only flushes occur, and none
    lies between its read and its write. `weak_rmw_empty`: it acts as a full fence;
  - `of_sc_x`: byte-granular SC executions embed into byte-granular TSO;
  - `readView_enqueue_same`: store forwarding of a whole span;
  - `concurrent_invariant`: the invariant principle for `Concurrent` used by the litmus
    proofs.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Tso

universe u

open Litmus

/-! ## Ported -/

theorem of_sc_execution {Tid Addr Val : Type u} [DecidableEq Tid] [DecidableEq Addr]
    {h h' : Silmaril.Memory.SC.Heap Addr Val} {es : List (Event Tid Addr Val)}
    (hs : Execution Silmaril.Memory.SC.Step h es h') :
    Execution WeakStep (Silmaril.Memory.TSO.embed h) es (Silmaril.Memory.TSO.embed h') :=
  Silmaril.Memory.TSO.of_sc_execution hs

theorem sc_store_buffering_forbidden :
    ¬ Concurrent Silmaril.Memory.SC.Step Silmaril.Memory.SC.Litmus.initial
      Silmaril.Memory.SC.Litmus.sbLeft Silmaril.Memory.SC.Litmus.sbRight :=
  Silmaril.Memory.SC.Litmus.store_buffering_forbidden

theorem store_buffering_allowed :
    Concurrent WeakStep Silmaril.Memory.TSO.Litmus.initial
      Silmaril.Memory.SC.Litmus.sbLeft Silmaril.Memory.SC.Litmus.sbRight :=
  Silmaril.Memory.TSO.Litmus.store_buffering_allowed

theorem weak_fence_empty {Tid Addr Val : Type u} [DecidableEq Tid] [DecidableEq Addr]
    {s s' : State Tid Addr Val} {t : Tid} (h : WeakStep s (.fence t) s') : s'.buffer t = [] :=
  Silmaril.Memory.TSO.weak_fence_empty h

/-! ## Byte-granular -/

theorem concurrent_invariant {S L : Type} {step : S → L → S → Prop}
    (P : List L → List L → S → Prop)
    (hl : ∀ x xs ys s s', P (x :: xs) ys s → step s x s' → P xs ys s')
    (hr : ∀ y xs ys s s', P xs (y :: ys) s → step s y s' → P xs ys s')
    {xs ys trace : List L} {s s' : S} (hm : trace ∈ Silmaril.Memory.shuffles xs ys)
    (h : Execution step s trace s') (hp : P xs ys s) : P [] [] s' :=
  Proofs.concurrent_invariant P hl hr xs ys trace s s' hm h hp

theorem sb_allowed : Concurrent XWeakStep xinitial sbLeft sbRight := Proofs.sb_allowed

theorem sb_mfence_forbidden (s₀ : XState Bool) (hb : ∀ t, s₀.buffer t = [])
    (hx : s₀.memory 0 = some 0) (hy : s₀.memory 1 = some 0) :
    ¬ Concurrent XWeakStep s₀ sbFenceLeft sbFenceRight :=
  Proofs.sb_mfence_forbidden s₀ hb hx hy

/-- Non-vacuity witness: the fenced SB programs run, with outcome `r0 = 0, r1 = 1`. -/
theorem sb_mfence_r1_allowed :
    Concurrent XWeakStep xinitial sbFenceLeft [.store true 1 [1], .fence true, .load true 0 [1]] :=
  Proofs.sb_mfence_r1_allowed

theorem sb_mfence_forbidden_initial : ¬ Concurrent XWeakStep xinitial sbFenceLeft sbFenceRight :=
  sb_mfence_forbidden xinitial (fun _ => rfl) rfl rfl

section
variable {Tid : Type} [DecidableEq Tid]

theorem rmw_atomic {s s' : XState Tid} {t : Tid} {a : Nat} {old new : List Byte} :
    XStep s (.rmw t a old new) s' ↔
      s.buffer t = [] ∧ readMem s.memory a old.length = some old ∧
        new.length = old.length ∧ s' = { s with memory := writeMem s.memory a new } :=
  Proofs.rmw_atomic

theorem weak_rmw_atomic {s s' : XState Tid} {t : Tid} {a : Nat} {old new : List Byte}
    (h : XWeakStep s (.rmw t a old new) s') :
    ∃ mid, XFlushes s mid ∧ mid.buffer t = [] ∧ readMem mid.memory a old.length = some old ∧
      new.length = old.length ∧ XFlushes { mid with memory := writeMem mid.memory a new } s' :=
  Proofs.weak_rmw_atomic h

theorem weak_rmw_empty {s s' : XState Tid} {t : Tid} {a : Nat} {old new : List Byte}
    (h : XWeakStep s (.rmw t a old new) s') : s'.buffer t = [] :=
  Proofs.weak_rmw_empty h

theorem weak_mfence_empty {s s' : XState Tid} {t : Tid}
    (h : XWeakStep s (.fence t) s') : s'.buffer t = [] :=
  Proofs.weak_fence_empty h

theorem of_sc_x {m m' : Mem} {es : List (XEvent Tid)} (h : Execution SCStep m es m') :
    Execution XWeakStep (xembed m) es (xembed m') :=
  Proofs.of_sc_x h

theorem readView_enqueue_same (s : XState Tid) (t : Tid) (a : Nat) (bs : List Byte) :
    readView (enqueue s t a bs) t a bs.length = some bs :=
  Proofs.readView_enqueue_same s t a bs

end

end Silmaril.X86.MemoryModel.Tso
