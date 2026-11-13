module

public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Thms
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Tame

/-!
# Tame programs on XL, and the release rule on XL

Everything here is PROVED (standard axioms
only).

* **`reach_tso_of_wb`**: from a start whose threads pass the syntactic check `Stmt.wbStores`
  (every `store` write-back), every configuration reachable on either buffered machine
  (`OModel.tso` or `.xl`) is reachable on TSO. With `Csl.tso_reach_xl` (TSO's runs are XL's), the
  two machines have the same runs from a tame start. This is the operational form of
  `Exec.xl_iff_tso_of_tame`.
* **`rel_wb`, `rel_wbG`: the release rule of `Csl.Rel` is sound on every buffered model**
  (`M ⊑ XL`, that is `M = .tso` or `M = .xl`) for tame programs: `rel_tso`'s and `rel_tsoG`'s
  conclusions at every finished, drained configuration of `OStep M`. In particular a plain
  write-back store (`mov`) is a release on XL when the program issues no `nt`/`str` store.
* `wbStores_setB`, `wbStores_chain`: the check is blind to loop bounds and is a conjunction over
  chains, so it is decided once for a certificate's code, for every loop bound.

**Why the side condition.** The release rule's soundness argument needs the released store to
leave the buffer after every earlier store of the thread. On XL a write-back store may pass an
earlier `nt`/`str` store (`Ent.passes`), so a weak store in a critical section could become
visible after the unlock that publishes it. `Csl.Tame.Litmus.wb_needed` shows it on message
passing: with an `nt` data store before a release flag store, XL reaches a final state (flag seen,
data not) that TSO does not, so `reach_tso_of_wb` cannot drop its hypothesis.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Csl.Tame

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel

/-- Setting loop bounds does not change the check. -/
theorem wbStores_setB (L : Nat) (s : Stmt) : (TvCfg.setB L s).wbStores = s.wbStores :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Tame.wbStores_setB L s

/-- The check of a chain is the conjunction of the checks. -/
theorem wbStores_chain (l : List Stmt) : (Tv.chain l).wbStores = l.all Stmt.wbStores :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Tame.wbStores_chain l

/-- A certificate's code passes the check for every loop bound once it passes it for the
unbounded chain. -/
theorem wbStores_gcert (c : TvCfg.GCert) (L : Nat) :
    (c.body L).wbStores = (Tv.chain c.start).wbStores :=
  wbStores_setB L _

/-- **One XL step of a tame configuration is a TSO step** (to a tame configuration). -/
theorem step_tso_of_wb {N : Nat} {C D : OCfg} (h : OStep .xl N C D) (hw : C.Wb N) :
    OStep .tso N C D ∧ D.Wb N :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Tame.step_tso h hw

/-- **Tame programs: every buffered model's runs are TSO runs.** -/
theorem reach_tso_of_wb {M : OModel} {N : Nat} {C0 : Cfg} {C : OCfg} (hw : C0.WbStores N)
    (h : OReach M N C0.toO C) : OReach .tso N C0.toO C :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Tame.reach_tso_of_wb hw h

/-- **Tame programs: XL and TSO have the same runs.** -/
theorem reach_xl_iff_tso {N : Nat} {C0 : Cfg} {C : OCfg} (hw : C0.WbStores N) :
    OReach .xl N C0.toO C ↔ OReach .tso N C0.toO C :=
  ⟨reach_tso_of_wb hw, tso_reach_xl⟩

variable {I : GProp}

/-- **The release rule on every buffered model, for tame programs.** `rel_tso`'s conclusion at
every finished, drained configuration of `OStep M` (`M = .tso` or `.xl`), provided every thread
of the start passes `Stmt.wbStores`. -/
theorem rel_wb {Q : Nat → Bool → Regs → Heap → Heap → Prop} {N : Nat} {G0 : Heap} {C0 : Cfg}
    {hs gs : Nat → Heap} {hI gI : Heap} (G : GInvR I Q N C0 hs gs hI gI)
    (hG0 : ∀ c, (G0 c).isSome → (gI c).isSome ∨ ∃ t < N, (gs t c).isSome)
    (hw : C0.WbStores N) {M : OModel}
    {C : OCfg} (hr : OReach M N C0.toO C) (hd : C.Drained)
    (hf : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps' : Nat → Bool),
      (∀ t < N, Q t (ps' t) (C.ts t).2 (hs' t) (gs' t)) ∧ I hI' gI' ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ c, (G0 c).isSome → (gI' c).isSome ∨ ∃ t < N, (gs' t c).isSome) :=
  rel_tso G hG0 (reach_tso_of_wb hw hr) hd hf

/-- **`rel_tsoG` on every buffered model, for tame programs.** -/
theorem rel_wbG {Q : Nat → Bool → Regs → Heap → Heap → Prop} {N : Nat} {G0 : Heap} {C0 : Cfg}
    {hs gs : Nat → Heap} {hI gI : Heap} (G : GInvR I Q N C0 hs gs hI gI)
    (hG0 : ∀ c, (G0 c).isSome → (gI c).isSome ∨ ∃ t < N, (gs t c).isSome)
    (hw : C0.WbStores N) {M : OModel}
    {C : OCfg} (hr : OReach M N C0.toO C) (hd : C.Drained)
    (hf : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps' : Nat → Bool),
      (∀ t < N, Q t (ps' t) (C.ts t).2 (hs' t) (gs' t)) ∧ I hI' gI' ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ t u, t ≠ u → Heap.Disjoint (gs' t) (gs' u)) ∧ (∀ t, Heap.Disjoint (gs' t) gI') ∧
      (∀ c, (G0 c).isSome → (gI' c).isSome ∨ ∃ t < N, (gs' t c).isSome) :=
  rel_tsoG G hG0 (reach_tso_of_wb hw hr) hd hf

end Silmaril.X86.Concurrency.Cir.Csl.Tame
