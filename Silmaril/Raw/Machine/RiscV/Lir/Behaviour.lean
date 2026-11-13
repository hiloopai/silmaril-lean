module

public import Silmaril.Machine.RiscV.Lir.Loader.Defs
public import Silmaril.Machine.RiscV.Ext.Behaviour.Defs
public import Silmaril.Machine.CBackend.Lir.Backend.Defs
/-!
# The RV64 backend as a refinement

`compile_refines` restates `compile_correct` in the behaviour layer:
for a program accepted by `compile` and a layout satisfying `Space.Valid`, the
machine `RiscV.Ext.sem` with the stub convention at the halt, trap and overflow
stubs of the compiled code refines the Lir semantics `Lir.sem p` in the mode
`⟨.strict, .allowed⟩`, from every loaded state `loadState S img.code p f args
lm` paired with the Lir start state of the same call.

The observation relates

* a returned machine state `m` (at the halt stub) to Lir values and memory
  `(vs, mem)` by `Returned A p S img.slots vs mem m`: the values in `a0 …` and
  `mem` at `memBase`;
* a trapped machine state `m` (at the trap stub) to a Lir trap memory `mem` by
  `Trapped A p S img.slots mem m`;
* no fault to anything (Lir has none).

A stop at the overflow stub is exhaustion, which implements every source
outcome, so nothing is claimed for runs that reach it.

`compile_refines_bounded` restates `compile_correct_bounded` in the mode
`⟨.strict, .forbidden⟩`: from start states whose reachable Lir states have at
most `D` suspended activations, with room for `D + 1` frames, no machine
behaviour is exhaustion. The bound `D` is a premise; nothing here computes it.

The stub addresses are distinct (`stubs_distinct`), so the target's final
outcomes at the halt and trap stubs are the return and the trap. Both theorems
are `Lir.Backend.refines_of_correct` and `refines_of_exact` applied to the
existing forward theorems.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.RiscV.Ext (MState)
open Machine.Lir (Prog)
open Machine.Behaviour (Refines)
open Relation

variable {P : Type}

section Classify

variable {A : Assign P} {p : Prog P} {S : Space} {N : Nat}
  (hv : S.Valid (emitProg A.reg N p).length)
include hv

/-- A state at the halt stub shows the return of that state. -/
theorem Returned.final {vs : List Word} {mem : Machine.Lir.Memory} {m : MState}
    (h : Returned A p S N vs mem m) :
    Ext.FinalOutcome (addrOf S.codeBase haltIdx) (addrOf S.codeBase trapIdx)
      (addrOf S.codeBase overflowIdx) m (.returned m) :=
  .returned (Returned.stopped hv h) h.2.1

/-- A state at the trap stub shows the trap of that state. -/
theorem Trapped.final {mem : Machine.Lir.Memory} {m : MState} (h : Trapped A p S N mem m) :
    Ext.FinalOutcome (addrOf S.codeBase haltIdx) (addrOf S.codeBase trapIdx)
      (addrOf S.codeBase overflowIdx) m (.trapped m) :=
  .trapped (Trapped.stopped hv h) h.2.1 (h.2.1 ▸ (stubs_distinct hv).1.symm)

/-- A state at the overflow stub shows exhaustion. -/
theorem Overflowed.final {m : MState} (h : Overflowed A p S N m) :
    Ext.FinalOutcome (addrOf S.codeBase haltIdx) (addrOf S.codeBase trapIdx)
      (addrOf S.codeBase overflowIdx) m .exhausted :=
  .exhausted (Overflowed.stopped hv h) h.2 (h.2 ▸ (stubs_distinct hv).2.1.symm)
    (h.2 ▸ (stubs_distinct hv).2.2.symm)

end Classify

variable [DecidableEq P]

/-- **The RV64 backend as a refinement.** For a program accepted by `compile`
and a valid layout, the machine with the stub convention at the halt, trap and
overflow stubs refines the Lir program, from every loaded state paired with
the Lir start state of the same call, up to exhaustion at the overflow stub. -/
theorem compile_refines {A : Assign P} {p : Prog P} {img : Image} (hcomp : compile A p = .ok img)
    {S : Space} (hv : S.Valid img.code.length) :
    Refines ⟨.strict, .allowed⟩
      (Ext.sem (addrOf S.codeBase haltIdx) (addrOf S.codeBase trapIdx)
        (addrOf S.codeBase overflowIdx))
      (Machine.Lir.sem p)
      (fun t s => ∃ f args lm, lm.size = S.memSize ∧ p.start f args lm = some s ∧
        t = loadState S img.code p f args lm)
      (fun _ _ => ⟨fun m (vs, mem) => Returned A p S img.slots vs mem m,
        fun m mem => Trapped A p S img.slots mem m, fun _ e => e.elim⟩) := by
  have hv' : S.Valid (emitProg A.reg img.slots p).length := (compile_ok hcomp).1 ▸ hv
  refine Machine.Lir.Backend.refines_of_correct Ext.sem_deterministic
    (Returned A p S img.slots) (Trapped A p S img.slots) (Overflowed A p S img.slots)
    (fun _ _ _ _ _ m h => ⟨m, Returned.final hv' h, h⟩)
    (fun _ _ _ _ m h => .inl ⟨m, Trapped.final hv' h, h⟩)
    (fun _ h => Overflowed.final hv' h) ?_ ?_ ?_
  · rintro - s ⟨f, args, lm, hsize, hs, rfl⟩
    exact (compile_correct hcomp hv hsize hs).1
  · rintro - s ⟨f, args, lm, hsize, hs, rfl⟩
    exact (compile_correct hcomp hv hsize hs).2.1
  · rintro - s ⟨f, args, lm, hsize, hs, rfl⟩
    exact (compile_correct hcomp hv hsize hs).2.2

/-- **The RV64 backend as a refinement without exhaustion, under a call-depth
bound.** From loaded states whose Lir start state has at most `D` suspended
activations in every reachable state, with room for `D + 1` frames in the
stack region, the machine refines the Lir program with exhaustion forbidden. -/
theorem compile_refines_bounded {A : Assign P} {p : Prog P} {img : Image}
    (hcomp : compile A p = .ok img) {S : Space} (hv : S.Valid img.code.length) {D : Nat}
    (hD : S.stackLo + (D + 1) * frameSize img.slots ≤ S.stackHi) :
    Refines ⟨.strict, .forbidden⟩
      (Ext.sem (addrOf S.codeBase haltIdx) (addrOf S.codeBase trapIdx)
        (addrOf S.codeBase overflowIdx))
      (Machine.Lir.sem p)
      (fun t s => ∃ f args lm, lm.size = S.memSize ∧ p.start f args lm = some s ∧
        DepthBounded p s D ∧ t = loadState S img.code p f args lm)
      (fun _ _ => ⟨fun m (vs, mem) => Returned A p S img.slots vs mem m,
        fun m mem => Trapped A p S img.slots mem m, fun _ e => e.elim⟩) := by
  have hv' : S.Valid (emitProg A.reg img.slots p).length := (compile_ok hcomp).1 ▸ hv
  refine Machine.Lir.Backend.refines_of_exact Ext.sem_deterministic
    (Returned A p S img.slots) (Trapped A p S img.slots)
    (fun _ _ _ _ _ m h => ⟨m, Returned.final hv' h, h⟩)
    (fun _ _ _ _ m h => ⟨m, Trapped.final hv' h, h⟩) ?_ ?_ ?_
  · rintro - s ⟨f, args, lm, hsize, hs, hb, rfl⟩
    exact (compile_correct_bounded hcomp hv hsize hs hb hD).1
  · rintro - s ⟨f, args, lm, hsize, hs, hb, rfl⟩
    exact (compile_correct_bounded hcomp hv hsize hs hb hD).2.1
  · rintro - s ⟨f, args, lm, hsize, hs, hb, rfl⟩
    exact (compile_correct_bounded hcomp hv hsize hs hb hD).2.2

end Silmaril.RiscV.Backend
