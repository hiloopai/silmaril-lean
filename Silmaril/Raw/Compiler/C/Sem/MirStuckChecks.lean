module

public import Silmaril.Compiler.C.Sem.InterpCounterexample.Defs
@[expose] public section

/-! # A stuck run whose image does not fit

The unrestricted stuck target must handle the earlier counterexample's zero-sized
memory. An unwritten-register return gets stuck in both semantics even though
their inaccessible image bytes differ.
-/

namespace Silmaril.Compile.Mir.StuckChecks

open Silmaril.Machine
open InterpCounterexample (cfg units linked mem link_eq)

attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'

def term : Lir.Term Nat := .ret [.reg 0]

theorem run_stuck : run cfg 1 (units term) =
    .ok (.stuck "return of an unwritten location" ⟨0,0,0⟩ mem) := by
  rw [run, link_eq]
  cbv

theorem beh_univ : beh cfg (units term) = Set.univ := by
  rw [beh_eq_link cfg _ _ (link_eq term)]
  change ubClose {o | (Lir.sem (linked term).prog).Beh
    ⟨⟨0,0,0⟩,.empty,[],Mir.initMem cfg (linked term)⟩ o} = Set.univ
  apply ubClose_of_undefined
  change (Lir.sem (linked term).prog).Beh
    ⟨⟨0,0,0⟩,.empty,[],Mir.initMem cfg (linked term)⟩ (.undefined : Mir.LirOutcome)
  refine Behaviour.Semantics.Beh.of_final ?_ (by intro h; cases h)
  rfl

end Silmaril.Compile.Mir.StuckChecks
