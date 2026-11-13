module

public import Silmaril.Compiler.Semantics.MirRTL.Defs
@[expose] public section

/-!
# Approved target statements for the RTL / RTL.SSA zoo

Only the Lir-to-RTL lift and the local copy-propagation lemma are targets.
The end-to-end composition results remain ordinary library lemmas.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Machine Silmaril.Compile.Category Silmaril.Compile.Semantics

/-- Lifting a register-only Lir program to RTL refines it. -/
def lir_rtl_lift_refines : Prop :=
  ∀ q : Mir.LirProgram, RTL.Prog.RegOnly q.prog → (ofLirProg q).beh ⊆ q.beh

/-- The local lemma of copy propagation, from every start state. -/
def ssa_copyProp_behaves : Prop :=
  ∀ {R : Type} [DecidableEq R] (p : RTL.SSA.Prog R) (f : RTL.FuncId) (args : List Lir.Word)
    (mem : Lir.Memory) (s : RTL.SSA.State R), p.start f args mem = some s →
    ∀ b, RTL.SSA.Behaves (RTL.SSA.CopyProp.copyProp p) s b ↔ RTL.SSA.Behaves p s b

end Silmaril.Compile.Targets
