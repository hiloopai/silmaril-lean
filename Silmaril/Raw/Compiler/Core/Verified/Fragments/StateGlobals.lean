module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.StateGlobals.Defs
/-! # Fragment: a block of `int` statements over `int` globals and locals

`Fragments.state` with file-scope `int` globals initialised by literals: `main`'s block reads
and assigns them like its locals (`StateGlobals.recognize`). The globals start as slots of the
`int` state holding their initialisers; the statements compile to one closed expression that
the Lir code computes at run time in registers (`IntExpr.exprOps`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem stateGlobals_sound :
    Fragment.OpsSound StateGlobals.recognize (IntExpr.exprOps 0) (fun _ => 0) := by
  intro doc t ht args
  rcases StateGlobals.recognize_sound doc t ht args with ub | ⟨ok, beh⟩
  · exact .inl ub
  · refine .inr ⟨_, IntExpr.exprOps_exec ok, ?_⟩
    rw [Fragment.status_ofInt]
    exact beh

/-- `IntExpr.exprOps 0 T`, returning register 0 (`OpsLink.link`). -/
def stateGlobals : Fragment :=
  .ofOps StateGlobals.recognize (IntExpr.exprOps 0) (fun _ => 0) stateGlobals_sound

end Silmaril.Compile.Core.Verified.Fragments
