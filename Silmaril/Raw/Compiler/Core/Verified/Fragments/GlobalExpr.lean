module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.GlobalExpr.Defs
/-! # Fragment: `int` globals initialised by literals, `main` returning `e` over one of them

The Core startup runs the initialisers into live objects (`Globals.initial_reaches_body`) and
`main` is `return e;` with `e` reading one global (`GlobalExpr.recognize`); the Lir code keeps
the global in a register set to its initialiser and computes `e` at run time
(`IntExpr.exprOps`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem globalExpr_sound :
    Fragment.OpsSound GlobalExpr.recognize (fun x => IntExpr.exprOps x.1 x.2) (fun _ => 0) := by
  intro doc x hx args
  rcases GlobalExpr.recognize_sound doc x.1 x.2 hx args with ub | ⟨ok, beh⟩
  · exact .inl ub
  · refine .inr ⟨_, IntExpr.exprOps_exec ok, ?_⟩
    rw [Fragment.status_ofInt]
    exact beh

/-- `IntExpr.exprOps n e`, returning register 0 (`OpsLink.link`). -/
def globalExpr : Fragment :=
  .ofOps GlobalExpr.recognize (fun x => IntExpr.exprOps x.1 x.2) (fun _ => 0) globalExpr_sound

end Silmaril.Compile.Core.Verified.Fragments
