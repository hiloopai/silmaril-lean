module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ReturnExpr.Defs
/-! # Fragment: `return e;` reading no local

The `unseq` elaboration of `return 1+2;` (`ReturnExpr.recognize`), also under nested returning
`if` statements (`StmtIf`); the Lir code computes `e`, the tests and the selection at run time in
registers (`IntExpr.exprOps`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem returnExpr_sound :
    Fragment.OpsSound ReturnExpr.recognize (IntExpr.exprOps 0) (fun _ => 0) := by
  intro doc t ht args
  rcases ReturnExpr.recognize_sound doc t ht args with ub | ⟨ok, beh⟩
  · exact .inl ub
  · refine .inr ⟨_, IntExpr.exprOps_exec ok, ?_⟩
    rw [Fragment.status_ofInt]
    exact beh

/-- `IntExpr.exprOps 0 e`, returning register 0 (`OpsLink.link`). -/
def returnExpr : Fragment :=
  .ofOps ReturnExpr.recognize (IntExpr.exprOps 0) (fun _ => 0) returnExpr_sound

end Silmaril.Compile.Core.Verified.Fragments
