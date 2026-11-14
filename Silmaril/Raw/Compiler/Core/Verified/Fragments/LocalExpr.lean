module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.LocalExpr.Defs
/-! # Fragment: `{ int x = n; return e; }`

`e` is an `int` expression over literals and reads of `x` (`LocalExpr.recognize`); the Lir code
computes it at run time in registers (`IntExpr.exprOps`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem localExpr_sound :
    Fragment.OpsSound LocalExpr.recognize (fun x => IntExpr.exprOps x.1 x.2) (fun _ => 0) := by
  intro doc x hx args
  rcases LocalExpr.recognize_sound doc x.1 x.2 hx args with ub | ⟨ok, beh⟩
  · exact .inl ub
  · refine .inr ⟨_, IntExpr.exprOps_exec ok, ?_⟩
    rw [Fragment.status_ofInt]
    exact beh

/-- `IntExpr.exprOps n e`, returning register 0 (`OpsLink.link`). -/
def localExpr : Fragment :=
  .ofOps LocalExpr.recognize (fun x => IntExpr.exprOps x.1 x.2) (fun _ => 0) localExpr_sound

end Silmaril.Compile.Core.Verified.Fragments
