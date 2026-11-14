module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ArrBlock.Defs
/-! # Fragment: one local int array with constant-index stores and reads

Array cells are translated by scalar replacement; the generated integer
expression computes the result at runtime through the proved backend. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem arrBlock_sound :
    Fragment.OpsSound ArrBlock.recognize (IntExpr.exprOps 0) (fun _ => 0) := by
  intro doc t ht args
  rcases ArrBlock.recognize_sound doc t ht args with ub | ⟨ok, beh⟩
  · exact .inl ub
  · refine .inr ⟨_, IntExpr.exprOps_exec ok, ?_⟩
    rw [Fragment.status_ofInt]
    exact beh

/-- `IntExpr.exprOps 0 T`, returning register 0 (`OpsLink.link`). -/
def arrBlock : Fragment :=
  .ofOps ArrBlock.recognize (IntExpr.exprOps 0) (fun _ => 0) arrBlock_sound

end Silmaril.Compile.Core.Verified.Fragments
