module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.State.Defs
/-! # Fragment: a block of `int` locals and statements

`int` locals created at the start of `main`'s block, then `int x;`, `int x = e;`, `x = e;`,
`if (c) return e;` and `return e;` (`State.recognize`). The assignments and selections are
compiled to one closed expression; the Lir code computes it at run time in registers
(`IntExpr.exprOps`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem state_sound :
    Fragment.OpsSound State.recognize (IntExpr.exprOps 0) (fun _ => 0) := by
  intro doc t ht args
  rcases State.recognize_sound doc t ht args with ub | ⟨ok, beh⟩
  · exact .inl ub
  · refine .inr ⟨_, IntExpr.exprOps_exec ok, ?_⟩
    rw [Fragment.status_ofInt]
    exact beh

/-- `IntExpr.exprOps 0 T`, returning register 0 (`OpsLink.link`). -/
def state : Fragment :=
  .ofOps State.recognize (IntExpr.exprOps 0) (fun _ => 0) state_sound

end Silmaril.Compile.Core.Verified.Fragments
