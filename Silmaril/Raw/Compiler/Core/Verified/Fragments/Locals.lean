module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.LocalsDoc.Defs
/-! # Fragment: one `int` local initialised by a literal

`{ int x = n; return x; }` or `{ int x = n; }` (`Locals.recognize`); the Lir code keeps the
local in a register (`Locals.ops`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem locals_sound :
    Fragment.OpsSound Locals.recognize (fun x => Locals.ops x.1 x.2) (fun _ => 0) := by
  intro doc x hx args
  refine .inr ⟨_, Locals.ops_exec x.1 x.2, ?_⟩
  rw [Fragment.status_ofInt]
  exact Locals.recognize_sound doc x.1 x.2 hx args

/-- `Locals.ops`, returning register 0 (`OpsLink.link`). -/
def locals : Fragment :=
  .ofOps Locals.recognize (fun x => Locals.ops x.1 x.2) (fun _ => 0) locals_sound

end Silmaril.Compile.Core.Verified.Fragments
