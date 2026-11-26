module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Expected.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Typing.Expected

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

universe u v
variable {Base : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)]

theorem checkWithBindings_sound {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base) (external : Fin exits → Ty Base)
    (entry : BindingTypes (Ty Base)) (rows : Fin blocks → BindingTypes (Ty Base))
    (accepted : checkWithBindings graph captures internal external entry rows = true) :
    graph.HasType captures internal external :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.checkWithBindings_sound graph captures internal external entry rows accepted

theorem checkExpected_sound {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) (accepted : checkExpected graph captures internal external = true) :
    graph.HasType captures internal external :=
  checkWithBindings_sound graph captures internal external .empty (fun _ => .empty) accepted

end Silmaril.Isotope.Bridge.NamedFlat
