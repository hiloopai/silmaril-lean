module

public import Silmaril.Wasm.Wac.Example.Defs
public import Silmaril.Wasm.Wac.Profile.Thms
meta import Silmaril.Wasm.Wac.Example.Defs

/-!
# WAC: the worked composition, checked

Kernel-checked evaluations (`decide +kernel`) of `Silmaril.Wasm.Wac.Example`: the WAT text
is read in the composition profile and prints back; it lowers to the expected
composition graph; the composed component has the merged import `host#print` and
exports `run` from the environment slot `2`; promotion merges the unsatisfied imports;
plugging `greeter` into `app` wires `greeter#greet`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Example

open Silmaril.Wasm.Component

theorem profile_ast : Profile ast := by decide +kernel

/-- The text is the printing of the syntax; by the round trip on the profile it reads
back as the normal form of `ast`. -/
theorem readProfile_ast : readProfile (Wat.print ast) = some (Wat.norm ast) :=
  readProfile_print profile_ast

#guard Wat.print ast == text
#guard (readProfile text).map Wat.print == some (Wat.print ast)
#guard lowered == some expected

theorem composed_imports : composed.imports = [("host#print", ft)] := by decide +kernel

theorem composed_exports : composed.exports.map (·.impl) == [Impl.fwd 2] := by decide +kernel

theorem implicit_iface : (implicit.iface sigs).map Prod.fst = ["host#print"] := by decide +kernel

theorem implicit_explicate : implicit.explicate sigs = { expected with imports := [] } := by
  decide +kernel

theorem seq_nodes_ex : (greeterG.seq sigs appG).nodes =
    [⟨0, []⟩, ⟨1, [("greeter#greet", .out 0 "greet"), ("host#print", .imp "host#print")]⟩] := by
  decide +kernel

theorem seq_iface_ex : ((greeterG.seq sigs appG).iface sigs).map Prod.fst = ["host#print"] := by
  decide +kernel

end Silmaril.Wasm.Wac.Example
