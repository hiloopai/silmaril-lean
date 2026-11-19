module

public import Silmaril.Project.Shapes.Abi.Sse.Defs
public import Silmaril.Machine.Abi.Conformance.Sse.Add.Thms

/-! # The first SSE row, registered

`add_row` solves `silmaril.abi.sse.add` by `Silmaril.Machine.Abi.Conformance.Sse.Add.conforms`
(standard axioms). The row is about the default-environment subset of `sysvScalar` on the model
machine `Mach.str9L`; see `Silmaril.Project.Shapes.Abi.Sse.Defs`. -/

@[expose] public section

namespace Silmaril.Project.Shapes.Abi.Sse

/-- **`addsd; ret` conforms as `double add(double, double)`** (default-environment subset, model
machine `Mach.str9L`). -/
@[solves "silmaril.abi.sse.add"]
theorem add_row : silmaril.abi.sse.add :=
  Silmaril.Machine.Abi.Conformance.Sse.Add.conforms

end Silmaril.Project.Shapes.Abi.Sse

end

silmaril group silmaril.abi.sse
  (title := "ABI conformance on the SSE model machine Mach.str9L: default-environment subset of System V (real x86 needs Faithful, not proved)")
  (children := [silmaril.shapes.abi.conforms.sysv_scalar_default_env_str9l, silmaril.abi.sse.add])
