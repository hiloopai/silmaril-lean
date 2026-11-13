module

public import Silmaril.Wasm.Wac.LowerTExample.Defs
public import Silmaril.Wasm.Wac.LowerWF.Thms

/-!
# WAC: the typed lowering on the worked composition, checked

By kernel evaluation: `astT` lowers to `Example.expected`; the untyped example `ast`
is rejected by the typed lowering. With `graph_wf` and `graph_iface`, the lowered graph
is well formed and its composed component imports `host#print` at `() -> u32`;
`astUnit` (`print: func()`) is rejected: its instantiation arguments are ill typed.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.LowerTExample

open Silmaril.Wasm.Component

theorem graph_astT : (LowerT.graph Example.sigs astT).toOption = some Example.expected := by
  decide +kernel

theorem graph_ast_rejected : (LowerT.graph Example.sigs Example.ast).toOption = none := by
  decide +kernel

theorem graph_astUnit_rejected : (LowerT.graph Example.sigs astUnit).toOption = none := by
  decide +kernel

theorem graph_astT_ok : LowerT.graph Example.sigs astT = .ok Example.expected := by
  have h := graph_astT
  revert h
  cases LowerT.graph Example.sigs astT <;> simp [Except.toOption]

theorem expected_wf : Example.expected.WF Example.sigs := LowerT.graph_wf graph_astT_ok

end Silmaril.Wasm.Wac.LowerTExample
