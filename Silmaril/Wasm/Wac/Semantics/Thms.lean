module

public import Silmaril.Wasm.Wac.World.Thms
public import Silmaril.Wasm.Wac.WorldExample.Thms
public import Silmaril.Wasm.Wac.LowerWF.Thms
public import Silmaril.Wasm.Wac.LowerTExample.Thms
public import Silmaril.Wasm.Wac.Nest.Thms
public import Silmaril.Wasm.Wac.NestInline.Thms

/-!
# WAC: semantics, an earlier step

See `docs/projects/wasm-components.md`.

* `Silmaril.Wasm.Wac.World`: typed targets checking as world satisfaction (WIT subtyping of
  the composition's component type and the target world's), the composition's world
  derived from the composition graph; relations to `Targets.Fits` and to the
  elaborator's `TargetOk`;
* `Silmaril.Wasm.Wac.WorldExample`: the worked composition against three worlds;
* `Silmaril.Wasm.Wac.LowerT`: the typed lowering of profile WAT to composition graphs
  (WAT function types as `FuncTy`, typed instantiation arguments) and the relational
  specification of the profile's index spaces it meets (`graph_spec`);
* `Silmaril.Wasm.Wac.LowerWF`: its graphs are well formed (`graph_wf`) and the composed
  component's imports are the declared, typed imports (`graph_iface`);
* `Silmaril.Wasm.Wac.LowerTExample`: the worked composition, typed;
* `Silmaril.Wasm.Wac.Nest`: inlining of compositions, checked on an example;
* `Silmaril.Wasm.Wac.NestInline`: nesting = inlining, with sorted imports (`nest_inline`).
-/
