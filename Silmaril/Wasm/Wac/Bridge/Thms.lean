module

public import Silmaril.Wasm.Wac.Bridge.Text.Thms
public import Silmaril.Wasm.Wac.Bridge.Encode.Thms
public import Silmaril.Wasm.Wac.Bridge.Graph.Thms
public import Silmaril.Wasm.Wac.Bridge.Compose.Defs

/-!
# WAC: the bridges of the pipeline

See `docs/projects/wasm-components.md` ("The bridge").

* `Silmaril.Wasm.Wac.Bridge.Text`: the text AST (`Wac.Text`) as the elaboration AST
  (`Wac.Syntax`): `ofDoc`, a bijection on expressions (`ofExpr_toExpr`,
  `toExpr_ofExpr`), acceptance exactly `okDoc` (`ofDoc_isOk`), statement by statement
  (`ofDoc_ok`);
* `Silmaril.Wasm.Wac.Bridge.Encode`: the elaborator's graphs (`CGraph`) as component WAT in
  the composition profile, kinds encoded as component types (`encode`,
  `encode_profile`);
* `Silmaril.Wasm.Wac.Bridge.Graph`: the direct translation to the IR's composition graphs
  (`toGraph`) and the agreement `lower_encode : Lower.graph S c = .ok (toGraph S g)`;
* `Silmaril.Wasm.Wac.Bridge.Decode`: packages from component binaries (for the tool);
* `Silmaril.Wasm.Wac.Bridge.Compose`: the pipeline of `wasm-wac compose`.
-/
