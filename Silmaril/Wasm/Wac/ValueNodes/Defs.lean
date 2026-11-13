module

public import Silmaril.Wasm.Wac.Lower.Defs

/-!
# WAC: value nodes have no reading in the function-level IR

A WAC composition has value nodes when a package imports or exports a component-model
*value* (`(import "v" (value u32))`): `new p { ... }` promotes the value import, `i.w` aliases a
value export. WAC text cannot write a value itself (`import v: u32` does not parse in wac
0.12.0). Values are the gated `cm-values` feature of the component model: `wasm-tools validate`
rejects them without `--features`, and wasmtime 50 does not run them
(`tools/wac/tests/differential.sh`, cases `value-*`).

The function-level IR (`Silmaril.Wasm.Component`) has functions only; a value is neither a
function nor an instance of functions. The composition graph the bytes are read as
(`Lower.graph`) is **undefined** for a composition with a value import or a value export
(`Silmaril.Wasm.Wac.ValueNodes.Thms`): no algebra term can be the reading of such a binary. This is
the restatement of the open item "value nodes as algebra terms": refuted for the IR as it is;
it needs an IR whose interfaces carry values (outside this track). `Bridge.NoValue`, checked
by the tool (`EndToEnd.noValues`), is therefore the exact domain of the end-to-end theorems.

* `HasValueImport c`, `HasValueExport c`: a top-level import of a value, an export of a value.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.ValueNodes

open Silmaril.Wasm.Component.Binary

/-- A top-level import of a value. -/
def HasValueImport (c : Ast) : Prop :=
  ∃ xs i b, Section.imports xs ∈ c.sections ∧ i ∈ xs ∧ i.desc = .value b

/-- A top-level export of a value. -/
def HasValueExport (c : Ast) : Prop :=
  ∃ xs e, Section.exports xs ∈ c.sections ∧ e ∈ xs ∧ e.item.sort = .value

end Silmaril.Wasm.Wac.ValueNodes
