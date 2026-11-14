module

public import Silmaril.Automata.Registry.Defs
public import Silmaril.Wasm.Cfg.Thms

/-!
# The `sil project` self-test: control-flow graphs of Wasm functions as machine documents

The CFGs that `Silmaril.Wasm.Cfg.ofExpr` extracts from example functions, written as machine
documents (`silmaril/machines/wasm-cfg.toml`): a state per CFG node (named `<index> <instruction>
@<path>`, or `exit`, `trap`, `raise`, `invalid`), one label `flow`, the entry as the initial state,
`exit` accepting and `trap`, `raise`, `invalid` as error states. Loading them makes the registry
prove each document's immediate-dominator table (`<name>.dominators`), so the explorer draws the
flat CFG and its kernel-checked dominator tree with the machine views.

`*_extracted` proves in the kernel that each document has the extraction's nodes and exactly its
edges (by node index), so the explorer's graph is the Lean extractor's output, not a separate
drawing; the node names are presentation (the kernel does not evaluate string formatting).
-/

namespace ProjectSelfTest.WasmCfg

@[expose] public section

open Silmaril.Automata Silmaril.Wasm.Cfg

/-- The name of a CFG node. -/
def nodeName (c : FuncCfg) (n : Nat) : String :=
  match c.kinds[n]? with
  | some (.instr p name) => s!"{n} {name} @{p}"
  | some .exit => "exit" | some .trap => "trap" | some .raise => "raise"
  | some .invalid => "invalid" | none => s!"{n}"

/-- A CFG as a machine spec: nodes are states, every edge is labelled `flow`. -/
def cfgSpec (c : FuncCfg) : Spec where
  states := (List.range c.graph.size).map (nodeName c)
  labels := ["flow"]
  edges := c.edges.map fun (a, b) => ⟨nodeName c a, "flow", nodeName c b⟩

/-- A CFG as a machine document. -/
def cfgDoc (id : String) (c : FuncCfg) : Document where
  id := id
  spec := cfgSpec c
  layers := ⟨[nodeName c c.graph.entry], ["exit"], [], ["trap", "raise", "invalid"]⟩

end

end ProjectSelfTest.WasmCfg

silmaril load "silmaril/machines/wasm-cfg.toml"

namespace ProjectSelfTest.WasmCfg

open Silmaril.Automata Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Examples

/-- The document's edges as pairs of state positions (node indices). -/
@[expose] public def edgeIndices (d : Document) : List (Nat × Nat) :=
  d.spec.edges.map fun e => (d.spec.states.idxOf e.src, d.spec.states.idxOf e.dst)

/-! Each document has the extraction's nodes and exactly its edges, by node index
(kernel-checked; the node names are presentation). -/

public theorem sum_extracted :
    silmaril.wasm.cfg.verified.sum.spec.states.length = (ofExpr sum).graph.size ∧
      edgeIndices silmaril.wasm.cfg.verified.sum = (ofExpr sum).edges := by decide +kernel
public theorem dispatch_extracted :
    silmaril.wasm.cfg.dispatch.spec.states.length = (ofExpr dispatch).graph.size ∧
      edgeIndices silmaril.wasm.cfg.dispatch = (ofExpr dispatch).edges := by decide +kernel
public theorem specials_extracted :
    silmaril.wasm.cfg.specials.spec.states.length = (ofExpr specials).graph.size ∧
      edgeIndices silmaril.wasm.cfg.specials = (ofExpr specials).edges := by decide +kernel
public theorem doorEnter_extracted :
    silmaril.wasm.cfg.rust_door.enter.spec.states.length = (ofExpr doorEnter).graph.size ∧
      edgeIndices silmaril.wasm.cfg.rust_door.enter = (ofExpr doorEnter).edges := by decide +kernel

end ProjectSelfTest.WasmCfg
