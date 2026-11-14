module

public import Silmaril.Automata.Registry.Defs
public import Silmaril.Wasm.Cfg.BlockCfg.Thms
public import Silmaril.Wasm.Cfg.Examples.Defs

/-!
# The `sil project` self-test: basic-block CFGs of Wasm functions as machine documents

The basic-block CFGs that `Silmaril.Wasm.Cfg.blockCfg` builds from example functions, written as
machine documents (`silmaril/machines/wasm-block-cfg.toml`). There is one state per node:
- `exit`, `trap`, `raise` and `invalid` come first;
- then one state per block, in `blocks` order, named
  `b<k> <path>.<position>: <n> instrs → <terminator>`.

Edges are labelled `flow` (the control edges, `Silmaril.Wasm.Cfg.Edge`) or `effect` (the "may"
edges of `Silmaril.Wasm.Cfg.EffectEdge`: possible traps, and possible raises of calls). Block names
carry their effect marks in braces.

**These graphs are syntactic and incomplete.** They are computed from the instruction tree by
structured-control rules, and no theorem says that executions follow them. The kernel-checked
dominator tables are facts about the drawn graph only. The entry is the initial state, `exit` is accepting, and `trap`,
`raise` and `invalid` are error states. Loading the documents makes the registry prove each one's
immediate-dominator table (`<name>.dominators`), so the explorer draws the block CFG and its
kernel-checked dominator tree.

`*_blocks` proves in the kernel that each document has one state per block plus the four special
nodes, and exactly the builder's edges, by node index. The builder is the declarative relation
`Edge` (`blockCfg_eq`, `edge_iff`), so the drawn `flow` graph is that relation. The node names are only
presentation: the kernel does not evaluate string formatting.
-/

namespace ProjectSelfTest.WasmBlockCfg

@[expose] public section

open Silmaril.Automata Silmaril.Wasm Silmaril.Wasm.Cfg

/-- The block identities of a body, in `blocks` order. -/
def ids (body : Expr) : List BlockId := (blocks body).map (·.1)

/-- A node's index: the special nodes are `0`–`3`, block `k` of `blocks` is `4 + k`. -/
def tIndex (body : Expr) : Target → Nat
  | .exit => 0 | .trap => 1 | .raise => 2 | .invalid => 3
  | .block b => 4 + (ids body).idxOf b

/-- The builder's control edges by node index. -/
def edgesIdx (body : Expr) : List (Nat × Nat) :=
  (blockCfg body).flatMap fun (b, ts) => ts.map fun t => (tIndex body (.block b), tIndex body t)

/-- The effect edges by node index. -/
def effectIdx (body : Expr) : List (Nat × Nat) :=
  (blocks body).flatMap fun (b, s) =>
    (effectSucc body b s).map fun t => (tIndex body (.block b), tIndex body t)

/-- All edges by node index, labelled `flow` (control, `Edge`) or `effect` (`EffectEdge`). -/
def labelledIdx (body : Expr) : List (Nat × String × Nat) :=
  (edgesIdx body).map (fun (a, b) => (a, "flow", b)) ++
    (effectIdx body).map (fun (a, b) => (a, "effect", b))

/-- The short name of an effect mark. -/
def Effect.short : Effect → String
  | .mayTrap => "may trap" | .call => "call" | .unresolvedHandler => "handler unresolved"

/-- The name of block `k` with identity `b` and segment `s`. -/
def blockName (body : Expr) (k : Nat) (b : BlockId) (s : Segment) : String :=
  let path := ".".intercalate (b.seq.map fun (m, a) => s!"{m}/{a}")
  let term := match s.term with | some t => mnemonic t | none => "falls through"
  let marks := blockEffects body b s
  let marks := if marks.isEmpty then "" else " {" ++ ", ".intercalate (marks.map Effect.short) ++ "}"
  s!"b{k} [{path}].{b.idx}: {s.body.length} instrs → {term}{marks}"

/-- The names of a body's nodes, by index. -/
def names (body : Expr) : List String :=
  ["exit", "trap", "raise", "invalid"] ++
    ((blocks body).zipIdx.map fun ((b, s), k) => blockName body k b s)

/-- The name of a node. -/
def tName (body : Expr) (t : Target) : String := (names body).getD (tIndex body t) "?"

/-- The block CFG of a body as a machine document. -/
def blockDoc (id : String) (body : Expr) : Document where
  id := id
  spec := {
    states := names body
    labels := ["flow", "effect"]
    edges := (labelledIdx body).map fun (a, l, b) =>
      ⟨(names body).getD a "?", l, (names body).getD b "?"⟩ }
  layers := ⟨[tName body (cfgEntry body)], ["exit"], [], ["trap", "raise", "invalid"]⟩

end

end ProjectSelfTest.WasmBlockCfg

silmaril load "silmaril/machines/wasm-block-cfg.toml"

namespace ProjectSelfTest.WasmBlockCfg

open Silmaril.Automata Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Examples

/-- The document's edges as labelled pairs of state positions (node indices). -/
@[expose] public def edgeIndices (d : Document) : List (Nat × String × Nat) :=
  d.spec.edges.map fun e => (d.spec.states.idxOf e.src, e.label, d.spec.states.idxOf e.dst)

/-- A document is the block CFG of `body`: one state per block plus the four special nodes, the
builder's control edges (`flow`) then the effect edges (`effect`) by node index, and the entry
block as the initial state. -/
@[expose] public def IsBlockDoc (d : Document) (body : Expr) : Prop :=
  d.spec.states.length = 4 + (blocks body).length ∧ edgeIndices d = labelledIdx body ∧
    d.layers.initial.map d.spec.states.idxOf = [tIndex body (cfgEntry body)]

public theorem sum_blocks : IsBlockDoc silmaril.wasm.blockcfg.verified.sum sum := by
  unfold IsBlockDoc; decide +kernel
public theorem dispatch_blocks : IsBlockDoc silmaril.wasm.blockcfg.dispatch dispatch := by
  unfold IsBlockDoc; decide +kernel
public theorem specials_blocks : IsBlockDoc silmaril.wasm.blockcfg.specials specials := by
  unfold IsBlockDoc; decide +kernel
public theorem guarded_blocks : IsBlockDoc silmaril.wasm.blockcfg.guarded guarded := by
  unfold IsBlockDoc; decide +kernel
public theorem doorEnter_blocks :
    IsBlockDoc silmaril.wasm.blockcfg.rust_door.enter doorEnter := by
  unfold IsBlockDoc; decide +kernel

end ProjectSelfTest.WasmBlockCfg
