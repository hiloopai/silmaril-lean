module

public import Silmaril.Wasm.Modules
public import Silmaril.Machine.CBackend.Graph.Dominance.Defs

@[expose] public section

/-!
# Control-flow graphs of Wasm functions

`Cfg.ofFunc f` extracts the **instruction-level control-flow graph** of a function body
(`Wasm.Expr`, structured control) as a `Silmaril.Machine.Graph.Digraph`, the rooted-graph type
whose dominators and dominator trees are analysed in `Silmaril.Machine.Graph` and
`Silmaril.Automata.Graph`.

**Nodes.** One node per instruction occurrence, identified by its **path** (`NodeKind.instr`:
the position in the body, through nested `block`/`loop`/`if`/`try_table` bodies; an `if`'s
else branch is marked `1` after the instruction's index), plus four special nodes:

| node | index | meaning |
| --- | --- | --- |
| `exit` | 0 | the function returns (falling off the body, `return`, tail calls) |
| `trap` | 1 | `unreachable` |
| `raise` | 2 | an exception leaves the instruction (`throw`, `throw_ref`); its handler is not resolved |
| `invalid` | 3 | a branch to a label depth that does not exist (an invalid module) |

The entry is the node of the first instruction (or `exit` for an empty body).

**Edges** follow the structured-control rules of the Wasm specification (Core 3.0 §4.4.8),
resolved syntactically by label depth: `block`'s label is its continuation, `loop`'s label is the
loop itself, an `if` branches to both arms, and the function body is a block whose label is the
return.

* `br l` → the target of label `l`; `br_if l` and the conditional reference branches
  (`br_on_null`, `br_on_non_null`, `br_on_cast`, `br_on_cast_fail`) → the target of `l` **and**
  the next instruction; `br_table ls d` → the target of every listed label and of `d` (all
  syntactically known; duplicates kept once).
* `return`, `return_call`, `return_call_ref`, `return_call_indirect` → `exit`;
  `unreachable` → `trap`; `throw`, `throw_ref` → `raise`.
* `try_table` → its body and, **conservatively**, the target of each catch clause (an
  exception raised anywhere in the body may reach any handler; which ones do is not analysed).
* Calls (`call`, `call_ref`, `call_indirect`) continue to the next instruction; their callees are
  the business of the call graph. That a callee may trap or throw is **not** an edge here:
  only `unreachable` and `throw`/`throw_ref` are. Every other instruction (including those that
  may trap at run time: division, memory and table accesses, casts) continues to the next.

So the graph is exact for the control transfers of structured control and branches, and states
its approximations: the unresolved exception target (`raise`), the over-approximate catch edges,
and the trap edges of operations that can trap being omitted. `Thms` checks extractions of
example functions against these rules in the kernel.
-/

namespace Silmaril.Wasm.Cfg

open Silmaril.Machine.Graph

/-- What a node of the CFG is. -/
inductive NodeKind where
  | instr (path : List Nat) (name : String)
  | exit | trap | raise | invalid
  deriving DecidableEq, Repr, Inhabited

/-- The special nodes. -/
def exitNode : Nat := 0
def trapNode : Nat := 1
def raiseNode : Nat := 2
def invalidNode : Nat := 3

/-- The builder's state: the node kinds and successor lists, by node index. -/
structure Builder where
  kinds : Array NodeKind := #[.exit, .trap, .raise, .invalid]
  succ : Array (List Nat) := #[[], [], [], []]
  deriving Inhabited

/-- Add a node; its successors are set later. -/
def alloc (k : NodeKind) : StateM Builder Nat := modifyGet fun b =>
  (b.kinds.size, { kinds := b.kinds.push k, succ := b.succ.push [] })

/-- Set a node's successors (duplicates dropped, order kept). -/
def setSucc (n : Nat) (ss : List Nat) : StateM Builder Unit :=
  modify fun b => { b with succ := b.succ.set! n ss.eraseDups }

/-- The target of label depth `l` (`invalid` beyond the label stack). -/
def resolve (labels : List Nat) (l : LabelIdx) : Nat := labels.getD l.value.val invalidNode

/-- An index as its number. -/
instance {k : IndexKind} : ToString (Idx k) := ⟨fun i => toString i.value.val⟩

/-- A short name for an instruction (its constructor). -/
def mnemonic : Instr → String
  | .nop => "nop" | .unreachable => "unreachable" | .drop => "drop" | .select _ => "select"
  | .block .. => "block" | .loop .. => "loop" | .if_ .. => "if"
  | .br l => s!"br {l}" | .brIf l => s!"br_if {l}"
  | .brTable ls d => s!"br_table {ls} {d}"
  | .brOnNull l => s!"br_on_null {l}" | .brOnNonNull l => s!"br_on_non_null {l}"
  | .brOnCast l .. => s!"br_on_cast {l}" | .brOnCastFail l .. => s!"br_on_cast_fail {l}"
  | .call f => s!"call {f}" | .callRef t => s!"call_ref {t}"
  | .callIndirect t ty => s!"call_indirect {t} {ty}"
  | .return_ => "return" | .returnCall f => s!"return_call {f}"
  | .returnCallRef t => s!"return_call_ref {t}"
  | .returnCallIndirect t ty => s!"return_call_indirect {t} {ty}"
  | .throw t => s!"throw {t}" | .throwRef => "throw_ref" | .tryTable .. => "try_table"
  | .localGet i => s!"local.get {i}" | .localSet i => s!"local.set {i}"
  | .localTee i => s!"local.tee {i}" | .globalGet i => s!"global.get {i}"
  | .globalSet i => s!"global.set {i}"
  | i =>
    -- the constructor's name, from `Repr` (e.g. `intBinary`); its arguments are left out
    let r := reprStr i
    let r := (r.dropPrefix "Silmaril.Wasm.Instr.").toString
    (r.splitOn " ").headD "op"

/-- The label of a catch clause. -/
def catchLabel : Catch → LabelIdx
  | .catch_ _ l | .catchRef _ l | .catchAll l | .catchAllRef l => l

mutual
/-- Build the nodes of `i` (at `path`), continuing to `next`, under the label targets `labels`;
returns the node of `i`. -/
def buildInstr (path : List Nat) (next : Nat) (labels : List Nat) : Instr → StateM Builder Nat
  | .block _ body => do
    let n ← alloc (.instr path "block")
    let b ← buildSeq (path ++ [0]) 0 next (next :: labels) body
    setSucc n [b]; pure n
  | .loop _ body => do
    let n ← alloc (.instr path "loop")
    let b ← buildSeq (path ++ [0]) 0 next (n :: labels) body
    setSucc n [b]; pure n
  | .if_ _ thenBody elseBody => do
    let n ← alloc (.instr path "if")
    let t ← buildSeq (path ++ [0]) 0 next (next :: labels) thenBody
    let e ← buildSeq (path ++ [1]) 0 next (next :: labels) elseBody
    setSucc n [t, e]; pure n
  | .tryTable _ catches body => do
    let n ← alloc (.instr path "try_table")
    let b ← buildSeq (path ++ [0]) 0 next (next :: labels) body
    setSucc n (b :: catches.map fun c => resolve labels (catchLabel c)); pure n
  | i => do
    let n ← alloc (.instr path (mnemonic i))
    setSucc n <| match i with
      | .br l => [resolve labels l]
      | .brIf l | .brOnNull l | .brOnNonNull l | .brOnCast l .. | .brOnCastFail l .. =>
        [resolve labels l, next]
      | .brTable ls d => (ls ++ [d]).map (resolve labels)
      | .return_ | .returnCall _ | .returnCallRef _ | .returnCallIndirect .. => [exitNode]
      | .unreachable => [trapNode]
      | .throw _ | .throwRef => [raiseNode]
      | _ => [next]
    pure n
/-- Build a sequence (at `path`, starting at index `k`), continuing to `next`; returns the node
of its first instruction (`next` when empty). -/
def buildSeq (path : List Nat) (k : Nat) (next : Nat) (labels : List Nat) :
    List Instr → StateM Builder Nat
  | [] => pure next
  | i :: is => do
    let r ← buildSeq path (k + 1) next labels is
    buildInstr (path ++ [k]) r labels i
end

/-- The CFG of a function body: the graph and what each node is. -/
structure FuncCfg where
  graph : Digraph
  kinds : Array NodeKind

/-- The CFG of a body (an implicit block whose label is the return). -/
def ofExpr (body : Expr) : FuncCfg :=
  let (entry, b) := (buildSeq [] 0 exitNode [exitNode] body).run {}
  { graph := { size := b.kinds.size, succ := fun n => b.succ.getD n [], entry }
    kinds := b.kinds }

/-- The CFG of a function. -/
def ofFunc (f : Func) : FuncCfg := ofExpr f.body

/-- The edges of a CFG, as `(from, to)` pairs. -/
def FuncCfg.edges (c : FuncCfg) : List (Nat × Nat) :=
  (List.range c.graph.size).flatMap fun n => (c.graph.succ n).map (n, ·)

end Silmaril.Wasm.Cfg
