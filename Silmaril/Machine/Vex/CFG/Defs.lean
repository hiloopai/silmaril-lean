module

public import Silmaril.Machine.Vex.Scalar.Defs
public import Silmaril.Machine.CBackend.Graph.Dominance.Defs

/-! # Labeled VEX graphs and checked dominator scoping -/

@[expose] public section

namespace Silmaril.Machine.Vex.AMD64Scalar

structure CFG where
  blocks : Array Block
  exits : List Word

def CFG.labels (cfg : CFG) : List Word := cfg.blocks.toList.map Block.address

def CFG.skeleton (cfg : CFG) : Graph.Digraph where
  size := cfg.blocks.size
  entry := 0
  succ := fun node => match cfg.blocks[node]? with
    | none => []
    | some block => block.code.targets.filterMap fun target => cfg.labels.idxOf? target

/-- Structural (not guard-feasible) reachability; the unverified skeleton is
not a substitute for checking a CFG's labels and exits. -/
def CFG.reachable (cfg : CFG) : List Word :=
  if cfg.blocks.isEmpty then []
  else (cfg.skeleton.closure (fun _ => true)).filterMap fun node =>
    cfg.blocks[node]?.map Block.address

inductive ScopeError where
  | empty
  | duplicateLabel
  | dangling (origin target : Word)
  | notForward (origin target : Word)
  | unreachable
  | outOfScope (origin target : Word)
  | incompleteTree
  deriving DecidableEq, Repr

/-- The block lives at its immediate dominator. Children bind labels over the
parent and all its subtrees. External exits remain free labels. -/
inductive Scoped where
  | region (index : Nat) (block : Block) (children : List Scoped)

def Scoped.indices : Scoped → List Nat
  | .region index _ children => index :: flatten children
where
  flatten : List Scoped → List Nat
    | [] => []
    | node :: rest => node.indices ++ flatten rest

def Scoped.flatten : Scoped → List Block
  | .region _ block children => block :: collect children
where
  collect : List Scoped → List Block
    | [] => []
    | node :: rest => node.flatten ++ collect rest

def CFG.scopeAt (cfg : CFG) (graph : Graph.Digraph) :
    Nat → Nat → List Word → Except ScopeError Scoped
  | 0, _, _ => .error .incompleteTree
  | fuel + 1, node, inherited => do
    let block ← requireSome .incompleteTree cfg.blocks[node]?
    let children := graph.domTreeChildren node
    let labels ← children.mapM fun child =>
      requireSome .incompleteTree (cfg.blocks[child]?.map Block.address)
    let visible := labels ++ inherited
    for target in block.code.targets do
      if !visible.contains target then throw (.outOfScope block.address target)
    return .region node block (← children.mapM fun child => cfg.scopeAt graph fuel child visible)

/-- Independently check closed internal edges, an explicit exit interface,
forward order, reachability, lexical scope, and exact node coverage. -/
def CFG.scope (cfg : CFG) : Except ScopeError Scoped := do
  if cfg.blocks.isEmpty then throw .empty
  let labels := cfg.labels
  let all := labels ++ cfg.exits
  if all.eraseDups.length != all.length then throw .duplicateLabel
  for (block, node) in cfg.blocks.toList.zipIdx do
    for target in block.code.targets do
      match labels.idxOf? target with
      | some dest => if dest ≤ node then throw (.notForward block.address target)
      | none => if !cfg.exits.contains target then throw (.dangling block.address target)
  let graph := cfg.skeleton
  if (graph.closure (fun _ => true)).length != graph.size then throw .unreachable
  let tree ← cfg.scopeAt graph graph.size graph.entry cfg.exits
  if tree.indices.mergeSort != List.range graph.size then throw .incompleteTree
  return tree

end Silmaril.Machine.Vex.AMD64Scalar
