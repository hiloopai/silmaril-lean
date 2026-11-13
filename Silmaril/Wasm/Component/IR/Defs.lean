module

public import Silmaril.Wasm.Component.Adapter.Defs

/-!
# The component IR

Two intermediate representations of WebAssembly components, both designed for
optimisation rather than parsing.

## The nested IR (`Comp`)

A component has imports (a WIT-like `Iface`), a list of *nodes* in
topological order, and exports. Each node is an instance:

* `Node.core m args`: an instance of the core module `m`;
* `Node.inst c args`: an instance of a nested component `c`.

The functions visible at a node form its *environment*: the imports of the
component, followed by the exports of the earlier nodes, in order (function
`r` of the environment is the `r`-th of this list). The `i`-th import of a
node is supplied by the wiring program `args[i]` (`Impl`), a chain of
canonical-ABI adapters (`canon lift`/`canon lower`, …) ending in a call of an
environment function or a known constant. Exports are wiring programs over
the final environment. Instances are stateful and shared: every consumer of a
function of a node talks to the same instance.

Host imports are the imports of the outermost component; aliases and
`canon` definitions are wiring programs, not nodes.

## The flat (linked) IR (`Linked`)

The same shape with core instances only. Flattening a nested component
(`Silmaril.Wasm.Component.Passes.Flatten`) inlines its nodes into the parent and
substitutes the parent's wiring into the child's: the cross-component
`canon lower ∘ canon lift` pairs then become adjacent in one chain, where
adapter fusion removes them.

## Core modules

Core modules are a parameter `M` with a `CoreModule` instance giving their
core import and export interfaces. They may be silmaril `BModule`s, or
abstract module names (as in the examples).
-/

@[expose] public section

namespace Silmaril.Wasm.Component

/-- The core interfaces of core modules. -/
class CoreModule (M : Type) where
  /-- The functions a module imports. -/
  imports : M → CoreIface
  /-- The functions a module exports. -/
  exports : M → CoreIface

/-- An export: a named function implemented by a wiring program over the final
environment. -/
structure Export where
  /-- The export name. -/
  name : String
  /-- The function type (documentation and type checking; the semantics is
  dynamically typed). -/
  ty : FuncTy
  /-- Its implementation. -/
  impl : Impl
  deriving Repr, Inhabited, BEq

mutual
/-- A node of a component: an instance with the wiring of its imports. -/
inductive Node (M : Type) where
  /-- An instance of a core module. -/
  | core (m : M) (args : List Impl)
  /-- An instance of a nested component. -/
  | inst (c : Comp M) (args : List Impl)

/-- A component: imports, nodes in topological order, exports. -/
inductive Comp (M : Type) where
  | mk (imports : Iface) (nodes : List (Node M)) (exports : List Export)
end

namespace Comp

variable {M : Type}

/-- The imports. -/
def imports : Comp M → Iface | .mk I _ _ => I
/-- The nodes. -/
def nodes : Comp M → List (Node M) | .mk _ ns _ => ns
/-- The exports. -/
def exports : Comp M → List Export | .mk _ _ xs => xs

@[simp] theorem imports_mk (I : Iface) (ns : List (Node M)) (xs : List Export) :
    (Comp.mk I ns xs).imports = I := rfl
@[simp] theorem nodes_mk (I : Iface) (ns : List (Node M)) (xs : List Export) :
    (Comp.mk I ns xs).nodes = ns := rfl
@[simp] theorem exports_mk (I : Iface) (ns : List (Node M)) (xs : List Export) :
    (Comp.mk I ns xs).exports = xs := rfl

end Comp

namespace Comp

variable {M : Type}

mutual
/-- Rewrite every wiring program of a component, including those of nested
components. -/
def mapImpls (f : Impl → Impl) : Comp M → Comp M
  | .mk I ns xs => .mk I (Comp.mapImplsNodes f ns) (xs.map fun x => { x with impl := f x.impl })

/-- `mapImpls` on a list of nodes. -/
def mapImplsNodes (f : Impl → Impl) : List (Node M) → List (Node M)
  | [] => []
  | n :: ns => Comp.mapImplsNode f n :: Comp.mapImplsNodes f ns

/-- `mapImpls` on a node. -/
def mapImplsNode (f : Impl → Impl) : Node M → Node M
  | .core m args => .core m (args.map f)
  | .inst c args => .inst (Comp.mapImpls f c) (args.map f)
end

end Comp

variable {M : Type} [CoreModule M]

/-- The number of functions a node exports. -/
def Node.width : Node M → Nat
  | .core m _ => (CoreModule.exports m).length
  | .inst c _ => c.exports.length

/-- The size of the environment after the nodes `ns`, starting from `e`. -/
def envAfter (e : Nat) : List (Node M) → Nat
  | [] => e
  | n :: ns => envAfter (e + n.width) ns

/-- The flat IR: core instances only. -/
structure Linked (M : Type) where
  /-- The imports. -/
  imports : Iface
  /-- Core instances, in topological order, with the wiring of their imports. -/
  nodes : List (M × List Impl)
  /-- The exports. -/
  exports : List Export

/-- The size of the environment after the core instances `ns`. -/
def linkedEnv (e : Nat) : List (M × List Impl) → Nat
  | [] => e
  | n :: ns => linkedEnv (e + (CoreModule.exports n.1).length) ns

/-- A flat component as a nested one. -/
def Linked.toComponent (l : Linked M) : Comp M :=
  .mk l.imports (l.nodes.map fun n => .core n.1 n.2) l.exports

/-- A component together with the exports its context observes (`none`: all
of them). -/
structure Program (M : Type) where
  /-- The component. -/
  comp : Comp M
  /-- The observed exports, by index. -/
  observe : Option (List Nat) := none

end Silmaril.Wasm.Component
