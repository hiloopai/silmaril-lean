module

public import Silmaril.Wasm.Component.Semantics.Defs

/-!
# WAC: composition graphs and their translation to the component IR

A WAC composition, at the level of functions, is a *composition graph* (`Graph`): a list
of package instances (`Inst`: a package index and named arguments) in topological order,
declared imports, and named exports. Every name is a function-level qualified name, in
the convention of `Silmaril.Wasm.Component.Binary.lower`: a function `f` of an instance
`i` is `i#f`. A reference (`Src`) is an import of the composition (`imp x`) or an export
`q` of an earlier instance (`out k q`).

Packages are components of the component IR, `P : Nat → Comp M` (package `k` is the
component of index `k` of the composition: embedded or imported). `Graph.toComp P g` is
the nested component

* whose **imports** are the declared imports, then the imports used by the instances,
  then those used by the exports, **deduplicated by name** (first occurrence wins);
* with one node `.inst (P n.pkg) args` per instance, where `args` wires every import
  `q` of the package: by its argument, if the instance names one (`n.args`), and
  otherwise by **promotion**: by the import `q` of the composition (`Inst.src`);
  two instances that leave the same import `q` unsatisfied share the import `q`;
* with one export per graph export.

The construction only depends on the packages through their interfaces (`PkgSig`):
`Graph.build S P g` takes the interfaces `S` separately, and `toComp P` is
`build (sigOf ∘ P) P`. References that do not resolve (an unknown export, a later or
unknown instance) are wired to a trap; `Graph.WF` says that every reference resolves.

Theorems in `Silmaril.Wasm.Wac.Graph.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

/-- A reference to a function in a composition. -/
inductive Src where
  /-- The import `name` of the composition. -/
  | imp (name : String)
  /-- The export `name` of the instance `node`. -/
  | out (node : Nat) (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- An instance of a package, with its named arguments. -/
structure Inst where
  /-- The package (component index). -/
  pkg : Nat
  /-- Named arguments: an import name of the package and its source. -/
  args : List (String × Src) := []
  deriving DecidableEq, Repr, Inhabited

/-- A composition graph. -/
structure Graph where
  /-- Declared (explicit) imports. -/
  imports : Iface := []
  /-- The instances, in topological order. -/
  nodes : List Inst
  /-- The exports: names and sources. -/
  exports : List (String × Src) := []
  deriving Repr, Inhabited, DecidableEq

/-- The interface of a package: imports and exports with their types. -/
structure PkgSig where
  imports : Iface
  exports : Iface
  deriving DecidableEq, Repr, Inhabited

variable {M : Type}

/-- The interface of a component. -/
def sigOf (c : Comp M) : PkgSig := ⟨c.imports, c.exports.map fun x => (x.name, x.ty)⟩

/-- The names of an interface. -/
abbrev names (I : Iface) : List String := I.map Prod.fst

/-- **Promotion**: the source of the import `q` of an instance is its argument `q`, if
any, and otherwise the import `q` of the composition. -/
def Inst.src (n : Inst) (q : String) : Src := (n.args.lookup q).getD (.imp q)

/-- The imports of the composition that an instance uses (with the types the package
expects). -/
def Inst.uses (S : Nat → PkgSig) (n : Inst) : Iface :=
  (S n.pkg).imports.filterMap fun p =>
    match n.src p.1 with
    | .imp x => some (x, p.2)
    | .out _ _ => none

/-- The placeholder type of an import used only by an export. -/
def anyTy : FuncTy := ⟨[], []⟩

/-- The imports used by the exports. -/
def Graph.exportUses (g : Graph) : Iface :=
  g.exports.filterMap fun p =>
    match p.2 with
    | .imp x => some (x, anyTy)
    | .out _ _ => none

/-- **Merging of duplicate imports**: keep the first entry of every name. -/
def dedup : Iface → Iface
  | [] => []
  | p :: l => p :: (dedup l).filter fun r => r.1 != p.1

/-- The imports of the composition. -/
def Graph.iface (S : Nat → PkgSig) (g : Graph) : Iface :=
  dedup (g.imports ++ g.nodes.flatMap (Inst.uses S) ++ g.exportUses)

/-- The number of functions exported by the first `k` instances. -/
def Graph.offset (S : Nat → PkgSig) (g : Graph) (k : Nat) : Nat :=
  ((g.nodes.take k).map fun n => (S n.pkg).exports.length).sum

/-- Does a reference resolve, in a context where the instances below `bound` exist? -/
def Graph.Resolves (S : Nat → PkgSig) (g : Graph) (I : Iface) (bound : Nat) : Src → Prop
  | .imp x => x ∈ names I
  | .out k q => ∃ n, g.nodes[k]? = some n ∧ k < bound ∧ q ∈ names (S n.pkg).exports

/-- The wiring of a reference, over the environment of the composition: its imports
`I`, then the exports of the instances; unresolved references trap. -/
def Graph.resolve (S : Nat → PkgSig) (g : Graph) (I : Iface) (bound : Nat) : Src → Impl
  | .imp x => if x ∈ names I then .fwd ((names I).idxOf x) else .trap
  | .out k q =>
    match g.nodes[k]? with
    | some n =>
      if k < bound ∧ q ∈ names (S n.pkg).exports then
        .fwd (I.length + g.offset S k + (names (S n.pkg).exports).idxOf q)
      else .trap
    | none => .trap

/-- The type of a reference (placeholder if it does not resolve). -/
def Graph.tyOf (S : Nat → PkgSig) (g : Graph) (I : Iface) : Src → FuncTy
  | .imp x => (I.lookup x).getD anyTy
  | .out k q =>
    match g.nodes[k]? with
    | some n => ((S n.pkg).exports.lookup q).getD anyTy
    | none => anyTy

/-- The wiring of the imports of instance `k`. -/
def Graph.argsOf (S : Nat → PkgSig) (g : Graph) (I : Iface) (k : Nat) (n : Inst) : List Impl :=
  (S n.pkg).imports.map fun p => g.resolve S I k (n.src p.1)

/-- The nodes of the composition, from instance `k` on. -/
def Graph.mkNodes (S : Nat → PkgSig) (P : Nat → Comp M) (g : Graph) (I : Iface) :
    Nat → List Inst → List (Node M)
  | _, [] => []
  | k, n :: ns => .inst (P n.pkg) (g.argsOf S I k n) :: g.mkNodes S P I (k + 1) ns

/-- The exports of the composition. -/
def Graph.mkExports (S : Nat → PkgSig) (g : Graph) (I : Iface) : List Export :=
  g.exports.map fun p => ⟨p.1, g.tyOf S I p.2, g.resolve S I g.nodes.length p.2⟩

/-- The composition, given the package interfaces `S` and the packages `P`. -/
def Graph.build (S : Nat → PkgSig) (P : Nat → Comp M) (g : Graph) : Comp M :=
  .mk (g.iface S) (g.mkNodes S P (g.iface S) 0 g.nodes) (g.mkExports S (g.iface S))

/-- **The composition as a component of the component IR.** -/
def Graph.toComp (P : Nat → Comp M) (g : Graph) : Comp M :=
  g.build (fun k => sigOf (P k)) P

/-- Every reference of the graph resolves: arguments to earlier instances, exports to
any instance. -/
def Graph.WF (S : Nat → PkgSig) (g : Graph) : Prop :=
  (∀ k n, g.nodes[k]? = some n → ∀ p ∈ (S n.pkg).imports, g.Resolves S (g.iface S) k (n.src p.1)) ∧
  (∀ p ∈ g.exports, g.Resolves S (g.iface S) g.nodes.length p.2)

/-- **Explicit promotion**: every import of every instance gets an explicit argument
(the promoted import `q` when the instance had none), as `wac` encodes a composition
in WAT (where instantiation arguments are total). -/
def Inst.explicate (S : Nat → PkgSig) (n : Inst) : Inst :=
  { n with args := (S n.pkg).imports.map fun p => (p.1, n.src p.1) }

/-- `Inst.explicate` on every instance. -/
def Graph.explicate (S : Nat → PkgSig) (g : Graph) : Graph :=
  { g with nodes := g.nodes.map (Inst.explicate S) }

/-- An instance has an argument for every import of its package. -/
def Inst.Explicit (S : Nat → PkgSig) (n : Inst) : Prop :=
  ∀ p ∈ (S n.pkg).imports, (n.args.lookup p.1).isSome

/-! ## The compositional semantics -/

open Silmaril.Games

/-- The environment size after the instances `ns`, from `e`. -/
def Graph.envFrom (S : Nat → PkgSig) : Nat → List Inst → Nat
  | e, [] => e
  | e, n :: ns => Graph.envFrom S (e + (S n.pkg).exports.length) ns

/-- The environment built by the instances `ns` (from instance `k`, over an environment
of `e` functions), each instance being a strategy `D n.pkg` below its wiring. -/
def Graph.semNodes (S : Nat → PkgSig) (g : Graph) (I : Iface) (D : Nat → Strategy sigU sigU)
    {X : Sig.{0}} : Nat → Nat → List Inst → Strategy X sigU → Strategy X sigU
  | _, _, [], E => E
  | k, e, n :: ns, E =>
    g.semNodes S I D (k + 1) (e + (S n.pkg).exports.length) ns
      (ext e E ((Strategy.ofHandler (implsH e (g.argsOf S I k n))).comp (D n.pkg)))

/-- **The meaning of a composition as a function of the meanings `D` of its packages**
(with interfaces `S`). -/
def Graph.sem (S : Nat → PkgSig) (g : Graph) (D : Nat → Strategy sigU sigU) :
    Strategy sigU sigU :=
  (g.semNodes S (g.iface S) D 0 (g.iface S).length g.nodes
      (Strategy.ofHandler (maskH (g.iface S).length))).comp
    (Strategy.ofHandler (exportsH (Graph.envFrom S (g.iface S).length g.nodes)
      (g.mkExports S (g.iface S))))

end Silmaril.Wasm.Wac
