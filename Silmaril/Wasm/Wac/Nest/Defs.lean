module

public import Silmaril.Wasm.Wac.Graph.Defs

/-!
# WAC: nesting and inlining of compositions

A composition `g₁` (over packages `P`) is itself a component, `g₁.toComp P`, so it can be
a package of a second composition `g₂`: package `k0` of `g₂` is `g₁.toComp P`
(`nestPkgs`). *Nesting = inlining* says that this means the same as `g₂` with every
instance of `k0` replaced by the instances of `g₁` (`Graph.inline`), wired to the
arguments of that instance.

## Inlining

`Graph.inline S k0 g₁ g₂` walks the nodes of `g₂`, renaming references (`ren` maps each
old node to the source of each of its exports in the new graph):

* a node of another package is kept, its arguments renamed;
* a node `⟨k0, args⟩` is replaced by the nodes of `g₁.explicate S` (every import of
  every instance an explicit argument, so that no import of `g₁` is promoted past the
  node): a reference `imp x` of `g₁` becomes the source of the import `x` at that node
  (its renamed argument, or `imp x` when it was promoted in `g₂`), and `out j q` becomes
  `out (base + j) q`. An export `q` of the node is the renamed source of `g₁`'s export
  `q`.

## The statement

Nesting = inlining is proved in `Silmaril.Wasm.Wac.NestInline.Thms` (`nest_inline`, and
`flatten_nest_inline`: the two flat components are equal). Two differences between the
sides are excluded:

* **import order**: `Graph.iface` lists imports by first occurrence, and the imports
  `g₁` promotes appear at the nested instance's position on one side and at the
  inlined nodes' positions on the other. Both components are therefore built over the
  **sorted** imports (`Graph.toCompSorted`, a canonical order);
* **lost imports**: an import of `g₁` used by no node of `g₁` (a declared but unused
  import, or one used only by an export) is an import of the nested side and absent
  from the inlined one. `NestOk` asks that `g₁` declares its imports, that each is used
  by a node of `g₁`, that exports are exports of instances, and that the types of
  the imports agree with what the packages expect (so the type `Graph.iface` keeps
  for an import does not depend on the order).

`Silmaril.Wasm.Wac.Nest.Thms` also checks the two sides on the worked composition by
evaluation.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

variable {M : Type}

/-- The lexicographic order of character lists, by code point. -/
def charsLe : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a.toNat < b.toNat || (a.toNat == b.toNat && charsLe as bs)

/-- Insert an import into a list sorted by name. -/
def insertIface (p : String × FuncTy) : Iface → Iface
  | [] => [p]
  | q :: l => if charsLe p.1.toList q.1.toList then p :: q :: l else q :: insertIface p l

/-- **The canonical import order**: sorted by name (insertion sort). -/
def sortIface : Iface → Iface
  | [] => []
  | p :: l => insertIface p (sortIface l)

/-- The composition over the imports `I` (any order of `Graph.iface`). -/
def Graph.buildWith (S : Nat → PkgSig) (P : Nat → Comp M) (g : Graph) (I : Iface) : Comp M :=
  .mk I (g.mkNodes S P I 0 g.nodes) (g.mkExports S I)

/-- The composition, with its imports in the canonical order. -/
def Graph.toCompSorted (P : Nat → Comp M) (g : Graph) : Comp M :=
  g.buildWith (fun k => sigOf (P k)) P (sortIface (g.iface fun k => sigOf (P k)))

/-- The packages of the nested composition: package `k0` is the composition `g₁`. -/
def nestPkgs (P : Nat → Comp M) (k0 : Nat) (g₁ : Graph) (k : Nat) : Comp M :=
  if k = k0 then g₁.toComp P else P k

/-- Rename a reference of `g₂` by `ren` (unknown nodes keep the reference to the
import of the same name, a placeholder for ill-formed graphs). -/
def renSrc (ren : List (String → Src)) : Src → Src
  | .imp x => .imp x
  | .out j q => match ren[j]? with
    | some r => r q
    | none => .imp q

/-- A reference of `g₁` inside the instance `n'` of `g₁` placed at node `base`. -/
def innerSrc (n' : Inst) (base : Nat) : Src → Src
  | .imp x => n'.src x
  | .out j q => .out (base + j) q

/-- The inlining state: the new nodes, and for each old node its export sources. -/
structure IAcc where
  nodes : List Inst := []
  ren : List (String → Src) := []

/-- One node of `g₂`. -/
def inlineNode (S : Nat → PkgSig) (k0 : Nat) (g₁ : Graph) (acc : IAcc) (n : Inst) : IAcc :=
  let n' : Inst := ⟨n.pkg, n.args.map fun a => (a.1, renSrc acc.ren a.2)⟩
  if n.pkg = k0 then
    let base := acc.nodes.length
    let inner := (g₁.explicate S).nodes.map fun m =>
      (⟨m.pkg, m.args.map fun a => (a.1, innerSrc n' base a.2)⟩ : Inst)
    { nodes := acc.nodes ++ inner
      ren := acc.ren ++ [fun q => match g₁.exports.lookup q with
        | some s => innerSrc n' base s
        | none => .imp q] }
  else
    { nodes := acc.nodes ++ [n']
      ren := acc.ren ++ [fun q => .out acc.nodes.length q] }

/-- **Inlining**: every instance of package `k0` of `g₂` replaced by the instances of
`g₁`. -/
def Graph.inline (S : Nat → PkgSig) (k0 : Nat) (g₁ g₂ : Graph) : Graph :=
  let acc := g₂.nodes.foldl (inlineNode S k0 g₁) {}
  { imports := g₂.imports
    nodes := acc.nodes
    exports := g₂.exports.map fun p => (p.1, renSrc acc.ren p.2) }

/-- Every reference of every instance and export of `g` is typed as its package
expects: an import used at the type `t` is an import of the composition at `t`. -/
def Graph.TypedImports (S : Nat → PkgSig) (g : Graph) : Prop :=
  ∀ n ∈ g.nodes, ∀ p ∈ (S n.pkg).imports, ∀ x, n.src p.1 = .imp x → (g.iface S).lookup x = some p.2

/-- The exports of `g` are exports of instances. -/
def Graph.ExportsOut (g : Graph) : Prop := ∀ p ∈ g.exports, ∃ k q, p.2 = .out k q

/-- The conditions of nesting = inlining. -/
structure NestOk (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph) : Prop where
  /-- Both graphs are well formed. -/
  wf₁ : g₁.WF fun k => sigOf (P k)
  wf₂ : g₂.WF fun k => sigOf (nestPkgs P k0 g₁ k)
  /-- `g₁` does not instantiate `k0`. -/
  noSelf : ∀ n ∈ g₁.nodes, n.pkg ≠ k0
  /-- `g₁` declares its imports, and uses each of them in a node. -/
  declared : (g₁.iface fun k => sigOf (P k)) = g₁.imports
  used : ∀ x ∈ names g₁.imports, ∃ n ∈ g₁.nodes, ∃ p ∈ (sigOf (P n.pkg)).imports, n.src p.1 = .imp x
  /-- Exports are exports of instances. -/
  out₁ : g₁.ExportsOut
  out₂ : g₂.ExportsOut
  /-- Imports are used at the types they are declared with. -/
  typed₁ : g₁.TypedImports fun k => sigOf (P k)
  typed₂ : g₂.TypedImports fun k => sigOf (nestPkgs P k0 g₁ k)

/-- The conditions the *run* of nesting = inlining needs: both graphs well formed, exports
of instances. Unlike `NestOk`, nothing about the imports of `g₁`: an unused or undeclared
import is allowed. Under it, the nested and the inlined composition built over **the same**
import list mean the same (`Wac.nest_inline_with`, `Wac.nest_inline_any` in
`Silmaril.Wasm.Wac.NestAny.Thms`). -/
structure NestRunOk (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph) : Prop where
  wf₁ : g₁.WF fun k => sigOf (P k)
  wf₂ : g₂.WF fun k => sigOf (nestPkgs P k0 g₁ k)
  out₁ : g₁.ExportsOut
  out₂ : g₂.ExportsOut

/-- `NestOk` gives the run conditions. -/
theorem NestOk.toRun {P : Nat → Comp M} {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂) :
    NestRunOk P k0 g₁ g₂ :=
  ⟨ok.wf₁, ok.wf₂, ok.out₁, ok.out₂⟩

end Silmaril.Wasm.Wac
