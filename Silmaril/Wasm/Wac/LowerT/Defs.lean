module

public import Silmaril.Wasm.Wac.Lower.Defs

/-!
# WAC: typed lowering of profile WAT to composition graphs, and its specification

`Silmaril.Wasm.Wac.Lower.graph` reads a profile component as a composition graph, but
gives every declared import the placeholder type `anyTy` unless a package uses it, and
does not check the types of instantiation arguments. This module gives

* **a typed lowering** `LowerT.graph S c`: function types of the WAT are converted to
  `FuncTy` with `Binary.lower`'s reading (`Binary.Lower.typeEntry` for type definitions,
  `Binary.Lower.instFuncs` for the function exports of instance types). An imported
  function or instance declares its imports with their types; an `instantiate`
  argument must have the type the package expects (equal `FuncTy`, as the component
  IR has no subtyping); and every import of the package must be given an argument
  (`wac` writes instantiation arguments in full);
* **a relational specification of the profile's index spaces** (`Den`, `NodeAt`,
  `Decls`, `Exps`). The component is a list of items (`items`), each defining at most
  one index of one sort (`Item.sp`). Index `j` of sort `s` after the items `l` is
  defined by the item `x` of `l = pre ++ [x] ++ post` with `j` the number of items of
  sort `s` in `pre`, and denotes what `x` denotes when its references are read in `pre`
  (`Den`). The relation is stated by appending one item at a time (`Den.there` keeps
  the indices of `pre`).

The theorems (`Silmaril.Wasm.Wac.LowerT.Thms`) prove the executable lowering sound for this
specification and the index-space sizes equal to the counts of items of each sort.

Index spaces: components (`comp`: embedded definitions and imported, aliased, exported
components; component `k` is package `k`), instances (`inst`: a location `Loc` and its
table of functions with their types), functions (`func`: a reference `Src` and its
type) and types (`type`: `Binary.Lower.TypeEntry`, as `Binary.lower` keeps them).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.LowerT

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wac.Lower (Loc qual)

/-- The `TypeEntry` of `Binary.lower`. -/
abbrev TypeEntry := Silmaril.Wasm.Component.Binary.Lower.TypeEntry

/-- The function exports of an instance, with their types. -/
abbrev Table := List (String × FuncTy)

/-! ## Items and index spaces -/

/-- An item of a profile component: one element of a section. -/
inductive Item where
  | type (t : DefType)
  | imp (i : Import)
  | comp
  | inst (e : InstanceExpr)
  | alias (a : Alias)
  | exp (e : Binary.Export)

/-- The items of a section (`none` outside the profile's sections). -/
def secItems : Section → Option (List Item)
  | .custom _ _ => some []
  | .types xs => some (xs.map .type)
  | .imports xs => some (xs.map .imp)
  | .component _ => some [.comp]
  | .instances xs => some (xs.map .inst)
  | .aliases xs => some (xs.map .alias)
  | .exports xs => some (xs.map .exp)
  | _ => none

/-- The items of a component. -/
def items (c : Ast) : Option (List Item) := (c.sections.mapM secItems).map List.flatten

/-- The index spaces of the profile. -/
inductive Sp where
  | comp | inst | func | type
  deriving DecidableEq, Repr

/-- The index space of a sort. -/
def spOfSort : ItemSort → Option Sp
  | .component => some .comp
  | .instance => some .inst
  | .func => some .func
  | .type => some .type
  | _ => none

/-- The sort of an extern descriptor. -/
def descSp : ExternDesc → Option Sp
  | .func _ => some .func
  | .type _ => some .type
  | .component _ => some .comp
  | .instance _ => some .inst
  | _ => none

/-- The index space an item adds an index to. -/
def Item.sp : Item → Option Sp
  | .type _ => some .type
  | .imp i => descSp i.desc
  | .comp => some .comp
  | .inst _ => some .inst
  | .alias a => spOfSort a.sort
  | .exp e => spOfSort e.item.sort

/-- Whether an item is an `instantiate` (a node of the graph). -/
def Item.isNode : Item → Bool
  | .inst (.instantiate _ _) => true
  | _ => false

/-- The number of indices of the space `s` defined by the items `l`. -/
def count (s : Sp) (l : List Item) : Nat := l.countP fun x => x.sp == some s

/-- The number of nodes defined by `l`. -/
def nodeCount (l : List Item) : Nat := l.countP Item.isNode

/-- The type entry an item adds, given the earlier ones. -/
def tyStep (ts : List TypeEntry) (x : Item) : List TypeEntry :=
  match x with
  | .type t => ts ++ [Silmaril.Wasm.Component.Binary.Lower.typeEntry ts.toArray t]
  | x => if x.sp == some .type then ts ++ [.other "imported, aliased or exported type"] else ts

/-- **The type index space** after the items `l`: types are read as `Binary.lower`
reads them; imported, aliased and exported types are opaque. -/
def typesOf (l : List Item) : List TypeEntry := l.foldl tyStep []

/-- The suffix `f` of `q = n#f` (`Lower.suffix?` on character lists, which the kernel
evaluates in modules; `sfx_eq_suffix` in `Silmaril.Wasm.Wac.LowerWF.Thms`). -/
def sfx? (n q : String) : Option String :=
  if (n.toList ++ ['#']).isPrefixOf q.toList then some (String.ofList (q.toList.drop (n.length + 1)))
  else none

/-- The table of a nested instance `n` of an instance with table `tab`. -/
def subTable (n : String) (tab : Table) : Table :=
  tab.filterMap fun p => (sfx? n p.1).map fun f => (f, p.2)

/-- The imports `n#f` of a package interface `s` that an instance argument `n`
supplies: the import, the function `f` and its type. -/
def instArgs (s : PkgSig) (n : String) : List (String × String × FuncTy) :=
  s.imports.filterMap fun p => (sfx? n p.1).map fun f => (p.1, f, p.2)

/-- An instance has an argument for every import of its package. -/
def explicitArgs (s : PkgSig) (as : List (String × Src)) : Bool :=
  s.imports.all fun p => (as.lookup p.1).isSome

/-! ## The specification -/

mutual
/-- **What an index denotes**: `Den S l j e` says that the index `j` of the space of `e`,
after the items `l`, denotes `e` (`.inl (loc, tab)` for an instance, `.inr (src, ft)`
for a function). -/
inductive Den (S : Nat → PkgSig) : List Item → Sp → Nat → (Loc × Table) ⊕ (Src × FuncTy) → Prop
  /-- An earlier index keeps its denotation. -/
  | there {l : List Item} {x : Item} {s : Sp} {j : Nat} {e} :
      Den S l s j e → Den S (l ++ [x]) s j e
  /-- An imported function, with the type its type index reads as. -/
  | impFunc {l : List Item} {i : Import} {t : Nat} {ft : FuncTy} :
      i.desc = .func t → (typesOf l)[t]? = some (.func ft) →
      Den S (l ++ [.imp i]) .func (count .func l) (.inr (.imp i.name.name, ft))
  /-- An imported instance, with the function exports of its instance type. -/
  | impInst {l : List Item} {i : Import} {t : Nat} {ds : List InstanceDecl} {tab : Table} :
      i.desc = .instance t → (typesOf l)[t]? = some (.inst ds) →
      Silmaril.Wasm.Component.Binary.Lower.instFuncs (typesOf l).toArray ds = .ok tab →
      Den S (l ++ [.imp i]) .inst (count .inst l) (.inl (.imp i.name.name, tab))
  /-- An instantiation of package `c`: the next node, with the package's exports. -/
  | node {l : List Item} {c : Nat} {args : List (String × SortIdx)} {as : List (String × Src)} :
      ArgsDen S l c args as → explicitArgs (S c) as = true → c < count .comp l →
      Den S (l ++ [.inst (.instantiate c args)]) .inst (count .inst l)
        (.inl (.node (nodeCount l) none, (S c).exports))
  /-- An alias of the function export `n` of instance `i`. -/
  | aliasFunc {l : List Item} {i : Nat} {n : String} {loc : Loc} {tab : Table} {ft : FuncTy} :
      Den S l .inst i (.inl (loc, tab)) → tab.lookup n = some ft →
      Den S (l ++ [.alias ⟨.func, .export i n⟩]) .func (count .func l) (.inr (loc.func n, ft))
  /-- An alias of the nested instance `n` of instance `i`. -/
  | aliasInst {l : List Item} {i : Nat} {n : String} {loc : Loc} {tab : Table} :
      Den S l .inst i (.inl (loc, tab)) →
      Den S (l ++ [.alias ⟨.instance, .export i n⟩]) .inst (count .inst l)
        (.inl (loc.inst n, subTable n tab))
  /-- An export of a function: a new index for the same function. -/
  | expFunc {l : List Item} {e : Binary.Export} {j : Nat} {src : Src} {ft : FuncTy} :
      e.item = ⟨.func, j⟩ → Den S l .func j (.inr (src, ft)) →
      Den S (l ++ [.exp e]) .func (count .func l) (.inr (src, ft))
  /-- An export of an instance: a new index for the same instance. -/
  | expInst {l : List Item} {e : Binary.Export} {j : Nat} {loc : Loc} {tab : Table} :
      e.item = ⟨.instance, j⟩ → Den S l .inst j (.inl (loc, tab)) →
      Den S (l ++ [.exp e]) .inst (count .inst l) (.inl (loc, tab))

/-- The arguments of an instantiation of package `c`, read after the items `l`: the
named arguments of the graph node, each typed as the package expects. -/
inductive ArgDen (S : Nat → PkgSig) : List Item → Nat →
    String × SortIdx → List (String × Src) → Prop
  | func {l : List Item} {c : Nat} {n : String} {j : Nat} {src : Src} {ft : FuncTy} :
      Den S l .func j (.inr (src, ft)) → (S c).imports.lookup n = some ft →
      ArgDen S l c (n, ⟨.func, j⟩) [(n, src)]
  | inst {l : List Item} {c : Nat} {n : String} {j : Nat} {loc : Loc} {tab : Table} :
      Den S l .inst j (.inl (loc, tab)) →
      (∀ q f ty, (q, f, ty) ∈ instArgs (S c) n → tab.lookup f = some ty) →
      ArgDen S l c (n, ⟨.instance, j⟩) ((instArgs (S c) n).map fun a => (a.1, loc.func a.2.1))
  | type {l : List Item} {c : Nat} {n : String} {j : Nat} : ArgDen S l c (n, ⟨.type, j⟩) []
  | comp {l : List Item} {c : Nat} {n : String} {j : Nat} : ArgDen S l c (n, ⟨.component, j⟩) []

/-- All the arguments: their named arguments, concatenated. -/
inductive ArgsDen (S : Nat → PkgSig) : List Item → Nat →
    List (String × SortIdx) → List (String × Src) → Prop
  | nil {l : List Item} {c : Nat} : ArgsDen S l c [] []
  | cons {l : List Item} {c : Nat} {a : String × SortIdx} {args : List (String × SortIdx)} {x xs : List (String × Src)} :
      ArgDen S l c a x → ArgsDen S l c args xs → ArgsDen S l c (a :: args) (x ++ xs)
end

/-- **The nodes**: node `k` after the items `l` is the `k`-th instantiation, with its
arguments read in the items before it. -/
inductive NodeAt (S : Nat → PkgSig) : List Item → Nat → Inst → Prop
  | there {l : List Item} {x : Item} {k : Nat} {n : Inst} : NodeAt S l k n → NodeAt S (l ++ [x]) k n
  | here {l : List Item} {c : Nat} {args : List (String × SortIdx)} {as : List (String × Src)} :
      ArgsDen S l c args as → explicitArgs (S c) as = true → c < count .comp l →
      NodeAt S (l ++ [.inst (.instantiate c args)]) (nodeCount l) ⟨c, as⟩

/-- **The declared imports**: an imported function `f` declares `f`, an imported instance
`i` declares `i#f` for every function `f` of its instance type, with their types. -/
inductive Decls (S : Nat → PkgSig) : List Item → Iface → Prop
  | nil : Decls S [] []
  | other {l : List Item} {x : Item} {I : Iface} :
      (∀ i, x ≠ .imp i) → Decls S l I → Decls S (l ++ [x]) I
  | impFunc {l : List Item} {i : Import} {I : Iface} {ft : FuncTy} :
      Decls S l I → Den S (l ++ [.imp i]) .func (count .func l) (.inr (.imp i.name.name, ft)) →
      Decls S (l ++ [.imp i]) (I ++ [(i.name.name, ft)])
  | impInst {l : List Item} {i : Import} {I : Iface} {tab : Table} :
      Decls S l I → Den S (l ++ [.imp i]) .inst (count .inst l) (.inl (.imp i.name.name, tab)) →
      Decls S (l ++ [.imp i]) (I ++ tab.map fun p => (qual i.name.name p.1, p.2))
  | impOther {l : List Item} {i : Import} {I : Iface} :
      (descSp i.desc = some .comp ∨ descSp i.desc = some .type) →
      Decls S l I → Decls S (l ++ [.imp i]) I

/-- **The exports**: an exported function `x`, and the functions `x#f` of an exported
instance `x`. -/
inductive Exps (S : Nat → PkgSig) : List Item → List (String × Src) → Prop
  | nil : Exps S [] []
  | other {l : List Item} {x : Item} {E : List (String × Src)} :
      (∀ e, x ≠ .exp e) → Exps S l E → Exps S (l ++ [x]) E
  | func {l : List Item} {e : Binary.Export} {E : List (String × Src)} {j : Nat} {src : Src} {ft : FuncTy} :
      Exps S l E → e.item = ⟨.func, j⟩ → Den S l .func j (.inr (src, ft)) →
      Exps S (l ++ [.exp e]) (E ++ [(e.name.name, src)])
  | inst {l : List Item} {e : Binary.Export} {E : List (String × Src)} {j : Nat} {loc : Loc} {tab : Table} :
      Exps S l E → e.item = ⟨.instance, j⟩ → Den S l .inst j (.inl (loc, tab)) →
      Exps S (l ++ [.exp e]) (E ++ tab.map fun p => (qual e.name.name p.1, loc.func p.1))
  | otherSort {l : List Item} {e : Binary.Export} {E : List (String × Src)} :
      (spOfSort e.item.sort = some .comp ∨ spOfSort e.item.sort = some .type) →
      Exps S l E → Exps S (l ++ [.exp e]) E

/-- **The specification of the lowering**: the graph `g` is read from the items `l`:
its imports are the declared imports, its exports the exports, and its nodes the
instantiations, each node `k` as `NodeAt` describes it. -/
def Spec (S : Nat → PkgSig) (l : List Item) (g : Graph) : Prop :=
  Decls S l g.imports ∧ Exps S l g.exports ∧ g.nodes.length = nodeCount l ∧
    ∀ k n, g.nodes[k]? = some n → NodeAt S l k n

/-! ## The executable lowering -/

/-- The lowering state: the instance and function index spaces, the graph so far. The
type space and the number of components are kept apart (`typesOf`, `count .comp`). -/
structure TSt where
  types : List TypeEntry := []
  comps : Nat := 0
  insts : List (Loc × Table) := []
  funcs : List (Src × FuncTy) := []
  imports : Iface := []
  nodes : List Inst := []
  exports : List (String × Src) := []

/-- One argument of an instantiation of package `c`. -/
def argT (S : Nat → PkgSig) (st : TSt) (c : Nat) : String × SortIdx → Except String (List (String × Src))
  | (n, ⟨.func, j⟩) =>
    match st.funcs[j]? with
    | some (src, ft) =>
      if (S c).imports.lookup n = some ft then .ok [(n, src)]
      else .error s!"argument {n}: the function has another type than the package's import"
    | none => .error s!"argument {n}: unknown function {j}"
  | (n, ⟨.instance, j⟩) =>
    match st.insts[j]? with
    | some (loc, tab) =>
      if (instArgs (S c) n).all (fun a => decide (tab.lookup a.2.1 = some a.2.2)) then
        .ok ((instArgs (S c) n).map fun a => (a.1, loc.func a.2.1))
      else .error s!"argument {n}: the instance lacks a function of the package's import, or has another type"
    | none => .error s!"argument {n}: unknown instance {j}"
  | (_, ⟨.type, _⟩) => .ok []
  | (_, ⟨.component, _⟩) => .ok []
  | (n, _) => .error s!"argument {n}: unsupported sort"

/-- The arguments of an instantiation. -/
def argsT (S : Nat → PkgSig) (st : TSt) (c : Nat) :
    List (String × SortIdx) → Except String (List (String × Src))
  | [] => .ok []
  | a :: args => (argT S st c a).bind fun x => (argsT S st c args).map (x ++ ·)

/-- An import. -/
def importT (st : TSt) (i : Import) : Except String TSt :=
  let n := i.name.name
  match i.desc with
  | .func t =>
    match (st.types[t]? : Option TypeEntry) with
    | some (.func ft) => .ok { st with funcs := st.funcs ++ [(.imp n, ft)], imports := st.imports ++ [(n, ft)] }
    | _ => .error s!"import {n}: type {t} is not a supported function type"
  | .instance t =>
    match (st.types[t]? : Option TypeEntry) with
    | some (.inst ds) =>
      match Silmaril.Wasm.Component.Binary.Lower.instFuncs st.types.toArray ds with
      | .ok tab => .ok { st with
          insts := st.insts ++ [(.imp n, tab)]
          imports := st.imports ++ tab.map fun p => (qual n p.1, p.2) }
      | .error e => .error s!"import {n}: {e}"
    | _ => .error s!"import {n}: type {t} is not an instance type"
  | .component _ | .type _ => .ok st
  | _ => .error s!"import {n}: unsupported sort"

/-- An instance. -/
def instT (S : Nat → PkgSig) (st : TSt) : InstanceExpr → Except String TSt
  | .instantiate c args =>
    if c < st.comps then
      match argsT S st c args with
      | .ok as =>
        if explicitArgs (S c) as then
          .ok { st with
            insts := st.insts ++ [(.node st.nodes.length none, (S c).exports)]
            nodes := st.nodes ++ [⟨c, as⟩] }
        else .error s!"instantiate {c}: an import of the package has no argument"
      | .error e => .error e
    else .error s!"instantiate: unknown component index {c}"
  | .exports _ => .error "instance: outside the composition profile"

/-- An alias. -/
def aliasT (st : TSt) (a : Alias) : Except String TSt :=
  match a.target with
  | .export i n =>
    match st.insts[i]? with
    | some (loc, tab) =>
      match a.sort with
      | .func =>
        match tab.lookup n with
        | some ft => .ok { st with funcs := st.funcs ++ [(loc.func n, ft)] }
        | none => .error s!"alias {n}: no such function export"
      | .instance => .ok { st with insts := st.insts ++ [(loc.inst n, subTable n tab)] }
      | .type | .component => .ok st
      | _ => .error s!"alias {n}: unsupported sort"
    | none => .error s!"alias {n}: unknown instance {i}"
  | _ => .error "alias: outside the composition profile"

/-- An export. -/
def exportT (st : TSt) (e : Binary.Export) : Except String TSt :=
  let x := e.name.name
  match e.item with
  | ⟨.func, j⟩ =>
    match st.funcs[j]? with
    | some (src, ft) => .ok { st with exports := st.exports ++ [(x, src)], funcs := st.funcs ++ [(src, ft)] }
    | none => .error s!"export {x}: unknown function {j}"
  | ⟨.instance, j⟩ =>
    match st.insts[j]? with
    | some (loc, tab) => .ok { st with
        exports := st.exports ++ tab.map fun p => (qual x p.1, loc.func p.1)
        insts := st.insts ++ [(loc, tab)] }
    | none => .error s!"export {x}: unknown instance {j}"
  | ⟨.type, _⟩ | ⟨.component, _⟩ => .ok st
  | _ => .error s!"export {x}: unsupported sort"

/-- The step of an item, apart from the type space and the component count. -/
def stepO (S : Nat → PkgSig) (st : TSt) : Item → Except String TSt
  | .type _ | .comp => .ok st
  | .imp i => importT st i
  | .inst e => instT S st e
  | .alias a => aliasT st a
  | .exp e => exportT st e

/-- One item. -/
def stepT (S : Nat → PkgSig) (st : TSt) (x : Item) : Except String TSt :=
  (stepO S st x).map fun st' => { st' with
    types := tyStep st.types x
    comps := st.comps + (if x.sp == some .comp then 1 else 0) }

/-- The items, in order. -/
def runT (S : Nat → PkgSig) : TSt → List Item → Except String TSt
  | st, [] => .ok st
  | st, x :: xs => (stepT S st x).bind fun st' => runT S st' xs

/-- **The typed composition graph of a profile component.** -/
def graph (S : Nat → PkgSig) (c : Ast) : Except String Graph :=
  if isProfile c then
    match items c with
    | some l => (runT S {} l).map fun st => ⟨st.imports, st.nodes, st.exports⟩
    | none => .error "not in the composition profile"
  else .error "not in the composition profile"

/-- **A profile component as a component of the component IR**, given its packages. -/
def toComp {M : Type} (P : Nat → Comp M) (c : Ast) : Except String (Comp M) :=
  (graph (fun k => sigOf (P k)) c).map (Graph.toComp P)

/-- **End to end**: the packages lowered with `Binary.lower`, then composed. -/
def toCompCore (c : Ast) : Except String (Comp CoreMod) := do
  let ps ← (Lower.packages c).mapM fun
    | some d => lower d
    | none => throw "imported package: its definition is needed (wac --import-dependencies)"
  toComp (fun k => ps.getD k (.mk [] [] [])) c

end Silmaril.Wasm.Wac.LowerT
