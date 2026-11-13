module

public import Silmaril.Project.Defs
public import Silmaril.Project.WasmComponents.Code.Defs
public import Silmaril.Wasm.Wac.Bridge.Compose.Defs
public import Silmaril.Wasm.Wac.Lower.Defs
public import Silmaril.Wasm.Wac.World.Defs
public import Silmaril.Wasi.Component.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Defs

/-!
# Standard problem shapes: WAC compositions, elaborated and typed

Three shapes about WAC compositions, beyond the names-and-sorts shapes of
`Silmaril.Project.Shapes.Component.Wac`:

| name | Lean | statement |
|---|---|---|
| `silmaril.shapes.component.wac_composes` | `WacComposes pkgs src out` | the WAC source `src` (format `wac.text`), elaborated against the packages `pkgs` (registry values, by package key) by WAC's elaborator and encoded with the packages defined in place (`composeDefined`), is the composition `out` without its custom sections |
| `silmaril.shapes.component.wac_has_typed_world` | `WacHasTypedWorld imps c W` | `c` is in the composition profile, its typed world (`Wac.World.profileWorld`, from the kinds of its embedded packages) exists and is a **subtype** of the world `W` (`Wac.World.Sat`) |
| (denotation) | `wacDen C L c` | the WASI model of a component: through `Wac.Lower.toCompCore` for a composition in the profile, through `Binary.lower` otherwise |

## The elaboration pipeline (`composeDefined`)

`wac compose` reads a document and its packages and writes a component. the library's side of the
pipeline is WAC's bridge (`Silmaril.Wasm.Wac.Bridge`, `docs/projects/wasm-wasi.md`, "The bridge"):

1. `Bridge.ofDoc`: the text AST (the value of `wac.text`) as the elaboration AST;
2. the packages' kinds: for each package key, the WIT projection of the package component
   (`Wit.Project.projectI`), read as kinds by `Bridge.pkgOfWorld` (what `Bridge.decodePkg`
   does after parsing; here the packages are already ASTs, the values of their files);
3. `Wac.elabDocA`: WAC's elaborator, to a composition graph (`CGraph`);
4. `Bridge.encode`: the graph as a component in the composition profile, written as
   `wac compose --import-dependencies` writes it (each package imported as
   `unlocked-dep=<ns:name>` of its component type);
5. `defineDeps` (here): the packages **defined in place**, as `wac compose` writes them by
   default (wac-graph's `define_components = true`): each package import becomes the
   package's `component` section and the type sections written for it are dropped.

`defineDeps` is the `define_components` switch as a pass on the encoding. It is partial.
`composeDefined` applies it only to graphs without import nodes (`noOwnImports`), whose
encoding imports nothing but packages, each once, in the order of their first instantiation
(`instKeys`, the order of `Bridge.encPackage`); so the `k`-th component import is the
package of the `k`-th key. Packages are matched by that order, not by the
`unlocked-dep=<…>` import name: `Bridge.depName` uses `String.splitOn`, which the kernel
does not evaluate. `defineDeps` also requires every type section to be followed by (more
type sections and then) a component import, and no instantiation argument or export to
refer to a type. Then the dropped type indices are used by the package imports only, and
the component index space is unchanged (one `component` section per package import, in
order). Compositions with imports or type definitions of their own are rejected; extending
the pass to them needs a renumbering of the type index space.

Not modelled: the custom sections `wac compose` adds (`component-name`, `producers`), which
is why `WacComposes` compares `out` without them (`stripCustom`; the profile, its surface
world, its IR lowering and `wacDen` all ignore custom sections).

## Typed targets

`WacHasTypedWorld` is `wac targets` with types: component subtyping of the composition's
world (`imports`, `exports` with kinds) against the target world, as wac-types'
`validate_target` checks it. The composition may import fewer items, at supertypes, and
export more items, at subtypes. The kinds of the composition's own imports are an input
(`imps`, by name), since the profile reader does not decode import types; the kinds of the
embedded packages are read off their WIT projection (`pkgKinds`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open Silmaril.Project (Value)
open Silmaril.Wasm Silmaril.Wasm.Wac
open Silmaril.Wasm.Component.Binary (Ast Section Import)

/-! ## The packages -/

/-- The kinds of a package component: its WIT projection, read as kinds. -/
def pkgTypeOf (c : Ast) : Except String (PkgType × Bridge.NomTable) :=
  match Wit.Project.projectI c with
  | some w => Bridge.pkgOfWorld w
  | none => .error "the package's world cannot be projected"

/-- The package environment and nominal table of a list of packages, by package key. -/
def pkgEnvOf (pkgs : List (String × Ast)) : Except String (PkgEnv × Bridge.NomTable) := do
  let ps ← pkgs.mapM fun p => do
    let (t, n) ← pkgTypeOf p.2
    pure ((p.1, t), n)
  pure (ps.map (·.1), ps.flatMap (·.2))

/-! ## Defining the packages in place -/

/-- Is an import a component import? -/
def isCompImport (i : Silmaril.Wasm.Component.Binary.Import) : Bool :=
  match i.desc with
  | .component _ => true
  | _ => false

/-- Do the next sections start with (more type sections and then) a component import? -/
def feedsComp : List Section → Bool
  | .types _ :: rest => feedsComp rest
  | .imports [i] :: _ => isCompImport i
  | _ => false

/-- Does a section refer to the type index space (an instantiation argument or an export of
sort `type`)? -/
def refersToTypes : Section → Bool
  | .instances xs => xs.any fun
    | .instantiate _ as => as.any fun a => a.2.sort == .type
    | .exports es => es.any fun e => e.2.sort == .type
  | .exports xs => xs.any fun e => e.item.sort == .type
  | _ => false

/-- **The packages defined in place** (`define_components = true`): the `k`-th component
import becomes the `component` section of the package of the `k`-th key of `ks`; the type
sections written for component imports are dropped. Partial (see the module
documentation). -/
def defineSecs (pkgs : List (String × Ast)) :
    List String → List Section → Except String (List Section)
  | _, [] => .ok []
  | ks, .types _ :: rest =>
    if feedsComp rest then defineSecs pkgs ks rest
    else .error "a type section not used by a package import"
  | k :: ks, .imports [i] :: rest =>
    if isCompImport i then
      match pkgs.lookup k with
      | some c => (Section.component c :: ·) <$> defineSecs pkgs ks rest
      | none => .error s!"package {k}: not given"
    else .error "an import that is not a package import"
  | _, .imports _ :: _ => .error "an import that is not a package import"
  | ks, s :: rest =>
    if refersToTypes s then .error "a section refers to a type"
    else (s :: ·) <$> defineSecs pkgs ks rest

/-- `defineSecs` on a component. -/
def defineDeps (pkgs : List (String × Ast)) (ks : List String) (c : Ast) : Except String Ast :=
  (defineSecs pkgs ks c.sections).map .mk

/-- The packages a composition graph instantiates, in the order of their first
instantiation (the order in which `Bridge.encode` imports them). -/
def instKeys (g : CGraph) : List String :=
  (g.nodes.filterMap fun nd => match nd.op with
    | .inst key _ _ => some key
    | _ => none).eraseDups

/-- Does a composition graph have no imports of its own? -/
def noOwnImports (g : CGraph) : Bool := g.nodes.all fun nd => !Bridge.isImportNode nd

/-- **The composition of a WAC document** against packages (by package key), with the
packages defined in place: `ofDoc`, WAC's elaborator (`elabDocA`), the encoder of the
bridge and `defineDeps`. Defined for compositions without imports of their own, whose
encoding imports only packages, in the order of `instKeys`. -/
def composeDefined (pkgs : List (String × Ast)) (d : Wac.Text.Document) : Except String Ast := do
  let sd ← Bridge.ofDoc d
  let (env, nom) ← pkgEnvOf pkgs
  let g ← Bridge.elabStr env sd
  if !noOwnImports g then throw "a composition with imports of its own"
  let c ← Bridge.encode (Bridge.docNom sd ++ nom) g
  defineDeps pkgs (instKeys g) c

/-- The parses of a list of registry values, by key. -/
def parseAll (pkgs : List (String × Value Ast)) : Option (List (String × Ast)) :=
  pkgs.mapM fun p => p.2.parse.map (p.1, ·)

/-- **The WAC source `src` composes to `out`**: the source parses (under `wac.text`), the
packages parse, `out` parses, and the composition of the document against the packages
(`composeDefined`) is `out` without its custom sections. -/
@[problem "silmaril.shapes.component.wac_composes"
  (title := "A WAC source composes, by WAC's elaborator, to a given component")]
def WacComposes (pkgs : List (String × Value Ast)) (src : Value Wac.Text.Document)
    (out : Value Ast) : Prop :=
  ∃ d ps c, src.parse = some d ∧ parseAll pkgs = some ps ∧ out.parse = some c ∧
    composeDefined ps d = .ok (Silmaril.Project.WasmComponents.stripCustom c)

/-! ## Typed targets -/

/-- The kind of a package component: the component type of its imports and exports. -/
def pkgKind (c : Ast) : Except String Kind :=
  (pkgTypeOf c).map fun p => .comp none p.1.imports p.1.exports

/-- The kinds of the embedded packages of a composition, in component index order (an
imported component, whose kind comes from the import kinds, gets a placeholder). -/
def pkgKinds (c : Ast) : Except String (List Kind) :=
  (Wac.Lower.packages c).mapM fun
    | some d => pkgKind d
    | none => .ok (.comp none [] [])

/-- The typed world of a composition, given the kinds of its own imports. -/
def typedWorld (imps : Externs) (c : Ast) : Except String World.WorldK := do
  let ks ← pkgKinds c
  World.profileWorld (fun k => ks.getD k (.comp none [] [])) imps c

/-- **The WAC composition `c` has the world `W`, with types**: `c` is in the composition
profile and its typed world is a subtype of `W` (fewer imports at supertypes, more exports
at subtypes; `Wac.World.Sat`). -/
@[problem "silmaril.shapes.component.wac_has_typed_world"
  (title := "A WAC composition has a given world (component subtyping)")]
def WacHasTypedWorld (imps : Externs) (c : Ast) (W : World.WorldK) : Prop :=
  Wac.Profile c ∧ ∃ cw, typedWorld imps c = .ok cw ∧ World.Sat cw W

/-- The decision procedure of `WacHasTypedWorld`. -/
def wacHasTypedWorld (imps : Externs) (c : Ast) (W : World.WorldK) : Bool :=
  Wac.isProfile c &&
    match typedWorld imps c with
    | .ok cw => World.sat cw W
    | .error _ => false

/-! ## A denotation for compositions and components -/

/-- The IR of a component: through WAC's lowering for a composition in the profile, through
`Binary.lower` otherwise. -/
def irOf (c : Ast) : Except String (Silmaril.Wasm.Component.Comp Silmaril.Wasm.Component.Binary.CoreMod) :=
  if Wac.isProfile c then Wac.Lower.toCompCore c else Silmaril.Wasm.Component.Binary.lower c

/-- **The WASI model of a component or composition** under the core semantics `C` and the
names `L` (the bottom model when it has no IR). -/
def wacDen (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) (c : Ast) : L.world.Model :=
  match irOf c with
  | .ok m => L.compModel C m
  | .error _ => ⊥

/-! ## Comparing flat components

`Linked CoreMod` has no `DecidableEq` (its `Target.const` answers carry payloads with
floats), so two flat components are compared by `linkedEq`, which accepts only call
targets. It is sound (`eq_of_linkedEq`, `Silmaril.Project.Shapes.Component.WacElab.Thms`). -/

/-- Equal call targets (constant answers are never accepted). -/
def tgtEq : Silmaril.Wasm.Component.Target → Silmaril.Wasm.Component.Target → Bool
  | .call a, .call b => a == b
  | _, _ => false

/-- Equal wiring programs with call targets. -/
def implEq (a b : Silmaril.Wasm.Component.Impl) : Bool :=
  decide (a.chain = b.chain) && tgtEq a.target b.target

/-- Pointwise comparison of two lists. -/
def listEq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listEq f as bs
  | _, _ => false

/-- Equal exports. -/
def exportEq (a b : Silmaril.Wasm.Component.Export) : Bool :=
  decide (a.name = b.name) && decide (a.ty = b.ty) && implEq a.impl b.impl

/-- Equal core modules. -/
def coreEq (a b : Silmaril.Wasm.Component.Binary.CoreMod) : Bool :=
  decide (a.bytes = b.bytes) && decide (a.importNames = b.importNames) &&
    decide (a.imports = b.imports) && decide (a.exports = b.exports)

/-- Equal core instances. -/
def nodeEq (a b : Silmaril.Wasm.Component.Binary.CoreMod × List Silmaril.Wasm.Component.Impl) : Bool :=
  coreEq a.1 b.1 && listEq implEq a.2 b.2

/-- Equal flat components (call targets only). -/
def linkedEq (a b : Silmaril.Wasm.Component.Linked Silmaril.Wasm.Component.Binary.CoreMod) : Bool :=
  decide (a.imports = b.imports) && listEq nodeEq a.nodes b.nodes && listEq exportEq a.exports b.exports

/-! ## Flattening with fuel

`Silmaril.Wasm.Component.flattenNodes` recurses into nested components by well-founded
recursion, which the kernel does not evaluate. `flattenNodesF` is the same function with a
fuel argument, structural in the fuel; it answers `none` when the fuel runs out, and agrees
with `flattenNodes` whenever it answers (`flattenNodesF_sound`). -/

section Fuel

open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- `flattenNodes` with fuel (one unit per call). -/
def flattenNodesF : Nat → List Impl → Nat → List (Node M) →
    Option (List Impl × Nat × List (M × List Impl))
  | 0, _, _, _ => none
  | _ + 1, σ, eB, [] => some (σ, eB, [])
  | f + 1, σ, eB, .core m args :: ns =>
    let w := (CoreModule.exports m).length
    (flattenNodesF f (σ ++ (List.range w).map fun i => Impl.fwd (eB + i)) (eB + w) ns).map
      fun r => (r.1, r.2.1, (m, args.map (Impl.subst σ)) :: r.2.2)
  | f + 1, σ, eB, .inst (.mk I ns' xs') args :: ns =>
    let σc := (List.range I.length).map fun i => (args[i]?.getD Impl.trap).subst σ
    (flattenNodesF f σc eB ns').bind fun rc =>
      (flattenNodesF f (σ ++ xs'.map fun x => x.impl.subst rc.1) rc.2.1 ns).map
        fun r => (r.1, r.2.1, rc.2.2 ++ r.2.2)

/-- `flatten` with fuel. -/
def flattenF (f : Nat) : Comp M → Option (Linked M)
  | .mk I ns xs =>
    (flattenNodesF f ((List.range I.length).map Impl.fwd) I.length ns).map fun r =>
      ⟨I, r.2.2, xs.map fun x => { x with impl := x.impl.subst r.1 }⟩

end Fuel

/-- The fuel `sameFlat` gives `flattenF`. -/
def flatFuel : Nat := 1000

/-- **The same flattening**: both components have an IR (`irOf`) and the flat components of
their IRs (`flattenF`, with `flatFuel`) are equal (`linkedEq`). A decision procedure for a
sufficient condition of equal denotations (`wacDen_eq_of_sameFlat`). -/
def sameFlat (a b : Ast) : Bool :=
  match irOf a, irOf b with
  | .ok p, .ok q =>
    match flattenF flatFuel p, flattenF flatFuel q with
    | some x, some y => linkedEq x y
    | _, _ => false
  | _, _ => false

end Silmaril.Project.Shapes.Component

end
