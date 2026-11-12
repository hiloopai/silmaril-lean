module

public import Silmaril.Wasm.Wac.Bridge.DecodeUse.Defs

/-!
# WAC bridge: an encoder variant for resource definitions and `use`

The encoder of `Bridge.Encode` writes every interface closed and never defines a
resource, so its output contains neither `(alias outer 0 …)` in the projected world nor
aliases of types of imported interfaces. This module is a second, small encoder for the
two layouts that `decodePkgU` (`Bridge.DecodeUse`) was written for:

* **Components that define and export resources** (`resComp rs`): for each name `r` of
  `rs`, a resource definition `(type (resource (rep i32)))` followed by its export
  `(export "r" (type k))`. The projection (`Wit.Project.projectX`) hoists each export
  before the definition and writes the component's own export as
  `(alias outer 0 k (type))` (`resWorld`). `DecodeGaps.cRes` is `resComp ["r"]`.
* **WIT packages of interfaces that use resources of other interfaces** (`usePkg items`,
  in wit-component's layout: `Wit.Project.itemsPackage`). An interface (`UIface`) has
  - used resources (`UseT`): `use I.{t as l}` of a resource `t` of the interface `I`
    (identifier `iid`). Its wrapper component type defines the instance type
    `(instance (export "t" (type (sub resource))))`, imports `iid` of that type and
    aliases its export `t`; the interface's instance type refers to it by
    `(alias outer 1 k (type))` and exports it as `l` by `(type (eq _))`;
  - resources it defines, `(export "r" (type (sub resource)))`;
  - functions whose parameters are primitive or `own`/`borrow` of a used or own
    resource (`UPar`). Every parameter type is defined as a type of its own before
    the function type (also primitive ones: a simplification against wit-component,
    which writes primitive types inline).

  The wrapper exports the instance type under the interface's identifier.
  `DecodeGaps.pkgAB` is `usePkg [("foo:bar/a", uA), ("foo:bar/b", uB)]`.

The expected readings are `resPkg rs` (one resource definition per name) and
`usePkgRd items` (one interface per item, with items `rdIface u`: `WitDecl.usedKind I t`
for each used type, `.type (.resource r)` for each own resource, and the functions over
`Ty.own`/`Ty.borrow` of `⟨.iface I, t⟩` or `⟨.local, r⟩`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner IfaceName)

namespace EncodeUse

/-! ## Components that define resources -/

/-- The sections of resources defined and exported, the first at type index `2 k`. -/
def resSecs : Nat → List String → List Section
  | _, [] => []
  | k, r :: rs => .types [.resource .i32 none] :: .exports [⟨⟨r, .plain0⟩, ⟨.type, 2 * k⟩, none⟩] :: resSecs (k + 1) rs

/-- **A component defining and exporting the resources `rs`.** -/
def resComp (rs : List String) : Ast := .mk (resSecs 0 rs)

/-- Its world: each resource hoisted as an export, then `alias outer 0` of it. -/
def resWorld : Nat → List String → Wit.Project.WorldType
  | _, [] => []
  | k, r :: rs => .inst (.export ⟨r, .plain0⟩ (.type .subResource)) :: .inst (.alias ⟨.type, .outer 0 (2 * k)⟩) ::
      resWorld (k + 1) rs

/-- The expected reading: one resource definition per name. -/
def resPkg (rs : List String) : PkgType :=
  { imports := [], exports := [], defs := rs.map fun r => (defName r, .type (.resource r)) }

/-! ## Interfaces that use resources of other interfaces -/

/-- `use I.{t as l}` of a resource `t` of the interface `I`, identifier `iid`. -/
structure UseT where
  iid : String
  I : IfaceName
  t : String
  l : String

/-- A resource a function parameter refers to: the `j`-th used one, or the `j`-th own one. -/
inductive URes where
  | used (j : Nat)
  | own (j : Nat)

/-- A function parameter type. -/
inductive UPar where
  | prim (p : PrimValType)
  | own (r : URes)
  | borrow (r : URes)

/-- An interface: used resources, own resources, functions (no results). -/
structure UIface where
  uses : List UseT := []
  res : List String := []
  funcs : List (String × List (String × UPar)) := []

/-! ### The wrapper component type -/

/-- The declarations of the used interfaces, the first at type index `2 k` and instance `k`:
its instance type, its import, the alias of its type export. -/
def useDecls : Nat → List UseT → List ComponentDecl
  | _, [] => []
  | k, e :: es => .inst (.type (.instance [.export ⟨e.t, .plain0⟩ (.type .subResource)])) ::
      .import ⟨e.iid, .plain0⟩ (.instance (2 * k)) :: .inst (.alias ⟨.type, .export k e.t⟩) :: useDecls (k + 1) es

/-- Inside the interface's instance type: the used types, from the outer type `2 k + 1`. -/
def useAliases : Nat → List UseT → List InstanceDecl
  | _, [] => []
  | k, _ :: es => .alias ⟨.type, .outer 1 (2 * k + 1)⟩ :: useAliases (k + 1) es

/-- Their exports under the local names, from the type `k` on. -/
def useExports : Nat → List UseT → List InstanceDecl
  | _, [] => []
  | k, e :: es => .export ⟨e.l, .plain0⟩ (.type (.eq k)) :: useExports (k + 1) es

/-- The own resources. -/
def resExports : List String → List InstanceDecl
  | [] => []
  | r :: rs => .export ⟨r, .plain0⟩ (.type .subResource) :: resExports rs

/-- The type index of a resource, for `nu` used ones. -/
def URes.idx (nu : Nat) : URes → Nat
  | .used j => nu + j
  | .own j => 2 * nu + j

/-- The defined type of a parameter. -/
def UPar.def (nu : Nat) : UPar → DefValType
  | .prim p => .prim p
  | .own r => .own (r.idx nu)
  | .borrow r => .borrow (r.idx nu)

/-- The parameters as value types, the first at type index `c`. -/
def parVals : Nat → List (String × UPar) → List (String × Silmaril.Wasm.Component.Binary.ValType)
  | _, [] => []
  | c, (x, _) :: ps => (x, .idx c) :: parVals (c + 1) ps

/-- The declarations of the functions, from the type index `c` on: the parameter types,
the function type, the export. -/
def funcDecls (nu : Nat) : Nat → List (String × List (String × UPar)) → List InstanceDecl
  | _, [] => []
  | c, (f, ps) :: fs =>
    ps.map (fun p => .type (.val (p.2.def nu))) ++
      [.type (.func ⟨parVals c ps, none, false⟩), .export ⟨f, .plain0⟩ (.func (c + ps.length))] ++
      funcDecls nu (c + ps.length + 1) fs

/-- The interface's instance type. -/
def ifaceBody (u : UIface) : List InstanceDecl :=
  useAliases 0 u.uses ++ useExports 0 u.uses ++ resExports u.res ++
    funcDecls u.uses.length (2 * u.uses.length + u.res.length) u.funcs

/-- **The wrapper component type of an interface** with identifier `id`. -/
def ifaceDefU (id : String) (u : UIface) : DefType :=
  .component (useDecls 0 u.uses ++
    [.inst (.type (.instance (ifaceBody u))), .inst (.export ⟨id, .plain0⟩ (.instance (2 * u.uses.length)))])

/-- **A WIT package of interfaces that use resources of each other.** -/
def usePkg (items : List (String × UIface)) : Ast :=
  Wit.Project.itemsPackage (items.map fun p => (p.1, ifaceDefU p.1 p.2)) []

/-! ### The expected reading -/

/-- The reference of a resource. -/
def URes.rd (u : UIface) : URes → TyRef
  | .used j => match u.uses[j]? with
    | some e => ⟨.iface e.I, e.t⟩
    | none => ⟨.local, ""⟩
  | .own j => ⟨.local, u.res.getD j ""⟩

/-- The type of a parameter. -/
def UPar.rd (u : UIface) : UPar → Silmaril.Wasm.Wit.Binary.Ty
  | .prim p => .prim p
  | .own r => .own (r.rd u)
  | .borrow r => .borrow (r.rd u)

/-- The signature of a function. -/
def sigRd (u : UIface) (ps : List (String × UPar)) : Sig :=
  ⟨false, ps.map fun p => (p.1, p.2.rd u), none⟩

/-- **The items of an interface**, as the elaborator writes them. -/
def rdIface (u : UIface) : Externs :=
  u.uses.map (fun e => (e.l, WitDecl.usedKind e.I e.t)) ++
    u.res.map (fun r => (r, .type (.resource r))) ++
    u.funcs.map fun f => (f.1, .func (sigRd u f.2))

/-- The reading of a package of interfaces. -/
def usePkgRd (items : List (String × UIface)) : PkgType :=
  { imports := [], exports := [],
    defs := items.map fun p => (defName p.1, .type (.inst (some p.1) (rdIface p.2))) }

/-! ### Well-formedness -/

/-- A resource reference in range. -/
def URes.Ok (u : UIface) : URes → Prop
  | .used j => j < u.uses.length
  | .own j => j < u.res.length

/-- A parameter in range. -/
def UPar.Ok (u : UIface) : UPar → Prop
  | .prim _ => True
  | .own r => r.Ok u
  | .borrow r => r.Ok u

/-- An interface whose used interfaces are interface identifiers (`ifaceOf`) and whose
parameters refer to resources in range. -/
structure UIface.Ok (u : UIface) : Prop where
  uses : ∀ e ∈ u.uses, DecodeUse.ifaceOf e.iid = some e.I
  pars : ∀ f ∈ u.funcs, ∀ p ∈ f.2, p.2.Ok u

end EncodeUse

end Silmaril.Wasm.Wac.Bridge
