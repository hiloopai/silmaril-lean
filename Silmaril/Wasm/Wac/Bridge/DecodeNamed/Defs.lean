module

public import Silmaril.Wasm.Wac.Bridge.Decode.Defs

/-!
# WAC bridge: the named fragment of `decode ∘ encode`

`Bridge.DecodeEnc`, `Bridge.DecodeIface`, `Bridge.DecodeAnon` and `Bridge.DecodeAnonIface`
prove `decode ∘ encode = id` for functions over anonymous value types and interfaces of
them. This module defines the larger fragment of `Bridge.DecodeNamed.Thms`: packages
whose items are

* functions over value types that may name types (`TyOk`): named value types
  (`ref`), resources (`own`, `borrow`) and resource aliases (`ref`, `borrow`), besides
  the anonymous types;
* type items (`EsOk.res`, `tyOwn`, `tyRef`, `tyNom`, `tyVal`, `tyFunc`, `tyInst`,
  `tyComp`): resources, aliases of resources, aliases of named value types, records,
  variants, enums and flags (taken from the encoder's nominal table, `NomOk`),
  anonymous value types, function, instance and component types;
* instances and components, nested arbitrarily (their items are closed: the encoder
  starts a fresh scope for them, so they name only their own types).

A type name stands for one of four things (`NS`), recorded in a context (`Ctx`) that the
type items extend, in order (`extend`; lookups find the first entry, as the encoder's
`names` do). The fragment fixes the forms the decoder writes back, the conventions of
the elaborator's `witTy`/`witTypeKind`: a resource is referred to as `own r`, an alias
`r2` of a resource as `ref r2`, an alias type item of a resource is `own r` of the
resource itself, and a record `n` is the type item `n` of `ref n`. The decoder reads an
item `n` back as `dk n`: instances and components get the interface identifier their
name carries (`ifaceId`), recursively.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

namespace DecodeNamed

/-! ## Contexts -/

/-- What a type name stands for. -/
inductive NS where
  /-- A resource defined under this name. -/
  | res
  /-- A name of the resource `root` (`type r2 = own<r>`). -/
  | ali (root : String)
  /-- A named value type: an alias of one, or a record, variant, enum or flags. -/
  | val
  /-- A function, instance or component type. -/
  | other

/-- The type names in scope, in order (a lookup finds the first). -/
abbrev Ctx := List (String × NS)

/-- What a type item of kind `k` names. -/
def sortOf : Kind → NS
  | .resource _ => .res
  | .value (.own r) => .ali r.name
  | .value _ => .val
  | _ => .other

/-- The context after the items `es`: each type item adds its name. -/
def extend : Ctx → Externs → Ctx
  | Γ, [] => Γ
  | Γ, (n, .type k) :: es => extend (Γ ++ [(n, sortOf k)]) es
  | Γ, _ :: es => extend Γ es

/-! ## Value types -/

/-- **Value types of the fragment** in the context `Γ`. -/
inductive TyOk (Γ : Ctx) : Silmaril.Wasm.Wit.Binary.Ty → Prop
  | prim (p : PrimValType) : TyOk Γ (.prim p)
  | refVal {a : String} : Γ.lookup a = some .val → TyOk Γ (.ref ⟨.local, a⟩)
  | refAlias {a r : String} : Γ.lookup a = some (.ali r) → TyOk Γ (.ref ⟨.local, a⟩)
  | own {a : String} : Γ.lookup a = some .res → TyOk Γ (.own ⟨.local, a⟩)
  | borrowRes {a : String} : Γ.lookup a = some .res → TyOk Γ (.borrow ⟨.local, a⟩)
  | borrowAlias {a r : String} : Γ.lookup a = some (.ali r) → TyOk Γ (.borrow ⟨.local, a⟩)
  | list {t : Silmaril.Wasm.Wit.Binary.Ty} : TyOk Γ t → TyOk Γ (.list t)
  | fixedList {t : Silmaril.Wasm.Wit.Binary.Ty} (n : Nat) : TyOk Γ t → TyOk Γ (.fixedList t n)
  | map {k v : Silmaril.Wasm.Wit.Binary.Ty} : TyOk Γ k → TyOk Γ v → TyOk Γ (.map k v)
  | option {t : Silmaril.Wasm.Wit.Binary.Ty} : TyOk Γ t → TyOk Γ (.option t)
  | result {a b : Option Silmaril.Wasm.Wit.Binary.Ty} : (∀ t ∈ a, TyOk Γ t) → (∀ t ∈ b, TyOk Γ t) → TyOk Γ (.result a b)
  | tuple {ts : List Silmaril.Wasm.Wit.Binary.Ty} : (∀ t ∈ ts, TyOk Γ t) → TyOk Γ (.tuple ts)
  | future {a : Option Silmaril.Wasm.Wit.Binary.Ty} : (∀ t ∈ a, TyOk Γ t) → TyOk Γ (.future a)
  | stream {a : Option Silmaril.Wasm.Wit.Binary.Ty} : (∀ t ∈ a, TyOk Γ t) → TyOk Γ (.stream a)

/-- A function type over value types of the fragment. -/
def SigOk (Γ : Ctx) (s : Sig) : Prop := (∀ p ∈ s.params, TyOk Γ p.2) ∧ ∀ t ∈ s.result, TyOk Γ t

/-- A nominal definition over value types of the fragment. -/
def NomOk (Γ : Ctx) : Nominal → Prop
  | .record fs => ∀ f ∈ fs, TyOk Γ f.2
  | .variant cs => ∀ c ∈ cs, ∀ t ∈ c.2, TyOk Γ t
  | .enum _ => True
  | .flags _ => True

/-- The definiens of a type item that the encoder defines anew or as a handle (neither a
named reference nor `own`). -/
def Plain : Silmaril.Wasm.Wit.Binary.Ty → Prop
  | .ref _ | .own _ => False
  | _ => True

/-! ## Items -/

/-- **Items of the fragment** in the context `Γ`, with the nominal table `N`. -/
inductive EsOk (N : NomTable) : Ctx → Externs → Prop
  | nil {Γ : Ctx} : EsOk N Γ []
  | func {Γ : Ctx} {n : String} {s : Sig} {es : Externs} :
      SigOk Γ s → EsOk N Γ es → EsOk N Γ ((n, .func s) :: es)
  | inst {Γ : Ctx} {n : String} {i : Option String} {fs es : Externs} :
      EsOk N [] fs → EsOk N Γ es → EsOk N Γ ((n, .inst i fs) :: es)
  | comp {Γ : Ctx} {n : String} {i : Option String} {is fs es : Externs} :
      EsOk N [] is → EsOk N (extend [] is) fs → EsOk N Γ es → EsOk N Γ ((n, .comp i is fs) :: es)
  | res {Γ : Ctx} {n : String} {es : Externs} :
      EsOk N (Γ ++ [(n, .res)]) es → EsOk N Γ ((n, .type (.resource n)) :: es)
  | tyOwn {Γ : Ctx} {n a : String} {es : Externs} : Γ.lookup a = some .res →
      EsOk N (Γ ++ [(n, .ali a)]) es → EsOk N Γ ((n, .type (.value (.own ⟨.local, a⟩))) :: es)
  | tyRef {Γ : Ctx} {n a : String} {es : Externs} : Γ.lookup a = some .val →
      EsOk N (Γ ++ [(n, .val)]) es → EsOk N Γ ((n, .type (.value (.ref ⟨.local, a⟩))) :: es)
  | tyNom {Γ : Ctx} {n : String} {d : Nominal} {es : Externs} : Γ.lookup n = none →
      N.lookup n = some d → NomOk Γ d →
      EsOk N (Γ ++ [(n, .val)]) es → EsOk N Γ ((n, .type (.value (.ref ⟨.local, n⟩))) :: es)
  | tyVal {Γ : Ctx} {n : String} {t : Silmaril.Wasm.Wit.Binary.Ty} {es : Externs} : Plain t → TyOk Γ t →
      EsOk N (Γ ++ [(n, .val)]) es → EsOk N Γ ((n, .type (.value t)) :: es)
  | tyFunc {Γ : Ctx} {n : String} {s : Sig} {es : Externs} : SigOk Γ s →
      EsOk N (Γ ++ [(n, .other)]) es → EsOk N Γ ((n, .type (.func s)) :: es)
  | tyInst {Γ : Ctx} {n : String} {i : Option String} {fs es : Externs} : EsOk N [] fs →
      EsOk N (Γ ++ [(n, .other)]) es → EsOk N Γ ((n, .type (.inst i fs)) :: es)
  | tyComp {Γ : Ctx} {n : String} {i : Option String} {is fs es : Externs} : EsOk N [] is →
      EsOk N (extend [] is) fs → EsOk N (Γ ++ [(n, .other)]) es →
      EsOk N Γ ((n, .type (.comp i is fs)) :: es)

/-! ## What the decoder reads back -/

mutual
/-- The kind the decoder reads back for an item named `n`: instances and components get
the interface identifier their name carries, recursively. -/
def dk (n : String) : Kind → Kind
  | .inst _ fs => .inst (ifaceId n) (dks fs)
  | .comp _ is es => .comp (ifaceId n) (dks is) (dks es)
  | .type k => .type (dk n k)
  | k => k
/-- `dk` on named items. -/
def dks : Externs → Externs
  | [] => []
  | (n, k) :: es => (n, dk n k) :: dks es
end

/-- The decoder's type information for a cached instance or component kind. -/
def infoK : Kind → TInfo
  | .inst _ fs => .inst (dks fs)
  | .comp _ is es => .comp (dks is) (dks es)
  | .func s => .func s
  | _ => .val (.tuple [])

/-- The package `pkgOfWorld` assembles from the imports and exports it reads. -/
def pkgOf (is es : Externs) : PkgType :=
  { imports := is, exports := es.filter (fun p => match p.2 with | .type _ => false | _ => true),
    defs := es.filterMap fun
      | (n, .type k) => some (defName n, .type (unwrapDef k))
      | _ => none }

end DecodeNamed

end Silmaril.Wasm.Wac.Bridge
