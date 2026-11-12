module

public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Defs

/-!
# WAC bridge: `ref` of a resource as a value type, at every level

The named fragment `DecodeNamed.EsOk` fixes the forms the decoder writes back: a
resource `a` is used as `own<a>`, a resource alias `a` as `ref a`. The elaborator may
also write `ref a` for a resource (its kind of a type name used as a value type) and
`own<a>` for an alias. The encoder writes the two forms the same way (a handle
`own i` of `a`'s index), and the decoder reads them back in its own form. Also, a type
item `type n = a` or `type n = own<a>` of a resource *or of a resource alias* names
the root resource: it is read back as `own<root>`.

This module defines the larger fragment `EsOkR` (value types `TyOkR`), with value
items, and what the decoder reads back: `rdT Γ t` for a value type in the context `Γ`
(`ref a` of a resource becomes `own<a>`, `own<a>` of an alias becomes `ref a`, inside
every other type), `rdEs Γ es` for items (the same in function types, value items and
type items, in every nested instance and component, each in its own context).
`Bridge.DecodeRefVal.Thms` proves that `decodePkg` reads a package `(is, es)` of the
fragment back as `dks (rdEs [] is)`, `dks (rdEs (extendR [] is) es)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

namespace DecodeRefVal

open DecodeNamed (Ctx NS NomOk Plain)

/-! ## What the decoder reads back -/

mutual
/-- The value type the decoder reads back for `t` in the context `Γ`. -/
def rdT (Γ : Ctx) : Ty → Ty
  | .prim p => .prim p
  | .ref r =>
    match Γ.lookup r.name with
    | some .res => .own r
    | _ => .ref r
  | .own r =>
    match Γ.lookup r.name with
    | some (.ali _) => .ref r
    | _ => .own r
  | .borrow r => .borrow r
  | .list t => .list (rdT Γ t)
  | .fixedList t n => .fixedList (rdT Γ t) n
  | .map k v => .map (rdT Γ k) (rdT Γ v)
  | .option t => .option (rdT Γ t)
  | .result a b => .result (rdTo Γ a) (rdTo Γ b)
  | .tuple ts => .tuple (rdTs Γ ts)
  | .future a => .future (rdTo Γ a)
  | .stream a => .stream (rdTo Γ a)
/-- `rdT` on an optional type. -/
def rdTo (Γ : Ctx) : Option Ty → Option Ty
  | none => none
  | some t => some (rdT Γ t)
/-- `rdT` on a list of types. -/
def rdTs (Γ : Ctx) : List Ty → List Ty
  | [] => []
  | t :: ts => rdT Γ t :: rdTs Γ ts
end

/-- `rdT` on named parameters. -/
def rdPs (Γ : Ctx) : List (String × Ty) → List (String × Ty)
  | [] => []
  | (n, t) :: ps => (n, rdT Γ t) :: rdPs Γ ps

/-- The function type the decoder reads back. -/
def rdS (Γ : Ctx) (s : Sig) : Sig := { s with params := rdPs Γ s.params, result := rdTo Γ s.result }

/-- The definiens of a type item `type n = own<a>` or `type n = a` (`t`): the root
resource when `a` is a resource or an alias of one. -/
def rdAli (Γ : Ctx) (r : TyRef) (t : Ty) : Kind :=
  match Γ.lookup r.name with
  | some .res => .value (.own r)
  | some (.ali a) => .value (.own ⟨.local, a⟩)
  | _ => .value t

/-- The definiens of a value type item. -/
def rdTV (Γ : Ctx) : Ty → Kind
  | .own r => rdAli Γ r (.own r)
  | .ref r => rdAli Γ r (.ref r)
  | t => .value (rdT Γ t)

/-- What a type item of kind `k` names, in the context `Γ`. -/
def sortR (Γ : Ctx) : Kind → NS
  | .resource _ => .res
  | .value (.own r) | .value (.ref r) =>
    match Γ.lookup r.name with
    | some .res => .ali r.name
    | some (.ali a) => .ali a
    | _ => .val
  | .value _ => .val
  | _ => .other

/-- The context after one item. -/
def stepR (Γ : Ctx) : String × Kind → Ctx
  | (n, .type k) => Γ ++ [(n, sortR Γ k)]
  | _ => Γ

/-- The context after the items `es`. -/
def extendR : Ctx → Externs → Ctx
  | Γ, [] => Γ
  | Γ, x :: es => extendR (stepR Γ x) es

mutual
/-- The kind the decoder reads back for an item of kind `k` in the context `Γ`
(before `DecodeNamed.dk` adds interface identifiers). -/
def rdKd (Γ : Ctx) : Kind → Kind
  | .func s => .func (rdS Γ s)
  | .value t => .value (rdT Γ t)
  | .resource n => .resource n
  | .type k => .type (rdTB Γ k)
  | .inst i fs => .inst i (rdEs [] fs)
  | .comp i is fs => .comp i (rdEs [] is) (rdEs (extendR [] is) fs)
/-- The definiens the decoder reads back for a type item `type k`. -/
def rdTB (Γ : Ctx) : Kind → Kind
  | .value t => rdTV Γ t
  | .func s => .func (rdS Γ s)
  | .resource n => .resource n
  | .type k => .type k
  | .inst i fs => .inst i (rdEs [] fs)
  | .comp i is fs => .comp i (rdEs [] is) (rdEs (extendR [] is) fs)
/-- The items the decoder reads back, each in the context of the earlier ones. -/
def rdEs (Γ : Ctx) : Externs → Externs
  | [] => []
  | (n, k) :: es => (n, rdKd Γ k) :: rdEs (stepR Γ (n, k)) es
end

/-! ## The fragment -/

/-- **Value types of the fragment**: those of `DecodeNamed.TyOk`, and `ref a` of a
resource and `own<a>` of a resource alias. -/
inductive TyOkR (Γ : Ctx) : Ty → Prop
  | prim (p : PrimValType) : TyOkR Γ (.prim p)
  | refVal {a : String} : Γ.lookup a = some .val → TyOkR Γ (.ref ⟨.local, a⟩)
  | refAlias {a r : String} : Γ.lookup a = some (.ali r) → TyOkR Γ (.ref ⟨.local, a⟩)
  | refRes {a : String} : Γ.lookup a = some .res → TyOkR Γ (.ref ⟨.local, a⟩)
  | own {a : String} : Γ.lookup a = some .res → TyOkR Γ (.own ⟨.local, a⟩)
  | ownAlias {a r : String} : Γ.lookup a = some (.ali r) → TyOkR Γ (.own ⟨.local, a⟩)
  | borrowRes {a : String} : Γ.lookup a = some .res → TyOkR Γ (.borrow ⟨.local, a⟩)
  | borrowAlias {a r : String} : Γ.lookup a = some (.ali r) → TyOkR Γ (.borrow ⟨.local, a⟩)
  | list {t : Ty} : TyOkR Γ t → TyOkR Γ (.list t)
  | fixedList {t : Ty} (n : Nat) : TyOkR Γ t → TyOkR Γ (.fixedList t n)
  | map {k v : Ty} : TyOkR Γ k → TyOkR Γ v → TyOkR Γ (.map k v)
  | option {t : Ty} : TyOkR Γ t → TyOkR Γ (.option t)
  | result {a b : Option Ty} : (∀ t ∈ a, TyOkR Γ t) → (∀ t ∈ b, TyOkR Γ t) → TyOkR Γ (.result a b)
  | tuple {ts : List Ty} : (∀ t ∈ ts, TyOkR Γ t) → TyOkR Γ (.tuple ts)
  | future {a : Option Ty} : (∀ t ∈ a, TyOkR Γ t) → TyOkR Γ (.future a)
  | stream {a : Option Ty} : (∀ t ∈ a, TyOkR Γ t) → TyOkR Γ (.stream a)

/-- A function type over value types of the fragment. -/
def SigOkR (Γ : Ctx) (s : Sig) : Prop := (∀ p ∈ s.params, TyOkR Γ p.2) ∧ ∀ t ∈ s.result, TyOkR Γ t

/-- `own<a>` or `a`, the two ways to write an alias type item of a resource. -/
def AliForm (a : String) (t : Ty) : Prop := t = .own ⟨.local, a⟩ ∨ t = .ref ⟨.local, a⟩

/-- **Items of the fragment** in the context `Γ`, with the nominal table `N`: those of
`DecodeNamed.EsOk` over `TyOkR`, value items, and alias type items of resources and of
resource aliases written as `own<a>` or `a`, at every level. -/
inductive EsOkR (N : NomTable) : Ctx → Externs → Prop
  | nil {Γ : Ctx} : EsOkR N Γ []
  | func {Γ : Ctx} {n : String} {s : Sig} {es : Externs} :
      SigOkR Γ s → EsOkR N Γ es → EsOkR N Γ ((n, .func s) :: es)
  | value {Γ : Ctx} {n : String} {t : Ty} {es : Externs} :
      TyOkR Γ t → EsOkR N Γ es → EsOkR N Γ ((n, .value t) :: es)
  | inst {Γ : Ctx} {n : String} {i : Option String} {fs es : Externs} :
      EsOkR N [] fs → EsOkR N Γ es → EsOkR N Γ ((n, .inst i fs) :: es)
  | comp {Γ : Ctx} {n : String} {i : Option String} {is fs es : Externs} :
      EsOkR N [] is → EsOkR N (extendR [] is) fs → EsOkR N Γ es → EsOkR N Γ ((n, .comp i is fs) :: es)
  | res {Γ : Ctx} {n : String} {es : Externs} :
      EsOkR N (Γ ++ [(n, .res)]) es → EsOkR N Γ ((n, .type (.resource n)) :: es)
  | tyRes {Γ : Ctx} {n a : String} {t : Ty} {es : Externs} : AliForm a t → Γ.lookup a = some .res →
      EsOkR N (Γ ++ [(n, .ali a)]) es → EsOkR N Γ ((n, .type (.value t)) :: es)
  | tyAli {Γ : Ctx} {n a r : String} {t : Ty} {es : Externs} : AliForm a t → Γ.lookup a = some (.ali r) →
      EsOkR N (Γ ++ [(n, .ali r)]) es → EsOkR N Γ ((n, .type (.value t)) :: es)
  | tyRef {Γ : Ctx} {n a : String} {es : Externs} : Γ.lookup a = some .val →
      EsOkR N (Γ ++ [(n, .val)]) es → EsOkR N Γ ((n, .type (.value (.ref ⟨.local, a⟩))) :: es)
  | tyNom {Γ : Ctx} {n : String} {d : Nominal} {es : Externs} : Γ.lookup n = none →
      N.lookup n = some d → NomOk Γ d →
      EsOkR N (Γ ++ [(n, .val)]) es → EsOkR N Γ ((n, .type (.value (.ref ⟨.local, n⟩))) :: es)
  | tyVal {Γ : Ctx} {n : String} {t : Ty} {es : Externs} : Plain t → TyOkR Γ t →
      EsOkR N (Γ ++ [(n, .val)]) es → EsOkR N Γ ((n, .type (.value t)) :: es)
  | tyFunc {Γ : Ctx} {n : String} {s : Sig} {es : Externs} : SigOkR Γ s →
      EsOkR N (Γ ++ [(n, .other)]) es → EsOkR N Γ ((n, .type (.func s)) :: es)
  | tyInst {Γ : Ctx} {n : String} {i : Option String} {fs es : Externs} : EsOkR N [] fs →
      EsOkR N (Γ ++ [(n, .other)]) es → EsOkR N Γ ((n, .type (.inst i fs)) :: es)
  | tyComp {Γ : Ctx} {n : String} {i : Option String} {is fs es : Externs} : EsOkR N [] is →
      EsOkR N (extendR [] is) fs → EsOkR N (Γ ++ [(n, .other)]) es →
      EsOkR N Γ ((n, .type (.comp i is fs)) :: es)

end DecodeRefVal

end Silmaril.Wasm.Wac.Bridge
