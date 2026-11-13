module

public import Silmaril.Wasm.Types

/-!
# WIT value types

A structural presentation of the value-type families in the Component Model
WIT design. Named references and nominal resource identities are parameters;
`ClosedType` is the reference-free input used by the canonical ABI. This is not
a WIT text parser or a package-name resolver.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v

inductive Primitive where
  | bool | u8 | u16 | u32 | u64 | s8 | s16 | s32 | s64 | f32 | f64 | char | string
  deriving Repr, DecidableEq

/-- The restricted key types admitted by WIT `map`. -/
inductive KeyType where
  | bool | u8 | u16 | u32 | u64 | s8 | s16 | s32 | s64 | char | string
  deriving Repr, DecidableEq

def KeyType.toPrimitive : KeyType → Primitive
  | .bool => .bool | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64
  | .s8 => .s8 | .s16 => .s16 | .s32 => .s32 | .s64 => .s64 | .char => .char | .string => .string

/-- Resolved type structure, with explicit slots for unresolved names. Resource
identities remain nominal even after names have been resolved. Feature gates
are recorded separately by consumers; syntax alone does not enable a feature. -/
inductive ValType (Ref : Type u) (Resource : Type v) where
  | prim (type : Primitive)
  | ref (name : Ref)
  | list (element : ValType Ref Resource)
  | fixedList (element : ValType Ref Resource) (length : Nat)
  | record (fields : List (String × ValType Ref Resource))
  | tuple (fields : List (ValType Ref Resource))
  | variant (cases : List (String × Option (ValType Ref Resource)))
  | enum (cases : List String)
  | flags (labels : List String)
  | option (element : ValType Ref Resource)
  | result (ok error : Option (ValType Ref Resource))
  | map (key : KeyType) (value : ValType Ref Resource)
  | own (resource : Resource)
  | borrow (resource : Resource)
  | future (element : Option (ValType Ref Resource))
  | stream (element : Option (ValType Ref Resource))
  | errorContext
  deriving Repr

abbrev ClosedType (Resource : Type u) := ValType Empty Resource
abbrev NamedType (Resource : Type u) := ValType String Resource

/-- WIT functions have at most one result type; multiple values are represented
by a tuple or record. Parameter names are retained independently of layout. -/
structure FuncType (Ref : Type u) (Resource : Type v) where
  params : List (String × ValType Ref Resource)
  result : Option (ValType Ref Resource)
  async_ : Bool := false
  deriving Repr

/-- Structural WIT type well-formedness, relative to a name/resource context.
Package resolution, identifier spelling, feature enablement and function-level
borrow/lifetime restrictions are separate obligations. The flags bound follows
the pinned canonical-ABI design's current 32-label limit. -/
inductive ValType.WellFormed {Ref : Type u} {Resource : Type v}
    (refOk : Ref → Prop) (resourceOk : Resource → Prop) : ValType Ref Resource → Prop where
  | prim (p : Primitive) : WellFormed refOk resourceOk (.prim p)
  | ref {r : Ref} (valid : refOk r) : WellFormed refOk resourceOk (.ref r)
  | list {t : ValType Ref Resource} (element : WellFormed refOk resourceOk t) :
      WellFormed refOk resourceOk (.list t)
  | fixedList {t : ValType Ref Resource} {n : Nat} (positive : 0 < n)
      (element : WellFormed refOk resourceOk t) : WellFormed refOk resourceOk (.fixedList t n)
  | record {fields : List (String × ValType Ref Resource)} (nonempty : fields ≠ [])
      (unique : (fields.map (fun f => f.1.toLower)).Nodup)
      (members : ∀ f ∈ fields, WellFormed refOk resourceOk f.2) :
      WellFormed refOk resourceOk (.record fields)
  | tuple {fields : List (ValType Ref Resource)} (nonempty : fields ≠ [])
      (members : ∀ t ∈ fields, WellFormed refOk resourceOk t) :
      WellFormed refOk resourceOk (.tuple fields)
  | variant {cases : List (String × Option (ValType Ref Resource))}
      (nonempty : cases ≠ []) (bounded : cases.length < 2 ^ 32)
      (unique : (cases.map (fun c => c.1.toLower)).Nodup)
      (members : ∀ c ∈ cases, ∀ t ∈ c.2, WellFormed refOk resourceOk t) :
      WellFormed refOk resourceOk (.variant cases)
  | enum {cases : List String} (nonempty : cases ≠ []) (bounded : cases.length < 2 ^ 32)
      (unique : (cases.map String.toLower).Nodup) : WellFormed refOk resourceOk (.enum cases)
  | flags {labels : List String} (nonempty : labels ≠ []) (bounded : labels.length ≤ 32)
      (unique : (labels.map String.toLower).Nodup) : WellFormed refOk resourceOk (.flags labels)
  | option {t : ValType Ref Resource} (element : WellFormed refOk resourceOk t) :
      WellFormed refOk resourceOk (.option t)
  | result {ok error : Option (ValType Ref Resource)}
      (okType : ∀ t ∈ ok, WellFormed refOk resourceOk t)
      (errorType : ∀ t ∈ error, WellFormed refOk resourceOk t) :
      WellFormed refOk resourceOk (.result ok error)
  | map {k : KeyType} {v : ValType Ref Resource} (value : WellFormed refOk resourceOk v) :
      WellFormed refOk resourceOk (.map k v)
  | own {r : Resource} (valid : resourceOk r) : WellFormed refOk resourceOk (.own r)
  | borrow {r : Resource} (valid : resourceOk r) : WellFormed refOk resourceOk (.borrow r)
  | future {t : Option (ValType Ref Resource)} (element : ∀ a ∈ t, WellFormed refOk resourceOk a) :
      WellFormed refOk resourceOk (.future t)
  | stream {t : Option (ValType Ref Resource)} (element : ∀ a ∈ t, WellFormed refOk resourceOk a) :
      WellFormed refOk resourceOk (.stream t)
  | errorContext : WellFormed refOk resourceOk .errorContext

end Silmaril.Wasm.Component.WIT
