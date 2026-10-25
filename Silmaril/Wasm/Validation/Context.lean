module

public import Silmaril.Wasm.Validation.Subtyping
public import Silmaril.Wasm.Validation.Types
public import Silmaril.Wasm.Instructions

@[expose] public section

/-! # Validation contexts and instruction types (§2.0)

`Context` transcribes `context` of `2.0-validation.contexts.spectec` field for
field (`RECS` is inherited from `TypeCtx`).

**Closed contexts (design B).** In the spec, `C.TYPES` holds *open* defined types
(they may mention `_IDX` of earlier types) and every use goes through
`$clos_*`. Here every type stored in a `Context` — and every type in an
`InstrType` — is already *closed*: module validation closes each recursive group
as it is added (`Validation/Modules.lean`), and source immediates are closed with
`Context.closeVal` & co. at the typing rule. Since `$clos_deftypes` is the
identity on a closed sequence (`closDefTypes_closed`), `C.close t` coincides with
the spec's `$clos_valtype(C, t)` for the corresponding open context; the
correspondence is stated in `Validation/Instructions/Properties.lean`.

Indices in semantic positions (local indices in instruction types, `REFS`) are
`Nat`; source immediates are `Idx` and are converted with `Idx.toNat`.
-/

namespace Silmaril.Wasm.Validation

/-- `init = SET | UNSET`. -/
inductive Init where
  | set | unset
  deriving DecidableEq, Repr

/-- `localtype = init valtype`. -/
structure LocalType where
  init : Init
  type : CValType
  deriving DecidableEq, Repr

/-- `instrtype = resulttype ->_(localidx*) resulttype`. Stacks are bottom-first. -/
structure InstrType where
  params : List CValType
  inits : List Nat := []
  results : List CValType
  deriving DecidableEq, Repr

/-- `t_1* -> t_2*` with no initialized locals. -/
abbrev InstrType.plain (params results : List CValType) : InstrType := ⟨params, [], results⟩

/-- The validation context `C`. `TYPES` and `RECS` come from `TypeCtx`; all types
are closed (see the module doc). -/
structure Context extends TypeCtx where
  tags : List DefType := []
  globals : List CGlobalType := []
  mems : List MemoryType := []
  tables : List CTableType := []
  funcs : List DefType := []
  /-- `DATAS datatype*`; `datatype = OK`. -/
  datas : List Unit := []
  elems : List CRefType := []
  locals : List LocalType := []
  /-- Innermost label first, as in the spec's `{LABELS (t*)} ++ C`. -/
  labels : List (List CValType) := []
  return_ : Option (List CValType) := none
  /-- `REFS funcidx*`: functions that may be referenced by `ref.func`. -/
  refs : List Nat := []
  deriving Repr

namespace Context

/-- `{LABELS (t*)} ++ C`. -/
def withLabel (C : Context) (ts : List CValType) : Context :=
  { C with labels := ts :: C.labels }

/-- `C[.LOCALS[x] = lt]`. -/
def setLocal (C : Context) (x : Nat) (lt : LocalType) : Context :=
  { C with locals := C.locals.set x lt }

/-- `$with_locals(C, x*, lt*)`. -/
def withLocals : Context → List Nat → List LocalType → Context
  | C, x :: xs, lt :: lts => withLocals (C.setLocal x lt) xs lts
  | C, _, _ => C

/-- `$with_locals(C, x*, (SET t)*)` where each `t` is the current type of local `x`
(the context update of `Instrs_ok/seq`). -/
def initLocals (C : Context) (xs : List Nat) : Context :=
  C.withLocals xs (xs.map fun x => ⟨.set, ((C.locals[x]?).map LocalType.type).getD default⟩)

/-- Close a source type use against this (closed) context. -/
def closeUse (C : Context) (u : CTypeUse) : CTypeUse := u.substAll (C.types.map .dt)

def closeHeap (C : Context) (h : HeapType) : CHeapType := (liftHeap h).substAll (C.types.map .dt)
def closeRef (C : Context) (r : RefType) : CRefType := (liftRef r).substAll (C.types.map .dt)
def closeVal (C : Context) (t : ValType) : CValType := (liftVal t).substAll (C.types.map .dt)
def closeResult (C : Context) (ts : ResultType) : List CValType := ts.map C.closeVal

/-- `REF NULL (_IDX x)` closed: the nullable reference to `C.TYPES[x]`. -/
def refToIdx (C : Context) (nullable : Bool) (x : TypeIdx) : CValType :=
  .refT nullable (.use (C.closeUse (liftTypeIdx x)))

/-- The type definition at a source index. -/
def type? (C : Context) (x : TypeIdx) : Option DefType := C.types[x.toNat]?

end Context

/-- `Instrtype_ok`. -/
def InstrTypeOk (C : Context) (it : InstrType) : Prop :=
  ResultOk C.toTypeCtx it.params ∧ ResultOk C.toTypeCtx it.results ∧
    ∀ x ∈ it.inits, ∃ lt, C.locals[x]? = some lt

/-- `Instrtype_sub`: contravariant parameters, covariant results, and the locals
initialized by the supertype but not the subtype must already be set. -/
def InstrTypeSub (C : Context) (it it' : InstrType) : Prop :=
  ResultSub C.toTypeCtx it'.params it.params ∧ ResultSub C.toTypeCtx it.results it'.results ∧
    ∀ x ∈ it'.inits, x ∉ it.inits → ∃ t, C.locals[x]? = some ⟨.set, t⟩

/-- `Memarg_ok: ⊢ {ALIGN n, OFFSET m} : at -> N`. -/
def MemArgOk (arg : MemArg) (at_ : AddrType) (N : Nat) : Prop :=
  2 ^ arg.align.val ≤ N / 8 ∧ arg.offset.val < 2 ^ at_.width

instance (arg : MemArg) (at_ : AddrType) (N : Nat) : Decidable (MemArgOk arg at_ N) := by
  unfold MemArgOk; infer_instance

/-- `$minat(at_1, at_2)`. -/
def _root_.Silmaril.Wasm.AddrType.min (a b : AddrType) : AddrType := if a.width ≤ b.width then a else b

/-- The value type of an address type. -/
def _root_.Silmaril.Wasm.AddrType.valType (a : AddrType) : CValType := .num (.int a.intType)

/-- `Defaultable` (§2.3/§4.1): `$default_(t) ≠ eps`. -/
def Defaultable : CValType → Prop
  | .num _ | .vec _ => True
  | .refv (.ref n _) => n = true
  | .botv => False

instance (t : CValType) : Decidable (Defaultable t) := by
  unfold Defaultable
  split <;> infer_instance

end Silmaril.Wasm.Validation
