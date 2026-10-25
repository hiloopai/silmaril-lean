module

public import Silmaril.Wasm.Types

@[expose] public section

/-! # Semantic (defined, rolled, closed) types of WebAssembly 3.0

This file is the type-level foundation of the Core 3.0 validator and runtime. It
transcribes the *semantic* type grammar of spec §1.2 (`1.2-syntax.types.spectec`):
type uses with `_IDX`, `REC i` and `_DEF rectype i`, the heap-type `BOT`, the
value-type `BOT`, substitution (`$subst_*`), complete substitution
(`$subst_all_*`), rolling and unrolling (`$rollrt`, `$unrollrt`, `$rolldt`,
`$unrolldt`), expansion (`Expand`, §2.1), free type indices (`$free_*`) and
closure (`$clos_*`, §2.0).

## Representation (design B, proof-engineering first)

The spec's ten mutually recursive semantic sorts (typeuse, heaptype, reftype,
valtype, storagetype, fieldtype, comptype, subtype, rectype, deftype) are one
**kind-indexed, non-nested** inductive family `Ty : TKind → Type`. Sequences are
not Lean `List`s inside the family but a list kind `TKind.list k` with its own
`nil`/`cons` constructors. Consequences:

* `deriving DecidableEq` works (the kernel reduces it, so `decide` works on
  concrete closed types);
* every operation (`subst`, `freeIdx`, …) is *one* structurally recursive
  function over all sorts, and every property is proved by *one* `induction`;
* the `induction` tactic applies directly (no nested-inductive recursors).

Each spec sort is an `abbrev` (`CValType := Ty .val`, `DefType := Ty .def`, …),
and each spec production is exactly one constructor. The list kinds are
isomorphic to `List` via `Ty.ofList`/`Ty.toList` (`toList_ofList`,
`ofList_toList`).

Spec subsorting is explicit: a `deftype` used as a `typeuse` is `Ty.dt`, a
`typeuse` used as a `heaptype` is `Ty.use`, a `reftype` used as a `valtype` is
`Ty.refv`, and a `valtype` used as a `storagetype` is `Ty.val`.
-/

namespace Silmaril.Wasm.Validation

/-- The spec's semantic type sorts, plus sequences of a sort. -/
inductive TKind where
  | use | heap | ref | val | storage | field | comp | sub | group | def
  | list (k : TKind)
  deriving DecidableEq, Repr

/-- All semantic types of §1.2, indexed by their sort. -/
inductive Ty : TKind → Type where
  /-- The empty sequence of a sort. -/
  | nil {k : TKind} : Ty (.list k)
  /-- A non-empty sequence of a sort. -/
  | cons {k : TKind} (hd : Ty k) (tl : Ty (.list k)) : Ty (.list k)
  /-- `_IDX typeidx`: a free type index (only in open types). -/
  | idx (x : Nat) : Ty .use
  /-- `REC i`: a reference to the `i`th member of the enclosing recursive group. -/
  | recv (i : Nat) : Ty .use
  /-- A defined type used as a type use. -/
  | dt (d : Ty .def) : Ty .use
  /-- `_DEF rectype i`: projection of a (rolled) recursive group. -/
  | defn (g : Ty .group) (i : Nat) : Ty .def
  /-- An abstract heap type. -/
  | abs (a : AbsHeapType) : Ty .heap
  /-- The semantic bottom heap type `BOT`. -/
  | bot : Ty .heap
  /-- A type use as a heap type. -/
  | use (u : Ty .use) : Ty .heap
  /-- `REF NULL? heaptype`. -/
  | ref (nullable : Bool) (h : Ty .heap) : Ty .ref
  | num (t : NumType) : Ty .val
  | vec (t : VecType) : Ty .val
  /-- A reference type as a value type. -/
  | refv (r : Ty .ref) : Ty .val
  /-- The semantic bottom value type `BOT`. -/
  | botv : Ty .val
  /-- A value type as a storage type. -/
  | val (t : Ty .val) : Ty .storage
  | pack (p : PackType) : Ty .storage
  /-- `mut? storagetype`. -/
  | field (m : Mutability) (s : Ty .storage) : Ty .field
  | struct (fields : Ty (.list .field)) : Ty .comp
  | array (field : Ty .field) : Ty .comp
  | func (params results : Ty (.list .val)) : Ty .comp
  /-- `SUB final? typeuse* comptype`. -/
  | sub (final : Bool) (supers : Ty (.list .use)) (body : Ty .comp) : Ty .sub
  /-- `REC subtype*`. -/
  | group (subs : Ty (.list .sub)) : Ty .group
  deriving DecidableEq, Repr

abbrev CTypeUse := Ty .use
abbrev CHeapType := Ty .heap
abbrev CRefType := Ty .ref
abbrev CValType := Ty .val
abbrev CStorageType := Ty .storage
abbrev CFieldType := Ty .field
abbrev CCompType := Ty .comp
abbrev CSubType := Ty .sub
abbrev CRecType := Ty .group
abbrev DefType := Ty .def

instance {k : TKind} : Inhabited (Ty (.list k)) := ⟨.nil⟩
instance : Inhabited CHeapType := ⟨.bot⟩
instance : Inhabited CValType := ⟨.botv⟩
instance : Inhabited CRecType := ⟨.group .nil⟩
instance : Inhabited DefType := ⟨.defn default 0⟩

/-! ## Sequences -/

namespace Ty

def ofList {k : TKind} : List (Ty k) → Ty (.list k)
  | [] => .nil
  | a :: l => .cons a (ofList l)

/-- The element sort of a sequence sort (identity elsewhere; used only to make
`toList` structurally recursive over an arbitrary index). -/
def _root_.Silmaril.Wasm.Validation.TKind.elem : TKind → TKind
  | .list k => k
  | k => k

/-- Elements of a sequence (empty for non-sequence sorts). -/
def elems : {j : TKind} → Ty j → List (Ty j.elem)
  | _, .cons a l => a :: elems l
  | _, _ => []

def toList {k : TKind} (t : Ty (.list k)) : List (Ty k) := elems t

@[simp] theorem toList_nil {k : TKind} : (Ty.nil : Ty (.list k)).toList = [] := rfl
@[simp] theorem toList_cons {k : TKind} (a : Ty k) (l : Ty (.list k)) :
    (Ty.cons a l).toList = a :: l.toList := rfl
@[simp] theorem ofList_nil {k : TKind} : ofList ([] : List (Ty k)) = .nil := rfl
@[simp] theorem ofList_cons {k : TKind} (a : Ty k) (l : List (Ty k)) :
    ofList (a :: l) = .cons a (ofList l) := rfl

@[simp] theorem toList_ofList {k : TKind} : (l : List (Ty k)) → (ofList l).toList = l
  | [] => rfl
  | a :: l => by simp [toList_ofList l]

@[simp] theorem ofList_toList {k : TKind} : (t : Ty (.list k)) → ofList t.toList = t
  | .nil => rfl
  | .cons a l => by simp [ofList_toList l]

/-- Sequence concatenation (`t_1* t_2*`). -/
def app {k : TKind} (a b : Ty (.list k)) : Ty (.list k) := ofList (a.toList ++ b.toList)

def length {k : TKind} (l : Ty (.list k)) : Nat := l.toList.length

/-! ## Projections -/

def subs : CRecType → Ty (.list .sub)
  | .group s => s

/-- Finality of a sub type. -/
def isFinal : CSubType → Bool
  | .sub f _ _ => f

/-- Declared supertypes of a sub type. -/
def supers : CSubType → List CTypeUse
  | .sub _ s _ => s.toList

/-- The composite type of a sub type. -/
def body : CSubType → CCompType
  | .sub _ _ b => b

end Ty

/-! ## Handy constructors -/

namespace Ty

def i32 : CValType := .num (.int .i32)
def i64 : CValType := .num (.int .i64)
def f32 : CValType := .num (.float .f32)
def f64 : CValType := .num (.float .f64)
def v128 : CValType := .vec .v128

/-- `REF NULL? ht` as a value type. -/
def refT (nullable : Bool) (h : CHeapType) : CValType := .refv (.ref nullable h)

/-- The heap type of a defined type. -/
def defHeap (d : DefType) : CHeapType := .use (.dt d)

def funcref : CRefType := .ref true (.abs .func)
def exnref : CRefType := .ref true (.abs .exn)
def externref : CRefType := .ref true (.abs .extern)

/-- A function composite type from two Lean lists. -/
def funcOf (params results : List CValType) : CCompType := .func (ofList params) (ofList results)

/-- `$unpack(storagetype)`. -/
def unpack : CStorageType → CValType
  | .val t => t
  | .pack _ => i32

/-- The `$is_packtype` test (`zt ≠ $unpack(zt)`). -/
def isPacked : CStorageType → Bool
  | .val _ => false
  | .pack _ => true

/-- Numeric or vector (the premise `t = numtype ∨ t = vectype`). -/
def IsNumOrVec : CValType → Prop
  | .num _ | .vec _ => True
  | _ => False

instance (t : CValType) : Decidable (IsNumOrVec t) := by
  cases t <;> unfold IsNumOrVec <;> infer_instance

end Ty

/-! ## Substitution (`$subst_*`) -/

/-- Type variables (`typevar`): `_IDX x` or `REC i`. -/
inductive TVar where
  | idx (x : Nat)
  | recv (i : Nat)
  deriving DecidableEq, Repr

/-- A substitution maps variables to type uses; `none` leaves the variable in place.
This is the function form of the spec's pair of sequences `tv*, tu*`
(see `Subst.ofLists`). -/
abbrev Subst := TVar → Option CTypeUse

/-- `$minus_recs`: `REC` variables are bound by an enclosing `rectype`. -/
def Subst.minusRecs (σ : Subst) : Subst
  | .recv _ => none
  | v => σ v

/-- The spec's list form `tv*, tu*` (first match wins, as in `$subst_typevar`). -/
def Subst.ofLists : List TVar → List CTypeUse → Subst
  | tv :: tvs, tu :: tus => fun v => if v = tv then some tu else Subst.ofLists tvs tus v
  | _, _ => fun _ => none

/-- Simultaneous substitution on every sort (`$subst_*`). Recursive groups bind
their `REC` variables, so the substitution under `group` is `σ.minusRecs`,
exactly as in `$subst_rectype`. -/
def Ty.subst (σ : Subst) : {k : TKind} → Ty k → Ty k
  | _, .nil => .nil
  | _, .cons a l => .cons (a.subst σ) (l.subst σ)
  | _, .idx x => (σ (.idx x)).getD (.idx x)
  | _, .recv i => (σ (.recv i)).getD (.recv i)
  | _, .dt d => .dt (d.subst σ)
  | _, .defn g i => .defn (g.subst σ) i
  | _, .abs a => .abs a
  | _, .bot => .bot
  | _, .use u => .use (u.subst σ)
  | _, .ref n h => .ref n (h.subst σ)
  | _, .num t => .num t
  | _, .vec t => .vec t
  | _, .refv r => .refv (r.subst σ)
  | _, .botv => .botv
  | _, .val t => .val (t.subst σ)
  | _, .pack p => .pack p
  | _, .field m s => .field m (s.subst σ)
  | _, .struct fs => .struct (fs.subst σ)
  | _, .array f => .array (f.subst σ)
  | _, .func ps rs => .func (ps.subst σ) (rs.subst σ)
  | _, .sub fin sups b => .sub fin (sups.subst σ) (b.subst σ)
  | _, .group subs => .group (subs.subst σ.minusRecs)

/-- The substitution of `$subst_all_*`: `(_IDX i)^(i<n) := tu^n`. -/
def Subst.all (tus : List CTypeUse) : Subst
  | .idx i => tus[i]?
  | .recv _ => none

/-- `$subst_all_*`. -/
def Ty.substAll {k : TKind} (t : Ty k) (tus : List CTypeUse) : Ty k := t.subst (Subst.all tus)

/-! ## Rolling and unrolling -/

/-- `$rollrt(x, rectype)`: replace `_IDX (x+i)` by `REC i` for the group's members. -/
def rollrt (x : Nat) : CRecType → CRecType
  | .group subs =>
    let n := subs.length
    .group (subs.subst fun
      | .idx y => if x ≤ y ∧ y < x + n then some (.recv (y - x)) else none
      | .recv _ => none)

/-- `$unrollrt(rectype)`: replace `REC i` by `_DEF rectype i`. -/
def unrollrt (rt : CRecType) : CRecType :=
  match rt with
  | .group subs =>
    let n := subs.length
    .group (subs.subst fun
      | .recv i => if i < n then some (.dt (.defn rt i)) else none
      | .idx _ => none)

/-- `$rolldt(x, rectype)`: the defined types of a recursive group at index `x`. -/
def rolldt (x : Nat) (rt : CRecType) : List DefType :=
  let rt' := rollrt x rt
  (List.range rt'.subs.length).map (Ty.defn rt')

/-- `$unrolldt(_DEF rectype i) = subtype*[i]` (partial, hence `Option`). -/
def unrolldt : DefType → Option CSubType
  | .defn rt i => (unrollrt rt).subs.toList[i]?

/-- The expansion of a defined type to its composite type. -/
def DefType.expand? (d : DefType) : Option CCompType := (unrolldt d).map Ty.body

/-- `Expand: deftype ~~ comptype` (§2.1). -/
inductive Expand : DefType → CCompType → Prop where
  | mk {d : DefType} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
      (h : unrolldt d = some (.sub fin sups ct)) : Expand d ct

theorem Expand.iff {d : DefType} {ct : CCompType} : Expand d ct ↔ d.expand? = some ct := by
  constructor
  · rintro ⟨h⟩
    simp [DefType.expand?, h, Ty.body]
  · intro h
    unfold DefType.expand? at h
    cases hu : unrolldt d with
    | none => simp [hu] at h
    | some st =>
      rw [hu] at h
      cases st with
      | sub fin sups b =>
        simp only [Option.map_some, Option.some.injEq, Ty.body] at h
        exact .mk (h ▸ hu)

instance (d : DefType) (ct : CCompType) : Decidable (Expand d ct) :=
  decidable_of_iff _ Expand.iff.symm

/-- The function type a defined type expands to, as Lean lists. -/
def DefType.funcType? (d : DefType) : Option (List CValType × List CValType) :=
  match d.expand? with
  | some (.func ps rs) => some (ps.toList, rs.toList)
  | _ => none

/-! ## Free type indices and closure -/

/-- The type indices free in a type (`$free_*`, restricted to `typeidx`). -/
def Ty.freeIdx : {k : TKind} → Ty k → List Nat
  | _, .nil => []
  | _, .cons a l => a.freeIdx ++ l.freeIdx
  | _, .idx x => [x]
  | _, .recv _ => []
  | _, .dt d => d.freeIdx
  | _, .defn g _ => g.freeIdx
  | _, .abs _ => []
  | _, .bot => []
  | _, .use u => u.freeIdx
  | _, .ref _ h => h.freeIdx
  | _, .num _ => []
  | _, .vec _ => []
  | _, .refv r => r.freeIdx
  | _, .botv => []
  | _, .val t => t.freeIdx
  | _, .pack _ => []
  | _, .field _ s => s.freeIdx
  | _, .struct fs => fs.freeIdx
  | _, .array f => f.freeIdx
  | _, .func ps rs => ps.freeIdx ++ rs.freeIdx
  | _, .sub _ sups b => sups.freeIdx ++ b.freeIdx
  | _, .group subs => subs.freeIdx

/-- A type is *closed* when it mentions no `_IDX` (it may mention `REC`). -/
def Ty.Closed {k : TKind} (t : Ty k) : Prop := t.freeIdx = []

instance {k : TKind} (t : Ty k) : Decidable t.Closed := inferInstanceAs (Decidable (_ = _))

/-- `$clos_deftypes`: close a context's type sequence from left to right. -/
def closDefTypes (dts : List DefType) : List DefType :=
  dts.foldl (fun acc d => acc ++ [d.substAll (acc.map .dt)]) []

/-- `$clos_*(C, t)` for a context whose `TYPES` are `types`. -/
def Ty.clos {k : TKind} (types : List DefType) (t : Ty k) : Ty k :=
  t.substAll ((closDefTypes types).map .dt)

/-! ## Lifting source syntax into semantic types

Source syntax (`Silmaril.Wasm.ValType`, …) refers to types by index only; its
image in `Ty` uses `_IDX`. Validation immediately closes it (`Context.close*`). -/

def liftTypeIdx (x : TypeIdx) : CTypeUse := .idx x.toNat

def liftHeap : HeapType → CHeapType
  | .abstract a => .abs a
  | .typeIdx x => .use (liftTypeIdx x)

def liftRef (r : RefType) : CRefType := .ref r.nullable (liftHeap r.heap)

def liftVal : ValType → CValType
  | .num t => .num t
  | .vec t => .vec t
  | .ref r => .refv (liftRef r)

def liftResult (ts : ResultType) : Ty (.list .val) := Ty.ofList (ts.map liftVal)

def liftStorage : StorageType → CStorageType
  | .val t => .val (liftVal t)
  | .packed p => .pack p

def liftField (f : FieldType) : CFieldType := .field f.mutability (liftStorage f.storage)

def liftComp : CompositeType → CCompType
  | .func ft => .func (liftResult ft.params) (liftResult ft.results)
  | .struct fs => .struct (Ty.ofList (fs.map liftField))
  | .array f => .array (liftField f)

def liftSub (st : SubType) : CSubType :=
  .sub st.final_ (Ty.ofList (st.supertypes.map liftTypeIdx)) (liftComp st.body)

def liftRec (rt : RecType) : CRecType := .group (Ty.ofList (rt.types.map liftSub))

/-! ## Closed external types -/

/-- `globaltype = mut? valtype` over semantic value types. -/
structure CGlobalType where
  mutability : Mutability
  type : CValType
  deriving DecidableEq, Repr

/-- `tabletype = addrtype limits reftype` over semantic reference types. -/
structure CTableType where
  address : AddrType
  limits : Limits
  element : CRefType
  deriving DecidableEq, Repr

/-- `externtype` with closed tag and function types (`$clos_externtype`). Memory
types contain no type uses, so the source `MemoryType` is reused. -/
inductive CExternType where
  | tag (type : DefType)
  | global (type : CGlobalType)
  | mem (type : MemoryType)
  | table (type : CTableType)
  | func (type : DefType)
  deriving DecidableEq, Repr

/-- `$funcsxt` and friends. -/
def CExternType.funcs : List CExternType → List DefType
  | [] => []
  | .func d :: xs => d :: funcs xs
  | _ :: xs => funcs xs

def CExternType.tags : List CExternType → List DefType
  | [] => []
  | .tag d :: xs => d :: tags xs
  | _ :: xs => tags xs

def CExternType.globals : List CExternType → List CGlobalType
  | [] => []
  | .global g :: xs => g :: globals xs
  | _ :: xs => globals xs

def CExternType.mems : List CExternType → List MemoryType
  | [] => []
  | .mem m :: xs => m :: mems xs
  | _ :: xs => mems xs

def CExternType.tables : List CExternType → List CTableType
  | [] => []
  | .table t :: xs => t :: tables xs
  | _ :: xs => tables xs

/-- `moduletype = externtype* -> externtype*`. -/
structure CModuleType where
  imports : List CExternType
  exports : List CExternType
  deriving DecidableEq, Repr

/-! ## Milestone statements about the type algebra -/

/-- Substituting the identity is the identity. -/
theorem Ty.subst_of_none {k : TKind} (t : Ty k) :
    ∀ σ : Subst, (∀ v, σ v = none) → t.subst σ = t := by
  induction t with
  | group subs ih =>
    intro σ hσ
    simp only [Ty.subst]
    rw [ih]
    intro v
    cases v <;> simp [Subst.minusRecs, hσ]
  | idx x => intro σ hσ; simp [Ty.subst, hσ]
  | recv i => intro σ hσ; simp [Ty.subst, hσ]
  | _ => intro σ hσ; simp_all [Ty.subst]

theorem Ty.subst_none {k : TKind} (t : Ty k) : t.subst (fun _ => none) = t :=
  t.subst_of_none _ fun _ => rfl

/-- A substitution that leaves `REC` variables alone does not change a closed type. -/
theorem Ty.subst_closed {k : TKind} (t : Ty k) :
    ∀ σ : Subst, (∀ i, σ (.recv i) = none) → t.freeIdx = [] → t.subst σ = t := by
  induction t with
  | idx x => intro σ _ h; simp [Ty.freeIdx] at h
  | recv i => intro σ hσ _; simp [Ty.subst, hσ]
  | group subs ih =>
    intro σ hσ h
    simp only [Ty.subst]
    rw [ih _ (fun i => by simp [Subst.minusRecs]) (by simpa [Ty.freeIdx] using h)]
  | cons a l iha ihl =>
    intro σ hσ h
    simp only [Ty.freeIdx, List.append_eq_nil_iff] at h
    simp only [Ty.subst, iha σ hσ h.1, ihl σ hσ h.2]
  | func ps rs ihp ihr =>
    intro σ hσ h
    simp only [Ty.freeIdx, List.append_eq_nil_iff] at h
    simp only [Ty.subst, ihp σ hσ h.1, ihr σ hσ h.2]
  | sub fin sups b ihs ihb =>
    intro σ hσ h
    simp only [Ty.freeIdx, List.append_eq_nil_iff] at h
    simp only [Ty.subst, ihs σ hσ h.1, ihb σ hσ h.2]
  | _ => intro σ hσ h; simp_all [Ty.subst, Ty.freeIdx]

theorem Ty.toList_subst {k : TKind} (σ : Subst) :
    ∀ l : Ty (.list k), (l.subst σ).toList = l.toList.map (·.subst σ)
  | .nil => rfl
  | .cons a l => by simp [Ty.subst, Ty.toList_subst σ l]

theorem Ty.length_subst {k : TKind} (σ : Subst) (l : Ty (.list k)) :
    (l.subst σ).length = l.length := by
  simp [Ty.length, Ty.toList_subst]

/-- Complete substitution does not touch a closed type. -/
theorem Ty.substAll_closed {k : TKind} {t : Ty k} (h : t.Closed) (tus : List CTypeUse) :
    t.substAll tus = t :=
  t.subst_closed _ (fun _ => rfl) h

/-- The spec's snoc equation for `$clos_deftypes`. -/
theorem closDefTypes_snoc (dts : List DefType) (d : DefType) :
    closDefTypes (dts ++ [d]) =
      closDefTypes dts ++ [d.substAll ((closDefTypes dts).map .dt)] := by
  simp [closDefTypes, List.foldl_append]

/-- Closing an already-closed context is the identity: validation stores closed
types in its contexts (see `Context`), so `$clos_*` is `substAll`. -/
theorem closDefTypes_closed {dts : List DefType} (h : ∀ d ∈ dts, d.Closed) :
    closDefTypes dts = dts := by
  unfold closDefTypes
  suffices H : ∀ acc : List DefType,
      dts.foldl (fun acc d => acc ++ [d.substAll (acc.map .dt)]) acc = acc ++ dts by
    simpa using H []
  induction dts with
  | nil => intro acc; simp
  | cons d ds ih =>
    intro acc
    simp only [List.foldl]
    rw [Ty.substAll_closed (h d (by simp)), ih (fun x hx => h x (by simp [hx]))]
    simp

/-- Every defined type produced by rolling a group unrolls (the spec's `$unrolldt`
is total on the image of `$rolldt`). -/
theorem unrolldt_rolldt_isSome (x : Nat) (rt : CRecType) :
    ∀ d ∈ rolldt x rt, (unrolldt d).isSome = true := by
  intro d hd
  simp only [rolldt, List.mem_map, List.mem_range] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  generalize rollrt x rt = g at hi
  cases g with
  | group s =>
    simp only [Ty.subs] at hi
    simp only [unrolldt, unrollrt, Ty.subs, Ty.toList_subst, List.getElem?_map,
      Ty.length] at hi ⊢
    simp [List.getElem?_eq_getElem hi]

/-! ### Free indices under substitution -/

/-- The possible origins of a free index `y` of `t.subst σ`, given the free indices `L` of `t`. -/
def SubstOrigin (σ : Subst) (L : List Nat) (y : Nat) : Prop :=
  (y ∈ L ∧ σ (.idx y) = none) ∨ ∃ x ∈ L, ∃ u, σ (.idx x) = some u ∧ y ∈ u.freeIdx

theorem SubstOrigin.mono {σ : Subst} {L L' : List Nat} {y : Nat} (h : SubstOrigin σ L y)
    (hL : L ⊆ L') : SubstOrigin σ L' y := by
  rcases h with ⟨h1, h2⟩ | ⟨x, hx, u, hu, hy⟩
  · exact .inl ⟨hL h1, h2⟩
  · exact .inr ⟨x, hL hx, u, hu, hy⟩

theorem SubstOrigin.minusRecs {σ : Subst} {L : List Nat} {y : Nat}
    (h : SubstOrigin σ.minusRecs L y) : SubstOrigin σ L y := h

/-- Every free index of `t.subst σ` is a free index of `t` left alone by `σ`, or a free
index of the image of a free index of `t`. -/
theorem Ty.freeIdx_subst {k : TKind} (t : Ty k) :
    ∀ σ : Subst, (∀ i, σ (.recv i) = none) → ∀ y ∈ (t.subst σ).freeIdx,
      SubstOrigin σ t.freeIdx y := by
  induction t with
  | idx x =>
    intro σ _ y hy
    simp only [Ty.subst] at hy
    cases h : σ (.idx x) with
    | none => simp [h, Ty.freeIdx] at hy; subst hy; exact .inl ⟨by simp [Ty.freeIdx], h⟩
    | some u => simp [h] at hy; exact .inr ⟨x, by simp [Ty.freeIdx], u, h, hy⟩
  | recv i => intro σ hσ y hy; simp [Ty.subst, hσ, Ty.freeIdx] at hy
  | group subs ih =>
    intro σ _ y hy
    exact (ih σ.minusRecs (fun _ => rfl) y hy : SubstOrigin σ.minusRecs _ y)
  | cons a l iha ihl =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy
    rcases hy with hy | hy
    · exact (iha σ hσ y hy).mono (by simp [Ty.freeIdx])
    · exact (ihl σ hσ y hy).mono (by simp [Ty.freeIdx])
  | func ps rs ihp ihr =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy
    rcases hy with hy | hy
    · exact (ihp σ hσ y hy).mono (by simp [Ty.freeIdx])
    · exact (ihr σ hσ y hy).mono (by simp [Ty.freeIdx])
  | sub fin sups b ihs ihb =>
    intro σ hσ y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy
    rcases hy with hy | hy
    · exact (ihs σ hσ y hy).mono (by simp [Ty.freeIdx])
    · exact (ihb σ hσ y hy).mono (by simp [Ty.freeIdx])
  | dt d ih => intro σ hσ y hy; exact ih σ hσ y hy
  | defn g i ih => intro σ hσ y hy; exact ih σ hσ y hy
  | use u ih => intro σ hσ y hy; exact ih σ hσ y hy
  | ref n h ih => intro σ hσ y hy; exact ih σ hσ y hy
  | refv r ih => intro σ hσ y hy; exact ih σ hσ y hy
  | val t ih => intro σ hσ y hy; exact ih σ hσ y hy
  | field m s ih => intro σ hσ y hy; exact ih σ hσ y hy
  | struct fs ih => intro σ hσ y hy; exact ih σ hσ y hy
  | array f ih => intro σ hσ y hy; exact ih σ hσ y hy
  | _ => intro σ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy

/-- A free index left alone by `σ` stays free. -/
theorem Ty.freeIdx_subst_of_none {k : TKind} (t : Ty k) :
    ∀ σ : Subst, ∀ y ∈ t.freeIdx, σ (.idx y) = none → y ∈ (t.subst σ).freeIdx := by
  induction t with
  | idx x =>
    intro σ y hy h
    simp only [Ty.freeIdx, List.mem_singleton] at hy
    subst hy
    simp [Ty.subst, h, Ty.freeIdx]
  | group subs ih => intro σ y hy h; exact ih σ.minusRecs y hy h
  | cons a l iha ihl =>
    intro σ y hy h; simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    exact hy.imp (iha σ y · h) (ihl σ y · h)
  | func a l iha ihl =>
    intro σ y hy h; simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    exact hy.imp (iha σ y · h) (ihl σ y · h)
  | sub _ a l iha ihl =>
    intro σ y hy h; simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    exact hy.imp (iha σ y · h) (ihl σ y · h)
  | _ => intro σ y hy h; simp_all [Ty.subst, Ty.freeIdx]

theorem Ty.mem_freeIdx_ofList {k : TKind} {y : Nat} :
    ∀ l : List (Ty k), y ∈ (Ty.ofList l).freeIdx ↔ ∃ a ∈ l, y ∈ a.freeIdx
  | [] => by simp [Ty.freeIdx]
  | a :: l => by simp [Ty.freeIdx, Ty.mem_freeIdx_ofList l]

theorem Ty.length_ofList {k : TKind} (l : List (Ty k)) : (Ty.ofList l).length = l.length := by
  simp [Ty.length]

end Silmaril.Wasm.Validation
