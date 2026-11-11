module

public import Silmaril.Games.Sig.Defs
public import Silmaril.Wasm.SingleThreaded.Thread
public import Silmaril.Wasm.Behaviour.Adapters.Core
import Silmaril.Wasm.Execution.Core.Soundness.RefTyping

/-!
# Effect signatures of scalar Core 3.0 function interfaces

The objects of the game semantics of Wasm modules: the `Silmaril.Games.Sig`
signatures of the import and export interfaces of a Core 3.0 module.

Only *store-independent* function interfaces are covered: parameters and
results are numbers (`i32`, `i64`, `f32`, `f64`), vectors (`v128`) or unboxed
scalar references `(ref null? i31)` (`ScalarType.i31`: an `i31` reference,
or `null` when nullable). Their typing does not depend on the store
(`ScalarType.hasVal_iff_valOk`, for `i31` through silmaril-lean's
`Sub.down_leaf`: only `i31`, the bottom heap types and `null` lie below `i31`).
No store-relative reference (`funcref`, `externref`, struct/array/exception
references), memory, table or global crosses an interface; see
`docs/projects/games.md`.

* `FnType` is a scalar function type `params → results`.
* `fnSig ft` has as operations the argument lists typed by `ft.params`
  (`Typed`) and as answers `Answer ft`: typed results, a trap, or an uncaught
  exception `throw a` carrying its raw exception address (store data shared
  with the environment, exactly as Core reports it).
* `ifaceSig ts` is the signature of an indexed family of functions: an
  operation is a function index `i` with a typed call of it. The import and
  export signatures of an instance are `ifaceSig` of its import and export
  types (`Silmaril.Wasm.Game.Strategy`).

An ill-typed call is not an operation, so a machine callout with ill-typed
arguments (impossible for well-formed instances) has no move.
-/

@[expose] public section

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- A scalar value type: a number type, `v128`, or `(ref null? i31)`. -/
inductive ScalarType where
  | num (t : NumType)
  | v128
  /-- `(ref i31)` (`nullable = false`) or `i31ref = (ref null i31)` (`nullable = true`). -/
  | i31 (nullable : Bool)
  deriving DecidableEq, Repr

namespace ScalarType

/-- The closed value type of a scalar type. -/
def toC : ScalarType → CValType
  | .num t => .num t
  | .v128 => .vec .v128
  | .i31 n => .refv (.ref n (.abs .i31))

/-- `HasVal t v`: the value `v` has the scalar type `t`. No store is needed: scalar values
do not mention addresses. -/
def HasVal : ScalarType → Val → Prop
  | .num t, v => ∃ bits, v = .num ⟨t, bits⟩
  | .v128, v => ∃ bits, v = .vec bits
  | .i31 n, v => (∃ b, v = .ref (.i31 b)) ∨ (n = true ∧ v = .ref .null)

/-- A reference whose principal type lies below `(ref null? i31)` (in any type context) is an
`i31` reference, or `null` when nullable. -/
theorem hasVal_i31_of_base {H : Type} {s : Store H} {Δ : TypeCtx} {r : Ref} {rt₀ : CRefType}
    {n : Bool} (hb : RefBase s r rt₀) (hs : Sub Δ rt₀ (.ref n (.abs .i31))) :
    (ScalarType.i31 n).HasVal (.ref r) := by
  cases hb with
  | null =>
    have hn : n = true := (Sub.ref_inv hs).2 rfl
    exact .inr ⟨hn, rfl⟩
  | i31 b => exact .inl ⟨b, rfl⟩
  | struct h =>
    exact absurd (Sub.down_leaf (Sub.ref_inv hs).1 (.inl rfl)) (by simp [HeapDown, Ty.defHeap])
  | array h =>
    exact absurd (Sub.down_leaf (Sub.ref_inv hs).1 (.inl rfl)) (by simp [HeapDown, Ty.defHeap])
  | func h =>
    exact absurd (Sub.down_leaf (Sub.ref_inv hs).1 (.inl rfl)) (by simp [HeapDown, Ty.defHeap])
  | exn h => exact absurd (Sub.down_leaf (Sub.ref_inv hs).1 (.inl rfl)) (by simp [HeapDown])
  | host a => exact absurd (Sub.down_leaf (Sub.ref_inv hs).1 (.inl rfl)) (by simp [HeapDown])
  | extern h hn => exact absurd (Sub.down_leaf (Sub.ref_inv hs).1 (.inl rfl)) (by simp [HeapDown])

/-- `(ref null? i31)` is a well-formed closed type. -/
theorem i31_tyOk (n : Bool) : TyOk {} (.ref n (.abs .i31) : CRefType) := .ref (.abs _)

/-- Every reference type is a subtype of itself. -/
theorem sub_ref_refl {Δ : TypeCtx} (n : Bool) (h : CHeapType) :
    Sub Δ (.ref n h : CRefType) (.ref n h) := by
  cases n with
  | false => exact .refNonNull .heapRefl
  | true => exact .refNull .heapRefl

/-- An `i31` reference, or `null`, has type `(ref null? i31)` when allowed, in any store. -/
theorem refOk_of_hasVal_i31 {H : Type} (s : Store H) {n : Bool} {r : Ref}
    (h : (ScalarType.i31 n).HasVal (.ref r)) : RefOk s r (.ref n (.abs .i31)) := by
  rcases h with ⟨b, hb⟩ | ⟨rfl, hb⟩
  · cases hb
    cases n with
    | false => exact .i31 b
    | true => exact .sub (.i31 b) (i31_tyOk true) (.refNull .heapRefl)
  · cases hb
    exact .sub .null (i31_tyOk true) (.refNull .bot)

/-- `(ref null? i31)` typing agrees with Core value typing, in any store. -/
theorem hasVal_i31_iff_valOk {H : Type} (s : Store H) (n : Bool) (v : Val) :
    (i31 n).HasVal v ↔ ValOk s v (.refv (.ref n (.abs .i31))) := by
  constructor
  · intro hv
    rcases hv with ⟨b, rfl⟩ | ⟨hn, rfl⟩
    · exact .ref (refOk_of_hasVal_i31 s (.inl ⟨b, rfl⟩))
    · exact .ref (refOk_of_hasVal_i31 s (.inr ⟨hn, rfl⟩))
  · intro hv
    obtain ⟨r, rt₀, rfl, hb, hs⟩ :=
      ValOk.ref_invRT (Δ := {}) hv (.refv (sub_ref_refl n (.abs .i31)))
    exact hasVal_i31_of_base hb hs

/-- Number typing agrees with Core value typing, in any store. -/
theorem hasVal_num_iff_valOk {H : Type} (s : Store H) (t : NumType) (v : Val) :
    (num t).HasVal v ↔ ValOk s v (.num t) := by
  constructor
  · rintro ⟨bits, rfl⟩
    exact ValOk.num ⟨t, bits⟩
  · intro h
    cases h with
    | num n => exact ⟨n.bits, rfl⟩

/-- Vector typing agrees with Core value typing, in any store. -/
theorem hasVal_v128_iff_valOk {H : Type} (s : Store H) (v : Val) :
    v128.HasVal v ↔ ValOk s v (.vec .v128) := by
  constructor
  · rintro ⟨bits, rfl⟩
    exact ValOk.vec bits
  · intro h
    cases h with
    | vec b => exact ⟨b, rfl⟩

/-- Scalar typing agrees with Core value typing, in any store. -/
theorem hasVal_iff_valOk {H : Type} (s : Store H) (t : ScalarType) (v : Val) :
    t.HasVal v ↔ ValOk s v t.toC := by
  cases t with
  | num t => exact hasVal_num_iff_valOk s t v
  | v128 => exact hasVal_v128_iff_valOk s v
  | i31 n => exact hasVal_i31_iff_valOk s n v

/-- The scalar type of a closed value type, if it is scalar. -/
def ofC? : CValType → Option ScalarType
  | .num t => some (.num t)
  | .vec .v128 => some .v128
  | .refv (.ref n (.abs .i31)) => some (.i31 n)
  | _ => none

theorem ofC?_toC (t : ScalarType) : ofC? t.toC = some t := by
  cases t <;> rfl

theorem toC_of_ofC? {c : CValType} {t : ScalarType} (h : ofC? c = some t) : t.toC = c := by
  unfold ofC? at h
  split at h <;> cases h <;> rfl

theorem map_toC_of_mapM {l : List CValType} {ts : List ScalarType}
    (h : l.mapM ofC? = some ts) : ts.map toC = l := by
  induction l generalizing ts with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | cons c l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨t, ht, ts', hts, rfl⟩ := h
    simp [toC_of_ofC? ht, ih hts]

end ScalarType

/-- Lists of values typed by a list of scalar types. -/
def Typed (ts : List ScalarType) : Type :=
  {vs : List Val // List.Forall₂ ScalarType.HasVal ts vs}

/-- A scalar function type. -/
structure FnType where
  params : List ScalarType
  results : List ScalarType
  deriving DecidableEq, Repr

/-- The composite type `func params results` of a scalar function type. -/
def FnType.toComp (ft : FnType) : CCompType :=
  .func (Ty.ofList (ft.params.map ScalarType.toC)) (Ty.ofList (ft.results.map ScalarType.toC))

/-- The scalar function type of a defined type, if it expands to a function type whose
parameters and results are all scalar. -/
def FnType.ofDefType? (d : DefType) : Option FnType := do
  let (ps, rs) ← d.funcType?
  let ps ← ps.mapM ScalarType.ofC?
  let rs ← rs.mapM ScalarType.ofC?
  pure ⟨ps, rs⟩

/-- A defined type whose `funcType?` is `(ps, rs)` expands to `func ps rs`. -/
private theorem expand_of_funcType? {d : DefType} {ps rs : List CValType}
    (hf : d.funcType? = some (ps, rs)) : Expand d (.func (Ty.ofList ps) (Ty.ofList rs)) := by
  rw [Expand.iff]
  unfold DefType.funcType? at hf
  split at hf
  next P R hex =>
    obtain ⟨hP, hR⟩ : P.toList = ps ∧ R.toList = rs := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hf
    rw [← hP, ← hR, Ty.ofList_toList, Ty.ofList_toList]
    exact hex
  next => cases hf

theorem FnType.expand_of_ofDefType? {d : DefType} {ft : FnType}
    (h : FnType.ofDefType? d = some ft) : Expand d ft.toComp := by
  obtain ⟨ps, rs, hf, ps', hps, rs', hrs, hft⟩ : ∃ ps rs, d.funcType? = some (ps, rs) ∧
      ∃ ps', ps.mapM ScalarType.ofC? = some ps' ∧
      ∃ rs', rs.mapM ScalarType.ofC? = some rs' ∧ (⟨ps', rs'⟩ : FnType) = ft := by
    simpa [FnType.ofDefType?, Option.bind_eq_some_iff, Prod.exists] using h
  have hcomp : ft.toComp = .func (Ty.ofList ps) (Ty.ofList rs) := by
    rw [← hft]
    simp only [FnType.toComp, ScalarType.map_toC_of_mapM hps, ScalarType.map_toC_of_mapM hrs]
  rw [hcomp]
  exact expand_of_funcType? hf

/-- The answer to a call of a function of type `ft` (the arity of `fnSig ft`):
typed results, a trap, or an uncaught exception with its exception address (see the module
docstring). -/
inductive Answer (ft : FnType) where
  | values (vs : Typed ft.results)
  | trap
  | throw (a : Nat)

namespace Answer

variable {ft : FnType}

/-- The Core result of an answer. A module is resumed with `resumeResult s t v.toResult`
(the spec's `$lift_result`), and a strategy-definable host (M2) returns `v.toResult`. -/
def toResult : Answer ft → Result
  | .values vs => .values vs.1
  | .trap => .trap
  | .throw a => .throw a

/-- `toResult` is injective. -/
theorem toResult_injective : Function.Injective (toResult (ft := ft)) := by
  intro a b h
  cases a with
  | values vs =>
    cases b with
    | values ws =>
      simp only [toResult, Result.values.injEq] at h
      exact congrArg Answer.values (Subtype.ext h)
    | trap => simp [toResult] at h
    | throw _ => simp [toResult] at h
  | trap =>
    cases b with
    | values _ => simp [toResult] at h
    | trap => rfl
    | throw _ => simp [toResult] at h
  | throw a =>
    cases b with
    | values _ => simp [toResult] at h
    | trap => simp [toResult] at h
    | throw b =>
      simp only [toResult, Result.throw.injEq] at h
      exact congrArg Answer.throw h

open Classical in
/-- The answer reported for a Core result of a call of type `ft`; `none` when returned
values are not typed by `ft.results` (impossible for well-typed modules). -/
noncomputable def ofResult? (ft : FnType) : Result → Option (Answer ft)
  | .values vs =>
    if h : List.Forall₂ ScalarType.HasVal ft.results vs then some (.values ⟨vs, h⟩) else none
  | .trap => some .trap
  | .throw a => some (.throw a)

/-- `ofResult?` inverts `toResult`. -/
theorem toResult_of_ofResult? {r : Result} {v : Answer ft} (h : ofResult? ft r = some v) :
    v.toResult = r := by
  cases r with
  | values vs =>
    simp only [ofResult?] at h
    split at h
    · cases h; rfl
    · cases h
  | trap =>
    simp only [ofResult?, Option.some.injEq] at h
    subst h; rfl
  | throw a =>
    simp only [ofResult?, Option.some.injEq] at h
    subst h; rfl

theorem ofResult?_toResult (v : Answer ft) : ofResult? ft v.toResult = some v := by
  cases v with
  | values vs =>
    simp only [toResult, ofResult?]
    split
    · rfl
    · rename_i hn
      exact absurd vs.2 hn
  | trap => simp only [toResult, ofResult?]
  | throw a => simp only [toResult, ofResult?]

/-- The behaviour of an answer (`Behaviour.throws a` keeps the address). -/
def toBehaviour (v : Answer ft) : Behaviour Val := v.toResult.toBehaviour

/-- `v` names an exception address below `n` (or is not an exception). -/
def ThrowsBelow (n : Nat) : Answer ft → Prop
  | .throw a => a < n
  | _ => True

end Answer

/-- The signature of a single scalar function (M1): operations are typed argument lists
and every call has arity `Answer ft`. -/
abbrev fnSig (ft : FnType) : Sig.{0} where
  Op := Typed ft.params
  Ar _ := Answer ft

/-- The signature of an indexed family of scalar functions (the sum of the `fnSig`): an
operation is an index `i` with a call of the `i`-th function. -/
abbrev ifaceSig (ts : List FnType) : Sig.{0} where
  Op := Σ i : Fin ts.length, Typed (ts.get i).params
  Ar e := Answer (ts.get e.1)

open Classical in
/-- The operation of `ifaceSig ts` denoted by a host callout `h args`: function `h` with
typed arguments; `none` if `h` is out of range or the arguments are ill-typed. -/
noncomputable def ifaceOp? (ts : List FnType) (h : Nat) (args : List Val) :
    Option (ifaceSig ts).Op :=
  if hlt : h < ts.length then
    if ht : List.Forall₂ ScalarType.HasVal (ts.get ⟨h, hlt⟩).params args then
      some ⟨⟨h, hlt⟩, ⟨args, ht⟩⟩
    else none
  else none

/-- With no functions, the interface signature has no operations. -/
theorem ifaceSig_nil_op_isEmpty : IsEmpty (ifaceSig []).Op :=
  ⟨fun e => Fin.elim0 e.1⟩

end Silmaril.Wasm.Game
