module

public import Silmaril.Wasm.Validation.Context

@[expose] public section

/-! # Non-recursive type well-formedness (§2.1)

The recursive core of §2.1 (`Heaptype_ok` … `Deftype_ok`, `Rectype_ok2`,
`Subtype_ok2`) is `TyOk`/`SubOk2`/`GroupOk2` in `Validation/Subtyping.lean`.
This file has the remaining judgments:

* `Limits_ok` is the existing `Limits.Valid` (`Validation/Types.lean`);
* `Tagtype_ok`, `Globaltype_ok`, `Memtype_ok`, `Tabletype_ok`, `Externtype_ok`
  on closed types;
* `Subtype_ok`/`Rectype_ok` with `OK(x)`, the module-level group check used by
  `Types_ok` (§2.4). They take *source* sub types (`_IDX` supertypes) and close
  their bodies against a context that already contains the group (as the spec's
  `Type_ok` does).
-/

namespace Silmaril.Wasm.Validation

/-- `Tagtype_ok`: the tag's type expands to a function type with no results. -/
def TagTypeOk (Δ : TypeCtx) (d : DefType) : Prop :=
  TyOk Δ d ∧ ∃ ps, Expand d (.func ps .nil)

/-- `Globaltype_ok`. -/
def GlobalTypeOk (Δ : TypeCtx) (g : CGlobalType) : Prop := TyOk Δ g.type

/-- `Memtype_ok`: `Limits_ok` within `2^(|at| - 16)` pages. -/
def MemTypeOk (m : MemoryType) : Prop := m.Valid

/-- `Tabletype_ok`: `Limits_ok` within `2^|at| - 1` and `Reftype_ok`. -/
def TableTypeOk (Δ : TypeCtx) (t : CTableType) : Prop :=
  t.limits.Valid (2 ^ t.address.width - 1) ∧ TyOk Δ t.element

/-- `Externtype_ok`. -/
inductive ExternTypeOk (Δ : TypeCtx) : CExternType → Prop where
  | tag {d : DefType} (h : TagTypeOk Δ d) : ExternTypeOk Δ (.tag d)
  | global {g : CGlobalType} (h : GlobalTypeOk Δ g) : ExternTypeOk Δ (.global g)
  | mem {m : MemoryType} (h : MemTypeOk m) : ExternTypeOk Δ (.mem m)
  | table {t : CTableType} (h : TableTypeOk Δ t) : ExternTypeOk Δ (.table t)
  | func {d : DefType} {ps rs : Ty (.list .val)} (h : TyOk Δ d) (he : Expand d (.func ps rs)) :
      ExternTypeOk Δ (.func d)

/-- Close a source composite type in a context. -/
def Context.closeComp (C : Context) (ct : CompositeType) : CCompType :=
  (liftComp ct).substAll (C.types.map .dt)

/-- `Subtype_ok: C ⊢ SUB FINAL? (_IDX x)* comptype : OK(x_0)`. The premise
`|x*| ≤ 1` is represented by the two constructors; the declared supertype must
precede `x_0` and unroll to a non-final sub type whose body the (closed) body
matches. -/
inductive SubTypeOkAt (C : Context) : SubType → Nat → Prop where
  | noSuper {fin : Bool} {ct : CompositeType} {x₀ : Nat}
      (hct : TyOk C.toTypeCtx (C.closeComp ct)) : SubTypeOkAt C ⟨fin, [], ct⟩ x₀
  | oneSuper {fin : Bool} {x : TypeIdx} {ct : CompositeType} {x₀ : Nat} {d : DefType}
      {sups' : Ty (.list .use)} {ct' : CCompType}
      (hx : x.toNat < x₀) (hd : C.types[x.toNat]? = some d)
      (hunroll : unrolldt d = some (.sub false sups' ct'))
      (hct : TyOk C.toTypeCtx (C.closeComp ct))
      (hsub : Sub C.toTypeCtx (C.closeComp ct) ct') :
      SubTypeOkAt C ⟨fin, [x], ct⟩ x₀

/-- `Rectype_ok: C ⊢ rectype : OK(x)` (the `empty` and `cons` rules). -/
inductive RecTypeOkAt (C : Context) : List SubType → Nat → Prop where
  | nil {x : Nat} : RecTypeOkAt C [] x
  | cons {st : SubType} {sts : List SubType} {x : Nat}
      (h : SubTypeOkAt C st x) (hs : RecTypeOkAt C sts (x + 1)) : RecTypeOkAt C (st :: sts) x

end Silmaril.Wasm.Validation
