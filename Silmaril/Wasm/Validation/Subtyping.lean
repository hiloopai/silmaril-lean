module

public import Silmaril.Wasm.Validation.DefTypes
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! # Type well-formedness and subtyping on semantic types (§2.1 core, §2.2)

The spec's type-validity judgments of §2.1 and its subtyping judgments of §2.2
are mutually recursive:

* `Heaptype_sub/trans` has a premise `Heaptype_ok`;
* `Heaptype_ok` → `Typeuse_ok` → `Deftype_ok` → `Rectype_ok2` → `Subtype_ok2`,
  and `Subtype_ok2` has a premise `Comptype_sub`.

So the recursive core of both sections lives in *one* mutual block here:

* `TyOk Δ t` — every `*_ok : OK` judgment on a semantic type of any sort
  (`Numtype_ok`, `Vectype_ok`, `Heaptype_ok`, `Reftype_ok`, `Valtype_ok`,
  `Typeuse_ok`, `Packtype_ok`, `Storagetype_ok`, `Fieldtype_ok`, `Comptype_ok`,
  `Deftype_ok`, `Resulttype_ok` as the list-kind instance);
* `SubOk2 Δ st i` — `Subtype_ok2: C ⊢ subtype : OK(i)`;
* `GroupOk2 Δ rt i` — `Rectype_ok2: C ⊢ rectype : OK(i)`;
* `Sub Δ a b` — every `*_sub` judgment between semantic types of the same sort
  (`Numtype_sub`, `Vectype_sub`, `Heaptype_sub`, `Reftype_sub`, `Valtype_sub`,
  `Packtype_sub`, `Storagetype_sub`, `Fieldtype_sub`, `Comptype_sub`,
  `Deftype_sub`, and `Resulttype_sub` as the pointwise list-kind instance).

The non-recursive judgments over these (limits, memory/table/global/tag/extern
types, instruction types, `Rectype_ok: OK(x)` for modules) are in
`Validation/TypeOk.lean` and `Validation/Subtyping/Extern.lean`.

**Context.** Only the `TYPES` and `RECS` fields of a context are read by these
rules, so they are parameterised by `TypeCtx` (`Context` extends it). This makes
every context update that leaves the type fields alone (labels, locals, return)
transparent to typing of types *by `rfl`*.

**Rule-for-rule fidelity.** Every constructor is one spec rule; the doc comment
names it. The single deviation of representation: `Resulttype_sub` and the
`STRUCT` prefix premise are the list-kind constructors `nil`/`cons` (pointwise),
with the `STRUCT` width part expressed by `Ty.app` in `struct`. The list-kind
`nil`/`cons` constructors are available at every list sort, but only the value
and field sorts are used by other rules.
-/

namespace Silmaril.Wasm.Validation

/-- The type fields of a validation context (`C.TYPES`, `C.RECS`). -/
structure TypeCtx where
  types : List DefType := []
  recs : List CSubType := []
  deriving DecidableEq, Repr

/-- `$unrollht_(C, typeuse)` (§2.1). -/
def TypeCtx.unrollUse (Δ : TypeCtx) : CTypeUse → Option CSubType
  | .dt d => unrolldt d
  | .idx x => Δ.types[x]? >>= unrolldt
  | .recv i => Δ.recs[i]?

/-- `$before(typeuse, i)` (§2.1). -/
def before : CTypeUse → Nat → Bool
  | .recv j, i => j < i
  | _, _ => true

/-- The context `C, RECS subtype*` used by `Deftype_ok`. This *replaces* the
`RECS` field by the group's own sub types rather than appending to it.

SpecTec's `C, RECS st*` is record extension (append). The two readings agree
whenever the outer `RECS` is empty (`TypeCtx.withRecs_of_recs_nil`), which is the
case for the spec's own uses: a `_DEF` deftype is closed, so its `REC j`
indices refer to its own group only. In this development contexts are closed
(every `_IDX` is replaced by the corresponding `_DEF`), so a group's fields
routinely contain `_DEF` deftypes of *earlier* groups; checking one of those
inside `GroupOk2` happens under a non-empty outer `RECS`, and appending would
make the inner `REC j` resolve against the outer group. Replacing gives the
correct scoping of `REC j` (the only indices a closed deftype may contain). -/
def TypeCtx.withRecs (Δ : TypeCtx) (sts : List CSubType) : TypeCtx :=
  { Δ with recs := sts }

/-- The replacement reading of `C, RECS st*` agrees with the literal (append)
reading when the outer `RECS` is empty. -/
theorem TypeCtx.withRecs_of_recs_nil (Δ : TypeCtx) (sts : List CSubType)
    (h : Δ.recs = []) : Δ.withRecs sts = { Δ with recs := Δ.recs ++ sts } := by
  simp [TypeCtx.withRecs, h]

mutual

/-- The `*_ok : OK` judgments of §2.1 on semantic types of every sort. -/
inductive TyOk : TypeCtx → {k : TKind} → Ty k → Prop where
  /-- `Typeuse_ok/typeidx`. -/
  | idx {Δ : TypeCtx} {x : Nat} {d : DefType} (h : Δ.types[x]? = some d) :
      TyOk Δ (.idx x)
  /-- `Typeuse_ok/rec`. -/
  | recv {Δ : TypeCtx} {i : Nat} {st : CSubType} (h : Δ.recs[i]? = some st) :
      TyOk Δ (.recv i)
  /-- `Typeuse_ok/deftype`. -/
  | dt {Δ : TypeCtx} {d : DefType} (h : TyOk Δ d) : TyOk Δ (.dt d)
  /-- `Deftype_ok`: `C, RECS subtype^n ⊢ rectype : OK(0)` and `i < n`. -/
  | defn {Δ : TypeCtx} {subs : Ty (.list .sub)} {i : Nat}
      (h : GroupOk2 (Δ.withRecs subs.toList) (.group subs) 0) (hi : i < subs.length) :
      TyOk Δ (.defn (.group subs) i)
  /-- `Heaptype_ok/abs`. -/
  | abs {Δ : TypeCtx} (a : AbsHeapType) : TyOk Δ (.abs a)
  /-- `Heaptype_ok/bot`. -/
  | bot {Δ : TypeCtx} : TyOk Δ .bot
  /-- `Heaptype_ok/typeuse`. -/
  | use {Δ : TypeCtx} {u : CTypeUse} (h : TyOk Δ u) : TyOk Δ (.use u)
  /-- `Reftype_ok`. -/
  | ref {Δ : TypeCtx} {n : Bool} {h : CHeapType} (hh : TyOk Δ h) : TyOk Δ (.ref n h)
  /-- `Valtype_ok/num` (with `Numtype_ok`). -/
  | num {Δ : TypeCtx} (t : NumType) : TyOk Δ (.num t)
  /-- `Valtype_ok/vec` (with `Vectype_ok`). -/
  | vec {Δ : TypeCtx} (t : VecType) : TyOk Δ (.vec t)
  /-- `Valtype_ok/ref`. -/
  | refv {Δ : TypeCtx} {r : CRefType} (h : TyOk Δ r) : TyOk Δ (.refv r)
  /-- `Valtype_ok/bot`. -/
  | botv {Δ : TypeCtx} : TyOk Δ .botv
  /-- `Storagetype_ok/val`. -/
  | val {Δ : TypeCtx} {t : CValType} (h : TyOk Δ t) : TyOk Δ (.val t)
  /-- `Storagetype_ok/pack` (with `Packtype_ok`). -/
  | pack {Δ : TypeCtx} (p : PackType) : TyOk Δ (.pack p)
  /-- `Fieldtype_ok`. -/
  | field {Δ : TypeCtx} {m : Mutability} {s : CStorageType} (h : TyOk Δ s) :
      TyOk Δ (.field m s)
  /-- `Comptype_ok/struct`. -/
  | struct {Δ : TypeCtx} {fs : Ty (.list .field)} (h : TyOk Δ fs) : TyOk Δ (.struct fs)
  /-- `Comptype_ok/array`. -/
  | array {Δ : TypeCtx} {f : CFieldType} (h : TyOk Δ f) : TyOk Δ (.array f)
  /-- `Comptype_ok/func` (with two `Resulttype_ok`). -/
  | func {Δ : TypeCtx} {ps rs : Ty (.list .val)} (hp : TyOk Δ ps) (hr : TyOk Δ rs) :
      TyOk Δ (.func ps rs)
  /-- Sequences: every element is valid (`Resulttype_ok`, and the `(…)*` premises). -/
  | nil {Δ : TypeCtx} {k : TKind} : TyOk Δ (.nil : Ty (.list k))
  | cons {Δ : TypeCtx} {k : TKind} {a : Ty k} {l : Ty (.list k)}
      (ha : TyOk Δ a) (hl : TyOk Δ l) : TyOk Δ (.cons a l)

/-- `Subtype_ok2: C ⊢ SUB final? typeuse* comptype : OK(i)`. The premise
`|typeuse*| ≤ 1` is represented by the two constructors. The declared supertype
must unroll to a *non-final* sub type (`SUB typeuse'* comptype'`). -/
inductive SubOk2 : TypeCtx → CSubType → Nat → Prop where
  | noSuper {Δ : TypeCtx} {fin : Bool} {ct : CCompType} {i : Nat}
      (hct : TyOk Δ ct) : SubOk2 Δ (.sub fin .nil ct) i
  | oneSuper {Δ : TypeCtx} {fin : Bool} {u : CTypeUse} {ct : CCompType} {i : Nat}
      {sups' : Ty (.list .use)} {ct' : CCompType}
      (hu : TyOk Δ u) (hb : before u i = true)
      (hunroll : Δ.unrollUse u = some (.sub false sups' ct'))
      (hct : TyOk Δ ct) (hsub : Sub Δ ct ct') :
      SubOk2 Δ (.sub fin (.cons u .nil) ct) i

/-- `Rectype_ok2: C ⊢ rectype : OK(i)`. -/
inductive GroupOk2 : TypeCtx → CRecType → Nat → Prop where
  | nil {Δ : TypeCtx} {i : Nat} : GroupOk2 Δ (.group .nil) i
  | cons {Δ : TypeCtx} {st : CSubType} {sts : Ty (.list .sub)} {i : Nat}
      (h : SubOk2 Δ st i) (hs : GroupOk2 Δ (.group sts) (i + 1)) :
      GroupOk2 Δ (.group (.cons st sts)) i

/-- The subtyping judgments of §2.2 on semantic types of every sort. -/
inductive Sub : TypeCtx → {k : TKind} → Ty k → Ty k → Prop where
  /-- `Heaptype_sub/refl`. -/
  | heapRefl {Δ : TypeCtx} {h : CHeapType} : Sub Δ h h
  /-- `Heaptype_sub/trans`. -/
  | heapTrans {Δ : TypeCtx} {h₁ h' h₂ : CHeapType}
      (hok : TyOk Δ h') (h₁' : Sub Δ h₁ h') (h'₂ : Sub Δ h' h₂) : Sub Δ h₁ h₂
  /-- `Heaptype_sub/eq-any`. -/
  | eqAny {Δ : TypeCtx} : Sub Δ (.abs .eq) (.abs .any)
  /-- `Heaptype_sub/i31-eq`. -/
  | i31Eq {Δ : TypeCtx} : Sub Δ (.abs .i31) (.abs .eq)
  /-- `Heaptype_sub/struct-eq`. -/
  | structEq {Δ : TypeCtx} : Sub Δ (.abs .struct) (.abs .eq)
  /-- `Heaptype_sub/array-eq`. -/
  | arrayEq {Δ : TypeCtx} : Sub Δ (.abs .array) (.abs .eq)
  /-- `Heaptype_sub/struct`. -/
  | defStruct {Δ : TypeCtx} {d : DefType} {fs : Ty (.list .field)}
      (h : Expand d (.struct fs)) : Sub Δ (.use (.dt d)) (.abs .struct)
  /-- `Heaptype_sub/array`. -/
  | defArray {Δ : TypeCtx} {d : DefType} {f : CFieldType}
      (h : Expand d (.array f)) : Sub Δ (.use (.dt d)) (.abs .array)
  /-- `Heaptype_sub/func`. -/
  | defFunc {Δ : TypeCtx} {d : DefType} {ps rs : Ty (.list .val)}
      (h : Expand d (.func ps rs)) : Sub Δ (.use (.dt d)) (.abs .func)
  /-- `Heaptype_sub/def`. -/
  | defDef {Δ : TypeCtx} {d₁ d₂ : DefType} (h : Sub Δ d₁ d₂) :
      Sub Δ (.use (.dt d₁)) (.use (.dt d₂))
  /-- `Heaptype_sub/typeidx-l`. -/
  | idxL {Δ : TypeCtx} {x : Nat} {d : DefType} {h : CHeapType}
      (hx : Δ.types[x]? = some d) (hs : Sub Δ (.use (.dt d)) h) : Sub Δ (.use (.idx x)) h
  /-- `Heaptype_sub/typeidx-r`. -/
  | idxR {Δ : TypeCtx} {x : Nat} {d : DefType} {h : CHeapType}
      (hx : Δ.types[x]? = some d) (hs : Sub Δ h (.use (.dt d))) : Sub Δ h (.use (.idx x))
  /-- `Heaptype_sub/rec-struct`.

  **Audit note** (applies to `recStruct`, `recArray`, `recFunc`): the spec
  premise is `C.RECS[i] = SUB final? (STRUCT fieldtype*)`, which omits the
  `typeuse*` component. SpecTec's convention elsewhere (e.g. `SUB typeuse'*
  comptype'` in `Subtype_ok2` meaning non-final; `SUB FINAL (FUNC …)` in the
  text format) reads an omitted iteration as `eps`, so the literal rule only
  covers parent-free `REC` members. These constructors accept any `sups`, a
  conservative generalisation that is admissible whenever the recursive group
  is valid (via `rec-sub` and the supertype's own rule). -/
  | recStruct {Δ : TypeCtx} {i : Nat} {fin : Bool} {sups : Ty (.list .use)}
      {fs : Ty (.list .field)} (h : Δ.recs[i]? = some (.sub fin sups (.struct fs))) :
      Sub Δ (.use (.recv i)) (.abs .struct)
  /-- `Heaptype_sub/rec-array`. -/
  | recArray {Δ : TypeCtx} {i : Nat} {fin : Bool} {sups : Ty (.list .use)}
      {f : CFieldType} (h : Δ.recs[i]? = some (.sub fin sups (.array f))) :
      Sub Δ (.use (.recv i)) (.abs .array)
  /-- `Heaptype_sub/rec-func`. -/
  | recFunc {Δ : TypeCtx} {i : Nat} {fin : Bool} {sups : Ty (.list .use)}
      {ps rs : Ty (.list .val)} (h : Δ.recs[i]? = some (.sub fin sups (.func ps rs))) :
      Sub Δ (.use (.recv i)) (.abs .func)
  /-- `Heaptype_sub/rec-sub`. -/
  | recSub {Δ : TypeCtx} {i j : Nat} {fin : Bool} {sups : Ty (.list .use)}
      {ct : CCompType} {u : CTypeUse}
      (h : Δ.recs[i]? = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u) :
      Sub Δ (.use (.recv i)) (.use u)
  /-- `Heaptype_sub/none`. -/
  | none {Δ : TypeCtx} {h : CHeapType} (hs : Sub Δ h (.abs .any)) (hb : h ≠ .bot) :
      Sub Δ (.abs .none) h
  /-- `Heaptype_sub/nofunc`. -/
  | nofunc {Δ : TypeCtx} {h : CHeapType} (hs : Sub Δ h (.abs .func)) (hb : h ≠ .bot) :
      Sub Δ (.abs .nofunc) h
  /-- `Heaptype_sub/noexn`. -/
  | noexn {Δ : TypeCtx} {h : CHeapType} (hs : Sub Δ h (.abs .exn)) (hb : h ≠ .bot) :
      Sub Δ (.abs .noexn) h
  /-- `Heaptype_sub/noextern`. -/
  | noextern {Δ : TypeCtx} {h : CHeapType} (hs : Sub Δ h (.abs .extern)) (hb : h ≠ .bot) :
      Sub Δ (.abs .noextern) h
  /-- `Heaptype_sub/bot`. -/
  | bot {Δ : TypeCtx} {h : CHeapType} : Sub Δ .bot h
  /-- `Reftype_sub/nonnull`. -/
  | refNonNull {Δ : TypeCtx} {h₁ h₂ : CHeapType} (h : Sub Δ h₁ h₂) :
      Sub Δ (.ref false h₁) (.ref false h₂)
  /-- `Reftype_sub/null`. -/
  | refNull {Δ : TypeCtx} {n : Bool} {h₁ h₂ : CHeapType} (h : Sub Δ h₁ h₂) :
      Sub Δ (.ref n h₁) (.ref true h₂)
  /-- `Valtype_sub/num` (with `Numtype_sub`). -/
  | num {Δ : TypeCtx} {t : NumType} : Sub Δ (.num t) (.num t)
  /-- `Valtype_sub/vec` (with `Vectype_sub`). -/
  | vec {Δ : TypeCtx} {t : VecType} : Sub Δ (.vec t) (.vec t)
  /-- `Valtype_sub/ref`. -/
  | refv {Δ : TypeCtx} {r₁ r₂ : CRefType} (h : Sub Δ r₁ r₂) : Sub Δ (.refv r₁) (.refv r₂)
  /-- `Valtype_sub/bot`. -/
  | botv {Δ : TypeCtx} {t : CValType} : Sub Δ .botv t
  /-- `Storagetype_sub/val`. -/
  | val {Δ : TypeCtx} {t₁ t₂ : CValType} (h : Sub Δ t₁ t₂) : Sub Δ (.val t₁) (.val t₂)
  /-- `Storagetype_sub/pack` (with `Packtype_sub`). -/
  | pack {Δ : TypeCtx} {p : PackType} : Sub Δ (.pack p) (.pack p)
  /-- `Fieldtype_sub/const`. -/
  | fieldConst {Δ : TypeCtx} {z₁ z₂ : CStorageType} (h : Sub Δ z₁ z₂) :
      Sub Δ (.field .const z₁) (.field .const z₂)
  /-- `Fieldtype_sub/var`. -/
  | fieldVar {Δ : TypeCtx} {z₁ z₂ : CStorageType} (h₁ : Sub Δ z₁ z₂) (h₂ : Sub Δ z₂ z₁) :
      Sub Δ (.field .var z₁) (.field .var z₂)
  /-- `Comptype_sub/struct`: `STRUCT (ft_1* ft'_1*) <: STRUCT ft_2*`. -/
  | struct {Δ : TypeCtx} {fs₁ extra fs₂ : Ty (.list .field)} (h : Sub Δ fs₁ fs₂) :
      Sub Δ (.struct (fs₁.app extra)) (.struct fs₂)
  /-- `Comptype_sub/array`. -/
  | array {Δ : TypeCtx} {f₁ f₂ : CFieldType} (h : Sub Δ f₁ f₂) :
      Sub Δ (.array f₁) (.array f₂)
  /-- `Comptype_sub/func` (contravariant parameters, covariant results). -/
  | func {Δ : TypeCtx} {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)}
      (hp : Sub Δ ps₂ ps₁) (hr : Sub Δ rs₁ rs₂) : Sub Δ (.func ps₁ rs₁) (.func ps₂ rs₂)
  /-- `Deftype_sub/refl`: equal after closure (`$clos_deftype`). -/
  | defRefl {Δ : TypeCtx} {d₁ d₂ : DefType} (h : d₁.clos Δ.types = d₂.clos Δ.types) :
      Sub Δ d₁ d₂
  /-- `Deftype_sub/super`. -/
  | defSuper {Δ : TypeCtx} {d₁ d₂ : DefType} {fin : Bool} {sups : Ty (.list .use)}
      {ct : CCompType} {j : Nat} {u : CTypeUse}
      (h : unrolldt d₁ = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u)
      (hs : Sub Δ (.use u) (.use (.dt d₂))) : Sub Δ d₁ d₂
  /-- Pointwise sequences (`Resulttype_sub`, `(Fieldtype_sub)*`): empty. -/
  | nil {Δ : TypeCtx} {k : TKind} : Sub Δ (.nil : Ty (.list k)) .nil
  /-- Pointwise sequences: cons. -/
  | cons {Δ : TypeCtx} {k : TKind} {a b : Ty k} {l l' : Ty (.list k)}
      (h : Sub Δ a b) (hl : Sub Δ l l') : Sub Δ (.cons a l) (.cons b l')

end

/-- `Resulttype_sub` on Lean lists (bottom-first stacks). -/
def ResultSub (Δ : TypeCtx) (ts₁ ts₂ : List CValType) : Prop :=
  List.Forall₂ (Sub Δ) ts₁ ts₂

/-- `Resulttype_ok` on Lean lists. -/
def ResultOk (Δ : TypeCtx) (ts : List CValType) : Prop := ∀ t ∈ ts, TyOk Δ t

theorem ResultSub.iff_sub (Δ : TypeCtx) (ts₁ ts₂ : List CValType) :
    ResultSub Δ ts₁ ts₂ ↔ Sub Δ (Ty.ofList ts₁) (Ty.ofList ts₂) := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hab _ ih => exact .cons hab ih
  · induction ts₁ generalizing ts₂ with
    | nil =>
      intro h
      cases ts₂ with
      | nil => exact .nil
      | cons b l => cases h
    | cons a l ih =>
      intro h
      cases ts₂ with
      | nil => cases h
      | cons b l' =>
        cases h with
        | cons hab hl => exact .cons hab (ih _ hl)

end Silmaril.Wasm.Validation
