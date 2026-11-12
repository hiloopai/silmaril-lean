module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round4.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track agreety-okintro: canonical validity derivations

`RefOkV.AgreeTy.okIntro` asks SpecTec's `Reftype_ok {}`, read by `DDerivesB`, to hold at every
bounded Core-valid reference type. A Core derivation of `TyOk {}` cannot be transcribed rule for
rule: inside a recursive group, `Subtype_ok2` checks `Comptype_sub` under `RECS`, and Core's
subtyping derivations may route `Heaptype_sub/trans` through **unbounded** middle types, whose
images are not typed SpecTec values (so `DDerivesB` cannot quantify over them).

This file states the **canonical** form of a derivation, which the interpreter can read rule for
rule:

* `TyOkB`, `SubOk2B`, `GroupOk2B`: `RefOkV.TyOkS`/`SubOk2S`/`GroupOk2S` (SpecTec's validation
  judgments on Core types: `Deftype_ok` checks its group under `RECS = subs ++ C.RECS`), over
  `SubB`, without `Typeuse_ok/typeidx` (contexts here have no `TYPES`).
* `SubB`: `RefOkV.SubS` (SpecTec's subtyping on Core types, with the parent-free `rec-*` rules)
  where **`Heaptype_sub/trans` needs a bounded middle type** (`Round4.tyBnd`), without the
  `typeidx-*` rules and without `Deftype_sub/refl` (reflexivity is `Heaptype_sub/refl` on the
  heap type).

The Core half (`tyOkB_of_tyOk`: Core-valid bounded types have canonical derivations, through
Silmaril's `REC`-aware subtyping checker `Sub.checkRWith`) and the interpreter half
(`TyOkB` is read by `DDerivesB`) are proved in `Silmaril/Proofs/Wasm/SpecTec/Sim/Round6/AgreeOk/`.
See `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.RefOkV (withRecsA)

mutual

/-- SpecTec's `*_ok : OK` judgments on Core types, over canonical subtyping (`SubB`). -/
inductive TyOkB : TypeCtx → {k : TKind} → Ty k → Prop where
  /-- `Typeuse_ok/rec`. -/
  | recv {Δ : TypeCtx} {i : Nat} {st : CSubType} (h : Δ.recs[i]? = some st) :
      TyOkB Δ (.recv i)
  /-- `Typeuse_ok/deftype`. -/
  | dt {Δ : TypeCtx} {d : DefType} (h : TyOkB Δ d) : TyOkB Δ (.dt d)
  /-- `Deftype_ok`, under `C, RECS subtype^n` read as SpecTec's record extension. -/
  | defn {Δ : TypeCtx} {subs : Ty (.list .sub)} {i : Nat}
      (h : GroupOk2B (withRecsA Δ subs.toList) (.group subs) 0) (hi : i < subs.length) :
      TyOkB Δ (.defn (.group subs) i)
  /-- `Heaptype_ok/abs`. -/
  | abs {Δ : TypeCtx} (a : AbsHeapType) : TyOkB Δ (.abs a)
  /-- `Heaptype_ok/bot`. -/
  | bot {Δ : TypeCtx} : TyOkB Δ .bot
  /-- `Heaptype_ok/typeuse`. -/
  | use {Δ : TypeCtx} {u : CTypeUse} (h : TyOkB Δ u) : TyOkB Δ (.use u)
  /-- `Reftype_ok`. -/
  | ref {Δ : TypeCtx} {n : Bool} {h : CHeapType} (hh : TyOkB Δ h) : TyOkB Δ (.ref n h)
  /-- `Valtype_ok/num`. -/
  | num {Δ : TypeCtx} (t : NumType) : TyOkB Δ (.num t)
  /-- `Valtype_ok/vec`. -/
  | vec {Δ : TypeCtx} (t : VecType) : TyOkB Δ (.vec t)
  /-- `Valtype_ok/ref`. -/
  | refv {Δ : TypeCtx} {r : CRefType} (h : TyOkB Δ r) : TyOkB Δ (.refv r)
  /-- `Valtype_ok/bot`. -/
  | botv {Δ : TypeCtx} : TyOkB Δ .botv
  /-- `Storagetype_ok/val`. -/
  | val {Δ : TypeCtx} {t : CValType} (h : TyOkB Δ t) : TyOkB Δ (.val t)
  /-- `Storagetype_ok/pack`. -/
  | pack {Δ : TypeCtx} (p : PackType) : TyOkB Δ (.pack p)
  /-- `Fieldtype_ok`. -/
  | field {Δ : TypeCtx} {m : Mutability} {s : CStorageType} (h : TyOkB Δ s) :
      TyOkB Δ (.field m s)
  /-- `Comptype_ok/struct`. -/
  | struct {Δ : TypeCtx} {fs : Ty (.list .field)} (h : TyOkB Δ fs) : TyOkB Δ (.struct fs)
  /-- `Comptype_ok/array`. -/
  | array {Δ : TypeCtx} {f : CFieldType} (h : TyOkB Δ f) : TyOkB Δ (.array f)
  /-- `Comptype_ok/func`. -/
  | func {Δ : TypeCtx} {ps rs : Ty (.list .val)} (hp : TyOkB Δ ps) (hr : TyOkB Δ rs) :
      TyOkB Δ (.func ps rs)
  /-- Sequences (`Resulttype_ok`, iterated premises): empty. -/
  | nil {Δ : TypeCtx} {k : TKind} : TyOkB Δ (.nil : Ty (.list k))
  /-- Sequences: cons. -/
  | cons {Δ : TypeCtx} {k : TKind} {a : Ty k} {l : Ty (.list k)}
      (ha : TyOkB Δ a) (hl : TyOkB Δ l) : TyOkB Δ (.cons a l)

/-- `Subtype_ok2` on Core types, over canonical subtyping. -/
inductive SubOk2B : TypeCtx → CSubType → Nat → Prop where
  | noSuper {Δ : TypeCtx} {fin : Bool} {ct : CCompType} {i : Nat}
      (hct : TyOkB Δ ct) : SubOk2B Δ (.sub fin .nil ct) i
  | oneSuper {Δ : TypeCtx} {fin : Bool} {u : CTypeUse} {ct : CCompType} {i : Nat}
      {sups' : Ty (.list .use)} {ct' : CCompType}
      (hu : TyOkB Δ u) (hb : before u i = true)
      (hunroll : Δ.unrollUse u = some (.sub false sups' ct'))
      (hct : TyOkB Δ ct) (hsub : SubB Δ ct ct') :
      SubOk2B Δ (.sub fin (.cons u .nil) ct) i

/-- `Rectype_ok2` on Core types, over canonical subtyping. -/
inductive GroupOk2B : TypeCtx → CRecType → Nat → Prop where
  | nil {Δ : TypeCtx} {i : Nat} : GroupOk2B Δ (.group .nil) i
  | cons {Δ : TypeCtx} {st : CSubType} {sts : Ty (.list .sub)} {i : Nat}
      (h : SubOk2B Δ st i) (hs : GroupOk2B Δ (.group sts) (i + 1)) :
      GroupOk2B Δ (.group (.cons st sts)) i

/-- SpecTec's `*_sub` judgments on Core types, **canonical**: `Heaptype_sub/trans` only through
bounded valid middle types; no `typeidx-*` rules and no `Deftype_sub/refl`. -/
inductive SubB : TypeCtx → {k : TKind} → Ty k → Ty k → Prop where
  /-- `Heaptype_sub/refl`. -/
  | heapRefl {Δ : TypeCtx} {h : CHeapType} : SubB Δ h h
  /-- `Heaptype_sub/trans`, through a bounded middle type. -/
  | heapTrans {Δ : TypeCtx} {h₁ h' h₂ : CHeapType} (hbnd : Round4.tyBnd h' = true)
      (hok : TyOkB Δ h') (h₁' : SubB Δ h₁ h') (h'₂ : SubB Δ h' h₂) : SubB Δ h₁ h₂
  /-- `Heaptype_sub/eq-any`. -/
  | eqAny {Δ : TypeCtx} : SubB Δ (.abs .eq) (.abs .any)
  /-- `Heaptype_sub/i31-eq`. -/
  | i31Eq {Δ : TypeCtx} : SubB Δ (.abs .i31) (.abs .eq)
  /-- `Heaptype_sub/struct-eq`. -/
  | structEq {Δ : TypeCtx} : SubB Δ (.abs .struct) (.abs .eq)
  /-- `Heaptype_sub/array-eq`. -/
  | arrayEq {Δ : TypeCtx} : SubB Δ (.abs .array) (.abs .eq)
  /-- `Heaptype_sub/struct`. -/
  | defStruct {Δ : TypeCtx} {d : DefType} {fs : Ty (.list .field)}
      (h : Expand d (.struct fs)) : SubB Δ (.use (.dt d)) (.abs .struct)
  /-- `Heaptype_sub/array`. -/
  | defArray {Δ : TypeCtx} {d : DefType} {f : CFieldType}
      (h : Expand d (.array f)) : SubB Δ (.use (.dt d)) (.abs .array)
  /-- `Heaptype_sub/func`. -/
  | defFunc {Δ : TypeCtx} {d : DefType} {ps rs : Ty (.list .val)}
      (h : Expand d (.func ps rs)) : SubB Δ (.use (.dt d)) (.abs .func)
  /-- `Heaptype_sub/def`. -/
  | defDef {Δ : TypeCtx} {d₁ d₂ : DefType} (h : SubB Δ d₁ d₂) :
      SubB Δ (.use (.dt d₁)) (.use (.dt d₂))
  /-- `Heaptype_sub/rec-struct`, no supertypes. -/
  | recStruct {Δ : TypeCtx} {i : Nat} {fin : Bool} {fs : Ty (.list .field)}
      (h : Δ.recs[i]? = some (.sub fin .nil (.struct fs))) :
      SubB Δ (.use (.recv i)) (.abs .struct)
  /-- `Heaptype_sub/rec-array`, no supertypes. -/
  | recArray {Δ : TypeCtx} {i : Nat} {fin : Bool} {f : CFieldType}
      (h : Δ.recs[i]? = some (.sub fin .nil (.array f))) :
      SubB Δ (.use (.recv i)) (.abs .array)
  /-- `Heaptype_sub/rec-func`, no supertypes. -/
  | recFunc {Δ : TypeCtx} {i : Nat} {fin : Bool} {ps rs : Ty (.list .val)}
      (h : Δ.recs[i]? = some (.sub fin .nil (.func ps rs))) :
      SubB Δ (.use (.recv i)) (.abs .func)
  /-- `Heaptype_sub/rec-sub`. -/
  | recSub {Δ : TypeCtx} {i j : Nat} {fin : Bool} {sups : Ty (.list .use)}
      {ct : CCompType} {u : CTypeUse}
      (h : Δ.recs[i]? = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u) :
      SubB Δ (.use (.recv i)) (.use u)
  /-- `Heaptype_sub/none`. -/
  | none {Δ : TypeCtx} {h : CHeapType} (hs : SubB Δ h (.abs .any)) (hb : h ≠ .bot) :
      SubB Δ (.abs .none) h
  /-- `Heaptype_sub/nofunc`. -/
  | nofunc {Δ : TypeCtx} {h : CHeapType} (hs : SubB Δ h (.abs .func)) (hb : h ≠ .bot) :
      SubB Δ (.abs .nofunc) h
  /-- `Heaptype_sub/noexn`. -/
  | noexn {Δ : TypeCtx} {h : CHeapType} (hs : SubB Δ h (.abs .exn)) (hb : h ≠ .bot) :
      SubB Δ (.abs .noexn) h
  /-- `Heaptype_sub/noextern`. -/
  | noextern {Δ : TypeCtx} {h : CHeapType} (hs : SubB Δ h (.abs .extern)) (hb : h ≠ .bot) :
      SubB Δ (.abs .noextern) h
  /-- `Heaptype_sub/bot`. -/
  | bot {Δ : TypeCtx} {h : CHeapType} : SubB Δ .bot h
  /-- `Reftype_sub/nonnull`. -/
  | refNonNull {Δ : TypeCtx} {h₁ h₂ : CHeapType} (h : SubB Δ h₁ h₂) :
      SubB Δ (.ref false h₁) (.ref false h₂)
  /-- `Reftype_sub/null`. -/
  | refNull {Δ : TypeCtx} {n : Bool} {h₁ h₂ : CHeapType} (h : SubB Δ h₁ h₂) :
      SubB Δ (.ref n h₁) (.ref true h₂)
  /-- `Valtype_sub/num`. -/
  | num {Δ : TypeCtx} {t : NumType} : SubB Δ (.num t) (.num t)
  /-- `Valtype_sub/vec`. -/
  | vec {Δ : TypeCtx} {t : VecType} : SubB Δ (.vec t) (.vec t)
  /-- `Valtype_sub/ref`. -/
  | refv {Δ : TypeCtx} {r₁ r₂ : CRefType} (h : SubB Δ r₁ r₂) : SubB Δ (.refv r₁) (.refv r₂)
  /-- `Valtype_sub/bot`. -/
  | botv {Δ : TypeCtx} {t : CValType} : SubB Δ .botv t
  /-- `Storagetype_sub/val`. -/
  | val {Δ : TypeCtx} {t₁ t₂ : CValType} (h : SubB Δ t₁ t₂) : SubB Δ (.val t₁) (.val t₂)
  /-- `Storagetype_sub/pack`. -/
  | pack {Δ : TypeCtx} {p : PackType} : SubB Δ (.pack p) (.pack p)
  /-- `Fieldtype_sub/const`. -/
  | fieldConst {Δ : TypeCtx} {z₁ z₂ : CStorageType} (h : SubB Δ z₁ z₂) :
      SubB Δ (.field .const z₁) (.field .const z₂)
  /-- `Fieldtype_sub/var`. -/
  | fieldVar {Δ : TypeCtx} {z₁ z₂ : CStorageType} (h₁ : SubB Δ z₁ z₂) (h₂ : SubB Δ z₂ z₁) :
      SubB Δ (.field .var z₁) (.field .var z₂)
  /-- `Comptype_sub/struct`. -/
  | struct {Δ : TypeCtx} {fs₁ extra fs₂ : Ty (.list .field)} (h : SubB Δ fs₁ fs₂) :
      SubB Δ (.struct (fs₁.app extra)) (.struct fs₂)
  /-- `Comptype_sub/array`. -/
  | array {Δ : TypeCtx} {f₁ f₂ : CFieldType} (h : SubB Δ f₁ f₂) :
      SubB Δ (.array f₁) (.array f₂)
  /-- `Comptype_sub/func`. -/
  | func {Δ : TypeCtx} {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)}
      (hp : SubB Δ ps₂ ps₁) (hr : SubB Δ rs₁ rs₂) : SubB Δ (.func ps₁ rs₁) (.func ps₂ rs₂)
  /-- `Deftype_sub/super`. -/
  | defSuper {Δ : TypeCtx} {d₁ d₂ : DefType} {fin : Bool} {sups : Ty (.list .use)}
      {ct : CCompType} {j : Nat} {u : CTypeUse}
      (h : unrolldt d₁ = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u)
      (hs : SubB Δ (.use u) (.use (.dt d₂))) : SubB Δ d₁ d₂
  /-- `Resulttype_sub`, pointwise: empty. -/
  | nil {Δ : TypeCtx} {k : TKind} : SubB Δ (.nil : Ty (.list k)) .nil
  /-- Pointwise: cons. -/
  | cons {Δ : TypeCtx} {k : TKind} {a b : Ty k} {l l' : Ty (.list k)}
      (h : SubB Δ a b) (hl : SubB Δ l l') : SubB Δ (.cons a l) (.cons b l')

end

/-- `Δ` with `M` appended to its `RECS` (as `RefOkV.ext`). -/
def ext (Δ : TypeCtx) (M : List CSubType) : TypeCtx := { Δ with recs := Δ.recs ++ M }

/-- The `RECS` of `Δ` are a valid group, as far as canonical subtyping needs: each declared
supertype comes earlier, is bounded, has canonical derivations in every extension, and unrolls
to a non-final subtype of the same kind. -/
def RecsGoodB (Δ : TypeCtx) : Prop :=
  ∀ (i : Nat) (st : CSubType), Δ.recs[i]? = some st → ∀ u ∈ st.supers, before u i = true ∧
    Round4.tyBnd u = true ∧ (∀ M, TyOkB (ext Δ M) u) ∧
    ∃ sups' ct', Δ.unrollUse u = some (.sub false sups' ct') ∧ compAbs ct' = compAbs st.body

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
