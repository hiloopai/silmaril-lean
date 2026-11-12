module

public import Silmaril.Wasm.Execution.Core.Typing.Store
public import Silmaril.Wasm.Validation.Subtyping.Check
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track refokbv-prove: SpecTec's type judgments, on Core types

`Round6.RefOkB.RefOkBV` asks SpecTec's `Ref_ok`, read by `DDerivesB`, to be Core's `RefOk` on
Core-valid stores and Core-valid closed reference types. SpecTec's `Ref_ok/sub` consults
`Reftype_ok {}` and `Reftype_sub {}`, and those differ from Core's `TyOk {}` and `Sub {}` in two
places (`docs/projects/spectec/README.md`):

1. **Append vs replace.** SpecTec's `Deftype_ok` checks a group under `C, RECS subtype*`, whose
   `RECS` is `subtype* ++ C.RECS`; Core's `TyOk.defn` *replaces* `RECS` (`TypeCtx.withRecs`).
2. **Parent-free `REC` rules.** SpecTec's `Heaptype_sub/rec-struct`, `rec-array` and `rec-func`
   only fire at `REC` members without declared supertypes (`SUB final? (STRUCT …)` writes
   `typeuse* = eps`); Core's `Sub.recStruct`, `recArray` and `recFunc` accept any supertypes.

This file transcribes SpecTec's judgments **rule for rule onto Core's `Ty`**, with exactly those
two differences:

* `TyOkS`, `SubOk2S`, `GroupOk2S`, `SubS`: `TyOk`, `SubOk2`, `GroupOk2`, `Sub` with `defn`
  checking under `RECS = subs ++ Δ.recs` (`TypeCtx.withRecsA`), and with the three `rec-*` kind
  rules restricted to `sups = .nil`. Every other constructor is Core's, rule for rule (each Core
  constructor already transcribes one SpecTec rule; see `Silmaril/Wasm/Validation/
  Subtyping.lean`).
* `RefOkS`: Core's `RefOk` with its `sub` rule reading `TyOkS {}` and `SubS {}`.

So the question `RefOkBV` asks splits in two: the interpreter reads SpecTec's relations as these
transcriptions (`Agree`, the interpreter half, open), and the transcriptions agree with Core on
Core-valid stores and types (the Core half, proved in this track: `refOkS_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

/-- SpecTec's `C, RECS subtype*`: record extension **prepends** the group's members to `RECS`. -/
def withRecsA (Δ : TypeCtx) (sts : List CSubType) : TypeCtx :=
  { Δ with recs := sts ++ Δ.recs }

mutual

/-- SpecTec's `*_ok : OK` judgments on Core types: `TyOk`, except that `Deftype_ok` checks the
group under `RECS = subs ++ Δ.recs` (`withRecsA`). -/
inductive TyOkS : TypeCtx → {k : TKind} → Ty k → Prop where
  /-- `Typeuse_ok/typeidx`. -/
  | idx {Δ : TypeCtx} {x : Nat} {d : DefType} (h : Δ.types[x]? = some d) : TyOkS Δ (.idx x)
  /-- `Typeuse_ok/rec`. -/
  | recv {Δ : TypeCtx} {i : Nat} {st : CSubType} (h : Δ.recs[i]? = some st) :
      TyOkS Δ (.recv i)
  /-- `Typeuse_ok/deftype`. -/
  | dt {Δ : TypeCtx} {d : DefType} (h : TyOkS Δ d) : TyOkS Δ (.dt d)
  /-- `Deftype_ok`, under `C, RECS subtype^n` read as SpecTec's record extension. -/
  | defn {Δ : TypeCtx} {subs : Ty (.list .sub)} {i : Nat}
      (h : GroupOk2S (withRecsA Δ subs.toList) (.group subs) 0) (hi : i < subs.length) :
      TyOkS Δ (.defn (.group subs) i)
  /-- `Heaptype_ok/abs`. -/
  | abs {Δ : TypeCtx} (a : AbsHeapType) : TyOkS Δ (.abs a)
  /-- `Heaptype_ok/bot`. -/
  | bot {Δ : TypeCtx} : TyOkS Δ .bot
  /-- `Heaptype_ok/typeuse`. -/
  | use {Δ : TypeCtx} {u : CTypeUse} (h : TyOkS Δ u) : TyOkS Δ (.use u)
  /-- `Reftype_ok`. -/
  | ref {Δ : TypeCtx} {n : Bool} {h : CHeapType} (hh : TyOkS Δ h) : TyOkS Δ (.ref n h)
  /-- `Valtype_ok/num`. -/
  | num {Δ : TypeCtx} (t : NumType) : TyOkS Δ (.num t)
  /-- `Valtype_ok/vec`. -/
  | vec {Δ : TypeCtx} (t : VecType) : TyOkS Δ (.vec t)
  /-- `Valtype_ok/ref`. -/
  | refv {Δ : TypeCtx} {r : CRefType} (h : TyOkS Δ r) : TyOkS Δ (.refv r)
  /-- `Valtype_ok/bot`. -/
  | botv {Δ : TypeCtx} : TyOkS Δ .botv
  /-- `Storagetype_ok/val`. -/
  | val {Δ : TypeCtx} {t : CValType} (h : TyOkS Δ t) : TyOkS Δ (.val t)
  /-- `Storagetype_ok/pack`. -/
  | pack {Δ : TypeCtx} (p : PackType) : TyOkS Δ (.pack p)
  /-- `Fieldtype_ok`. -/
  | field {Δ : TypeCtx} {m : Mutability} {s : CStorageType} (h : TyOkS Δ s) :
      TyOkS Δ (.field m s)
  /-- `Comptype_ok/struct`. -/
  | struct {Δ : TypeCtx} {fs : Ty (.list .field)} (h : TyOkS Δ fs) : TyOkS Δ (.struct fs)
  /-- `Comptype_ok/array`. -/
  | array {Δ : TypeCtx} {f : CFieldType} (h : TyOkS Δ f) : TyOkS Δ (.array f)
  /-- `Comptype_ok/func`. -/
  | func {Δ : TypeCtx} {ps rs : Ty (.list .val)} (hp : TyOkS Δ ps) (hr : TyOkS Δ rs) :
      TyOkS Δ (.func ps rs)
  /-- Sequences (`Resulttype_ok`, iterated premises): empty. -/
  | nil {Δ : TypeCtx} {k : TKind} : TyOkS Δ (.nil : Ty (.list k))
  /-- Sequences: cons. -/
  | cons {Δ : TypeCtx} {k : TKind} {a : Ty k} {l : Ty (.list k)}
      (ha : TyOkS Δ a) (hl : TyOkS Δ l) : TyOkS Δ (.cons a l)

/-- `Subtype_ok2` on Core types (`SubOk2` over `TyOkS`/`SubS`). -/
inductive SubOk2S : TypeCtx → CSubType → Nat → Prop where
  | noSuper {Δ : TypeCtx} {fin : Bool} {ct : CCompType} {i : Nat}
      (hct : TyOkS Δ ct) : SubOk2S Δ (.sub fin .nil ct) i
  | oneSuper {Δ : TypeCtx} {fin : Bool} {u : CTypeUse} {ct : CCompType} {i : Nat}
      {sups' : Ty (.list .use)} {ct' : CCompType}
      (hu : TyOkS Δ u) (hb : before u i = true)
      (hunroll : Δ.unrollUse u = some (.sub false sups' ct'))
      (hct : TyOkS Δ ct) (hsub : SubS Δ ct ct') :
      SubOk2S Δ (.sub fin (.cons u .nil) ct) i

/-- `Rectype_ok2` on Core types. -/
inductive GroupOk2S : TypeCtx → CRecType → Nat → Prop where
  | nil {Δ : TypeCtx} {i : Nat} : GroupOk2S Δ (.group .nil) i
  | cons {Δ : TypeCtx} {st : CSubType} {sts : Ty (.list .sub)} {i : Nat}
      (h : SubOk2S Δ st i) (hs : GroupOk2S Δ (.group sts) (i + 1)) :
      GroupOk2S Δ (.group (.cons st sts)) i

/-- SpecTec's `*_sub` judgments on Core types: `Sub`, except that `Heaptype_sub/rec-struct`,
`rec-array` and `rec-func` need a member **without** declared supertypes. -/
inductive SubS : TypeCtx → {k : TKind} → Ty k → Ty k → Prop where
  /-- `Heaptype_sub/refl`. -/
  | heapRefl {Δ : TypeCtx} {h : CHeapType} : SubS Δ h h
  /-- `Heaptype_sub/trans`. -/
  | heapTrans {Δ : TypeCtx} {h₁ h' h₂ : CHeapType}
      (hok : TyOkS Δ h') (h₁' : SubS Δ h₁ h') (h'₂ : SubS Δ h' h₂) : SubS Δ h₁ h₂
  /-- `Heaptype_sub/eq-any`. -/
  | eqAny {Δ : TypeCtx} : SubS Δ (.abs .eq) (.abs .any)
  /-- `Heaptype_sub/i31-eq`. -/
  | i31Eq {Δ : TypeCtx} : SubS Δ (.abs .i31) (.abs .eq)
  /-- `Heaptype_sub/struct-eq`. -/
  | structEq {Δ : TypeCtx} : SubS Δ (.abs .struct) (.abs .eq)
  /-- `Heaptype_sub/array-eq`. -/
  | arrayEq {Δ : TypeCtx} : SubS Δ (.abs .array) (.abs .eq)
  /-- `Heaptype_sub/struct`. -/
  | defStruct {Δ : TypeCtx} {d : DefType} {fs : Ty (.list .field)}
      (h : Expand d (.struct fs)) : SubS Δ (.use (.dt d)) (.abs .struct)
  /-- `Heaptype_sub/array`. -/
  | defArray {Δ : TypeCtx} {d : DefType} {f : CFieldType}
      (h : Expand d (.array f)) : SubS Δ (.use (.dt d)) (.abs .array)
  /-- `Heaptype_sub/func`. -/
  | defFunc {Δ : TypeCtx} {d : DefType} {ps rs : Ty (.list .val)}
      (h : Expand d (.func ps rs)) : SubS Δ (.use (.dt d)) (.abs .func)
  /-- `Heaptype_sub/def`. -/
  | defDef {Δ : TypeCtx} {d₁ d₂ : DefType} (h : SubS Δ d₁ d₂) :
      SubS Δ (.use (.dt d₁)) (.use (.dt d₂))
  /-- `Heaptype_sub/typeidx-l`. -/
  | idxL {Δ : TypeCtx} {x : Nat} {d : DefType} {h : CHeapType}
      (hx : Δ.types[x]? = some d) (hs : SubS Δ (.use (.dt d)) h) : SubS Δ (.use (.idx x)) h
  /-- `Heaptype_sub/typeidx-r`. -/
  | idxR {Δ : TypeCtx} {x : Nat} {d : DefType} {h : CHeapType}
      (hx : Δ.types[x]? = some d) (hs : SubS Δ h (.use (.dt d))) : SubS Δ h (.use (.idx x))
  /-- `Heaptype_sub/rec-struct`: `C.RECS[i] = SUB final? (STRUCT fieldtype*)`, no supertypes. -/
  | recStruct {Δ : TypeCtx} {i : Nat} {fin : Bool} {fs : Ty (.list .field)}
      (h : Δ.recs[i]? = some (.sub fin .nil (.struct fs))) :
      SubS Δ (.use (.recv i)) (.abs .struct)
  /-- `Heaptype_sub/rec-array`, no supertypes. -/
  | recArray {Δ : TypeCtx} {i : Nat} {fin : Bool} {f : CFieldType}
      (h : Δ.recs[i]? = some (.sub fin .nil (.array f))) :
      SubS Δ (.use (.recv i)) (.abs .array)
  /-- `Heaptype_sub/rec-func`, no supertypes. -/
  | recFunc {Δ : TypeCtx} {i : Nat} {fin : Bool} {ps rs : Ty (.list .val)}
      (h : Δ.recs[i]? = some (.sub fin .nil (.func ps rs))) :
      SubS Δ (.use (.recv i)) (.abs .func)
  /-- `Heaptype_sub/rec-sub`. -/
  | recSub {Δ : TypeCtx} {i j : Nat} {fin : Bool} {sups : Ty (.list .use)}
      {ct : CCompType} {u : CTypeUse}
      (h : Δ.recs[i]? = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u) :
      SubS Δ (.use (.recv i)) (.use u)
  /-- `Heaptype_sub/none`. -/
  | none {Δ : TypeCtx} {h : CHeapType} (hs : SubS Δ h (.abs .any)) (hb : h ≠ .bot) :
      SubS Δ (.abs .none) h
  /-- `Heaptype_sub/nofunc`. -/
  | nofunc {Δ : TypeCtx} {h : CHeapType} (hs : SubS Δ h (.abs .func)) (hb : h ≠ .bot) :
      SubS Δ (.abs .nofunc) h
  /-- `Heaptype_sub/noexn`. -/
  | noexn {Δ : TypeCtx} {h : CHeapType} (hs : SubS Δ h (.abs .exn)) (hb : h ≠ .bot) :
      SubS Δ (.abs .noexn) h
  /-- `Heaptype_sub/noextern`. -/
  | noextern {Δ : TypeCtx} {h : CHeapType} (hs : SubS Δ h (.abs .extern)) (hb : h ≠ .bot) :
      SubS Δ (.abs .noextern) h
  /-- `Heaptype_sub/bot`. -/
  | bot {Δ : TypeCtx} {h : CHeapType} : SubS Δ .bot h
  /-- `Reftype_sub/nonnull`. -/
  | refNonNull {Δ : TypeCtx} {h₁ h₂ : CHeapType} (h : SubS Δ h₁ h₂) :
      SubS Δ (.ref false h₁) (.ref false h₂)
  /-- `Reftype_sub/null`. -/
  | refNull {Δ : TypeCtx} {n : Bool} {h₁ h₂ : CHeapType} (h : SubS Δ h₁ h₂) :
      SubS Δ (.ref n h₁) (.ref true h₂)
  /-- `Valtype_sub/num`. -/
  | num {Δ : TypeCtx} {t : NumType} : SubS Δ (.num t) (.num t)
  /-- `Valtype_sub/vec`. -/
  | vec {Δ : TypeCtx} {t : VecType} : SubS Δ (.vec t) (.vec t)
  /-- `Valtype_sub/ref`. -/
  | refv {Δ : TypeCtx} {r₁ r₂ : CRefType} (h : SubS Δ r₁ r₂) : SubS Δ (.refv r₁) (.refv r₂)
  /-- `Valtype_sub/bot`. -/
  | botv {Δ : TypeCtx} {t : CValType} : SubS Δ .botv t
  /-- `Storagetype_sub/val`. -/
  | val {Δ : TypeCtx} {t₁ t₂ : CValType} (h : SubS Δ t₁ t₂) : SubS Δ (.val t₁) (.val t₂)
  /-- `Storagetype_sub/pack`. -/
  | pack {Δ : TypeCtx} {p : PackType} : SubS Δ (.pack p) (.pack p)
  /-- `Fieldtype_sub/const`. -/
  | fieldConst {Δ : TypeCtx} {z₁ z₂ : CStorageType} (h : SubS Δ z₁ z₂) :
      SubS Δ (.field .const z₁) (.field .const z₂)
  /-- `Fieldtype_sub/var`. -/
  | fieldVar {Δ : TypeCtx} {z₁ z₂ : CStorageType} (h₁ : SubS Δ z₁ z₂) (h₂ : SubS Δ z₂ z₁) :
      SubS Δ (.field .var z₁) (.field .var z₂)
  /-- `Comptype_sub/struct`. -/
  | struct {Δ : TypeCtx} {fs₁ extra fs₂ : Ty (.list .field)} (h : SubS Δ fs₁ fs₂) :
      SubS Δ (.struct (fs₁.app extra)) (.struct fs₂)
  /-- `Comptype_sub/array`. -/
  | array {Δ : TypeCtx} {f₁ f₂ : CFieldType} (h : SubS Δ f₁ f₂) :
      SubS Δ (.array f₁) (.array f₂)
  /-- `Comptype_sub/func`. -/
  | func {Δ : TypeCtx} {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)}
      (hp : SubS Δ ps₂ ps₁) (hr : SubS Δ rs₁ rs₂) : SubS Δ (.func ps₁ rs₁) (.func ps₂ rs₂)
  /-- `Deftype_sub/refl`. -/
  | defRefl {Δ : TypeCtx} {d₁ d₂ : DefType} (h : d₁.clos Δ.types = d₂.clos Δ.types) :
      SubS Δ d₁ d₂
  /-- `Deftype_sub/super`. -/
  | defSuper {Δ : TypeCtx} {d₁ d₂ : DefType} {fin : Bool} {sups : Ty (.list .use)}
      {ct : CCompType} {j : Nat} {u : CTypeUse}
      (h : unrolldt d₁ = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u)
      (hs : SubS Δ (.use u) (.use (.dt d₂))) : SubS Δ d₁ d₂
  /-- `Resulttype_sub`, pointwise: empty. -/
  | nil {Δ : TypeCtx} {k : TKind} : SubS Δ (.nil : Ty (.list k)) .nil
  /-- Pointwise: cons. -/
  | cons {Δ : TypeCtx} {k : TKind} {a b : Ty k} {l l' : Ty (.list k)}
      (h : SubS Δ a b) (hl : SubS Δ l l') : SubS Δ (.cons a l) (.cons b l')

end

/-! ## Elimination-side readings in `{}`

What a SpecTec derivation in `{}` is read back as needs less than the full transcription: the
subtyping argument uses a middle type of `Heaptype_sub/trans` only through its **coherence**
(`Coh`: every type reachable along declared supertypes keeps its kind). `SubE` is `SubS {}` with
that premise in place of `TyOkS {}`, and without the rules that cannot fire in `{}` (`typeidx-*`,
`rec-*`); `RefOkE` is `RefOkS` with `Reftype_ok {}` read as coherence and `Reftype_sub {}` as
`SubE`. -/

/-- **Coherence**: every defined type reachable from `d` along declared supertypes (in `{}`)
has `d`'s kind. -/
def Coh (d : DefType) : Prop :=
  ∀ e, ({} : TypeCtx).Reach d e → Validation.defKind e = Validation.defKind d

/-- Coherence of a heap type: of its defined type, if it is one. -/
def CohH : CHeapType → Prop
  | .use (.dt d) => Coh d
  | _ => True

/-- The heap type of a reference type. -/
def refHeap : CRefType → CHeapType
  | .ref _ h => h

/-- SpecTec's `Heaptype_sub`/`Reftype_sub`/`Deftype_sub` in `{}`, with `trans`'s middle read as
coherent. -/
inductive SubE : {k : TKind} → Ty k → Ty k → Prop where
  | heapRefl {h : CHeapType} : SubE h h
  | heapTrans {h₁ h' h₂ : CHeapType} (hok : CohH h') (h₁' : SubE h₁ h') (h'₂ : SubE h' h₂) :
      SubE h₁ h₂
  | eqAny : SubE (.abs .eq) (.abs .any)
  | i31Eq : SubE (.abs .i31) (.abs .eq)
  | structEq : SubE (.abs .struct) (.abs .eq)
  | arrayEq : SubE (.abs .array) (.abs .eq)
  | defStruct {d : DefType} {fs : Ty (.list .field)} (h : Expand d (.struct fs)) :
      SubE (.use (.dt d)) (.abs .struct)
  | defArray {d : DefType} {f : CFieldType} (h : Expand d (.array f)) :
      SubE (.use (.dt d)) (.abs .array)
  | defFunc {d : DefType} {ps rs : Ty (.list .val)} (h : Expand d (.func ps rs)) :
      SubE (.use (.dt d)) (.abs .func)
  | defDef {d₁ d₂ : DefType} (h : SubE d₁ d₂) : SubE (.use (.dt d₁)) (.use (.dt d₂))
  | none {h : CHeapType} (hs : SubE h (.abs .any)) (hb : h ≠ .bot) : SubE (.abs .none) h
  | nofunc {h : CHeapType} (hs : SubE h (.abs .func)) (hb : h ≠ .bot) : SubE (.abs .nofunc) h
  | noexn {h : CHeapType} (hs : SubE h (.abs .exn)) (hb : h ≠ .bot) : SubE (.abs .noexn) h
  | noextern {h : CHeapType} (hs : SubE h (.abs .extern)) (hb : h ≠ .bot) :
      SubE (.abs .noextern) h
  | bot {h : CHeapType} : SubE .bot h
  | refNonNull {h₁ h₂ : CHeapType} (h : SubE h₁ h₂) : SubE (.ref false h₁) (.ref false h₂)
  | refNull {n : Bool} {h₁ h₂ : CHeapType} (h : SubE h₁ h₂) : SubE (.ref n h₁) (.ref true h₂)
  | defRefl {d₁ d₂ : DefType} (h : d₁.clos [] = d₂.clos []) : SubE d₁ d₂
  | defSuper {d₁ d₂ : DefType} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType} {j : Nat}
      {u : CTypeUse} (h : unrolldt d₁ = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u)
      (hs : SubE (.use u) (.use (.dt d₂))) : SubE d₁ d₂

variable {H : Type}

/-- SpecTec's `Ref_ok`, read back: `RefOkS` with `Reftype_ok {}` read as coherence of the heap
type and `Reftype_sub {}` as `SubE`. -/
inductive RefOkE (s : Store H) : Ref → CRefType → Prop where
  | null : RefOkE s .null (.ref true .bot)
  | i31 (b : BitVec 31) : RefOkE s (.i31 b) (.ref false (.abs .i31))
  | struct {a : Nat} {si : StructInst} (h : s.structs[a]? = some si) :
      RefOkE s (.struct a) (.ref false (.defHeap si.type))
  | array {a : Nat} {ai : ArrayInst} (h : s.arrays[a]? = some ai) :
      RefOkE s (.array a) (.ref false (.defHeap ai.type))
  | func {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
      RefOkE s (.func a) (.ref false (.defHeap fi.type))
  | exn {a : Nat} {e : ExnInst} (h : s.exns[a]? = some e) :
      RefOkE s (.exn a) (.ref false (.abs .exn))
  | host (a : Nat) : RefOkE s (.host a) (.ref false (.abs .any))
  | extern {r : Ref} (h : RefOkE s r (.ref false (.abs .any))) (hn : r ≠ .null) :
      RefOkE s (.extern r) (.ref false (.abs .extern))
  | sub {r : Ref} {rt rt' : CRefType} (h : RefOkE s r rt') (hok : CohH (refHeap rt))
      (hs : SubE rt' rt) : RefOkE s r rt

/-- SpecTec's `Ref_ok` on Core references and types: Core's `RefOk`, with `Ref_ok/sub` reading
`Reftype_ok {}` and `Reftype_sub {}` as `TyOkS {}` and `SubS {}`. -/
inductive RefOkS (s : Store H) : Ref → CRefType → Prop where
  /-- `Ref_ok/null`. -/
  | null : RefOkS s .null (.ref true .bot)
  /-- `Ref_ok/i31`. -/
  | i31 (b : BitVec 31) : RefOkS s (.i31 b) (.ref false (.abs .i31))
  /-- `Ref_ok/struct`. -/
  | struct {a : Nat} {si : StructInst} (h : s.structs[a]? = some si) :
      RefOkS s (.struct a) (.ref false (.defHeap si.type))
  /-- `Ref_ok/array`. -/
  | array {a : Nat} {ai : ArrayInst} (h : s.arrays[a]? = some ai) :
      RefOkS s (.array a) (.ref false (.defHeap ai.type))
  /-- `Ref_ok/func`. -/
  | func {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
      RefOkS s (.func a) (.ref false (.defHeap fi.type))
  /-- `Ref_ok/exn`. -/
  | exn {a : Nat} {e : ExnInst} (h : s.exns[a]? = some e) :
      RefOkS s (.exn a) (.ref false (.abs .exn))
  /-- `Ref_ok/host`. -/
  | host (a : Nat) : RefOkS s (.host a) (.ref false (.abs .any))
  /-- `Ref_ok/extern`. -/
  | extern {r : Ref} (h : RefOkS s r (.ref false (.abs .any))) (hn : r ≠ .null) :
      RefOkS s (.extern r) (.ref false (.abs .extern))
  /-- `Ref_ok/sub`, with SpecTec's `Reftype_ok {}` and `Reftype_sub {}`. -/
  | sub {r : Ref} {rt rt' : CRefType} (h : RefOkS s r rt') (hok : TyOkS {} rt)
      (hs : SubS {} rt' rt) : RefOkS s r rt

/-! ## The interpreter half -/

open Silmaril.SpecTec.Sem

/-- **The interpreter half of `RefOkBV`** (open): SpecTec's `Ref_ok`, read by `DDerivesB`, is its
transcription `RefOkS` onto Core types, at the images of a Core-valid store with a typed image
and a Core-valid, closed, bounded reference type. This is a statement about the interpreter
only: `RefOkS` differs from Core's `RefOk` exactly where SpecTec's rules differ from Core's, and
the Core half (`refOkS_iff`, proved) closes that gap. -/
structure Agree (env : Env) : Prop where
  /-- On a Core-valid, typed store and a Core-valid, closed, bounded reference type. -/
  refOk : ∀ {H : Type} (hn : H → String) (s : Store H) (rt : CRefType),
    TypedV env storeT (storeV hn s) → StoreOk s → Round4.tyBnd rt = true → TyOk {} rt →
      ∀ (O : ElseI) (r : Ref), Round6.Reading.DDerivesB env O "Ref_ok" "%|-%:%" []
        (.tuple [storeV hn s, Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue r,
          CT.elemType rt]) ↔ RefOkS s r rt

/-- The value of the empty context `{}` (`Round6.Reading.ctx0V`). -/
def ctxEmptyV : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list []), ("MEMS", .list []),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list []), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list [])]

open Silmaril.SpecTec.Equiv.Validation (tyV) in
/-- **The type-judgment part of `Agree`** (open): SpecTec's `Reftype_ok {}` and `Reftype_sub {}`,
read by `DDerivesB`, against Core's judgments (introduction, at bounded Core-valid types) and
against their transcriptions `TyOkS {}`/`SubS {}` (elimination). No store is involved; `Agree`
follows from it for every `B` (`agree_of_agreeTy`), through the nine `Ref_ok` rules. -/
structure AgreeTy (env : Env) : Prop where
  /-- `Reftype_ok {}` holds at a bounded, Core-valid reference type. -/
  okIntro : ∀ (O : ElseI) (rt : CRefType), Round4.tyBnd rt = true → TyOk {} rt →
    Round6.Reading.DDerivesB env O "Reftype_ok" "%|-%:OK" [] (.tuple [ctxEmptyV, tyV rt])
  /-- `Reftype_sub {}` holds between bounded, Core-valid reference types in Core's `Sub {}`. -/
  subIntro : ∀ (O : ElseI) (p rt : CRefType), Round4.tyBnd p = true → Round4.tyBnd rt = true →
    TyOk {} p → TyOk {} rt → Sub {} p rt →
    Round6.Reading.DDerivesB env O "Reftype_sub" "%|-%<:%" [] (.tuple [ctxEmptyV, tyV p, tyV rt])
  /-- `Reftype_ok {}` at the image of a reference type makes its heap type coherent (as
  `TyOkS {}` does, `cohH_of_tyOkS`). -/
  okElim : ∀ (O : ElseI) (rt : CRefType),
    Round6.Reading.DDerivesB env O "Reftype_ok" "%|-%:OK" [] (.tuple [ctxEmptyV, tyV rt]) →
      CohH (refHeap rt)
  /-- `Reftype_sub {}` from the image of a reference type is `SubE`, to an image. -/
  subElim : ∀ (O : ElseI) (p : CRefType) (w : Value),
    Round6.Reading.DDerivesB env O "Reftype_sub" "%|-%<:%" [] (.tuple [ctxEmptyV, tyV p, w]) →
      ∃ rt, w = tyV rt ∧ SubE p rt

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
