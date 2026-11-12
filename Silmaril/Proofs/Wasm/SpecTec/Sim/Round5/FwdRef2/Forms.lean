module

public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Defs
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs

/-!
# Round 5, pass 3, track fwdref: the operator encodings are injective

The leaves of `instrToV`'s injectivity (`Round5.FwdRef2.instrToV_inj`): every encoder of an
instruction immediate that is not an `Encode` instance (operators, shapes, signedness, memory
arguments, lane indices, the memory SIMD schema values) is injective, and the numeric instruction
families have a head form (`instrToV (.intBinOp t op) = .case "BINOP" (.tuple [ntV t, ibinopV op])`
and so on), so that their injectivity is that of their operator encoders.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (ntV iunopV ibinopV itestopV irelopV)
open Silmaril.Wasm.SpecTec.Sim.Vec (fUnOpV fBinOpV)
open Silmaril.Wasm.SpecTec (node nat encodeUnsigned)

/-! ## Small encoders -/

theorem caseNilV_inj {a b : MixopS} (h : caseNilV a = caseNilV b) : a = b := by
  simpa [caseNilV] using h

theorem pctV_inj {a b : Nat} (h : pctV a = pctV b) : a = b := by
  simpa [pctV] using h

theorem equivSxV_inj : Function.Injective Equiv.sxV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [Equiv.sxV])

theorem sxV_inj : Function.Injective Sim.sxV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [Sim.sxV, caseNilV])

theorem vecSxV_inj : Function.Injective Vec.sxV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [Vec.sxV, caseNilV])

theorem halfV_inj : Function.Injective Vec.halfV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [Vec.halfV, caseNilV])

@[simp] theorem equivSxV_eq_iff {a b : Signedness} : Equiv.sxV a = Equiv.sxV b ↔ a = b :=
  equivSxV_inj.eq_iff
@[simp] theorem sxV_eq_iff {a b : Signedness} : Sim.sxV a = Sim.sxV b ↔ a = b := sxV_inj.eq_iff
@[simp] theorem vecSxV_eq_iff {a b : Signedness} : Vec.sxV a = Vec.sxV b ↔ a = b :=
  vecSxV_inj.eq_iff
@[simp] theorem halfV_eq_iff {a b : Half} : Vec.halfV a = Vec.halfV b ↔ a = b := halfV_inj.eq_iff
@[simp] theorem optMap_halfV_eq_iff {a b : Option Half} :
    a.map Vec.halfV = b.map Vec.halfV ↔ a = b := (Option.map_injective halfV_inj).eq_iff

theorem ntV_inj : Function.Injective ntV := by
  intro a b h
  cases a <;> cases b <;>
    first | rfl | exact absurd h (by simp [ntV, Encode.toValue_injective.eq_iff])

theorem numTypeV_inj : Function.Injective Vec.numTypeV := by
  intro a b h
  rcases a with a | a <;> cases a <;> rcases b with b | b <;> cases b <;>
    first | rfl | exact absurd h (by simp [Vec.numTypeV, caseNilV])

@[simp] theorem ntV_eq_iff {a b : IntType} : ntV a = ntV b ↔ a = b := ntV_inj.eq_iff
@[simp] theorem numTypeV_eq_iff {a b : NumType} : Vec.numTypeV a = Vec.numTypeV b ↔ a = b :=
  numTypeV_inj.eq_iff

/-- `ntV` is `numTypeV` at integer types. -/
theorem ntV_eq (t : IntType) : ntV t = Vec.numTypeV (.int t) := by cases t <;> rfl

theorem ntV_ne_float (t : IntType) (u : FloatType) : ntV t ≠ Vec.numTypeV (.float u) := by
  rw [ntV_eq]
  intro h
  cases numTypeV_inj h

/-! ## Scalar operators -/

theorem iunopV_inj : Function.Injective iunopV := by
  intro a b h
  rcases a with _ | _ | _ | a <;> rcases b with _ | _ | _ | b <;>
    (try cases a) <;> (try cases b) <;>
    first | rfl | exact absurd h (by simp [iunopV, PackSize.width])

theorem ibinopV_inj : Function.Injective ibinopV := by
  intro a b h
  cases a <;> cases b <;> simp [ibinopV] at h ⊢ <;> exact h

theorem itestopV_inj : Function.Injective itestopV := by
  intro a b _
  cases a
  cases b
  rfl

theorem irelopV_inj : Function.Injective irelopV := by
  intro a b h
  cases a <;> cases b <;> simp [irelopV] at h ⊢ <;> exact h

theorem fUnOpV_inj : Function.Injective fUnOpV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [fUnOpV, caseNilV])

theorem fBinOpV_inj : Function.Injective fBinOpV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [fBinOpV, caseNilV])

theorem vFloatRelOpV_inj : Function.Injective Vec.vFloatRelOpV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [Vec.vFloatRelOpV, caseNilV])

/-! ## Head forms of the numeric families -/

theorem iv_intBinOp (t : IntType) (op : IntBinOp) :
    instrToV (.intBinOp t op) = .case "BINOP" (.tuple [ntV t, ibinopV op]) := by
  cases t <;> cases op <;> (try rename_i s; cases s) <;> rfl

theorem iv_intRelOp (t : IntType) (op : IntRelOp) :
    instrToV (.intRelOp t op) = .case "RELOP" (.tuple [ntV t, irelopV op]) := by
  cases t <;> cases op <;> (try rename_i s; cases s) <;> rfl

theorem iv_intTestOp (t : IntType) (op : IntTestOp) :
    instrToV (.intTestOp t op) = .case "TESTOP" (.tuple [ntV t, itestopV op]) := by
  cases t <;> cases op <;> rfl

/-- An integer unary operator: valid ones have a head form, invalid ones are junk. -/
theorem iv_intUnOp (t : IntType) (op : IntUnOp) :
    instrToV (.intUnOp t op) =
      if op.valid t then .case "UNOP" (.tuple [ntV t, iunopV op]) else .tuple [] := by
  cases t <;> cases op <;> (try rename_i p; cases p) <;> rfl

theorem iv_floatUnOp (t : FloatType) (op : FloatUnOp) :
    instrToV (.floatUnOp t op) = .case "UNOP" (.tuple [Vec.numTypeV (.float t), fUnOpV op]) := by
  cases t <;> cases op <;> rfl

theorem iv_floatBinOp (t : FloatType) (op : FloatBinOp) :
    instrToV (.floatBinOp t op) =
      .case "BINOP" (.tuple [Vec.numTypeV (.float t), fBinOpV op]) := by
  cases t <;> cases op <;> rfl

theorem iv_floatRelOp (t : FloatType) (op : FloatRelOp) :
    instrToV (.floatRelOp t op) =
      .case "RELOP" (.tuple [Vec.numTypeV (.float t), Vec.vFloatRelOpV op]) := by
  cases t <;> cases op <;> rfl

/-! ## Conversions -/

theorem cvtOpV_eq (a b : ConvertOp) (hs : a.source = b.source) (ht : a.target = b.target)
    (h : Vec.cvtOpV a = Vec.cvtOpV b) : a = b := by
  cases a <;> cases b <;>
    simp_all [Vec.cvtOpV, ConvertOp.source, ConvertOp.target, caseNilV]

theorem convertInstrV_inj : Function.Injective Vec.convertInstrV := by
  intro a b h
  simp only [Vec.convertInstrV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
    and_true] at h
  exact cvtOpV_eq a b (numTypeV_inj h.2.1) (numTypeV_inj h.1) h.2.2

/-! ## Immediates of memory, aggregate and vector instructions -/

@[simp] theorem toValue_eq_iff {α : Type} [Encode α] {a b : α} :
    Encode.toValue a = Encode.toValue b ↔ a = b := Encode.toValue_injective.eq_iff

@[simp] theorem pctV_eq_iff {a b : Nat} : pctV a = pctV b ↔ a = b := ⟨pctV_inj, by rintro rfl; rfl⟩

@[simp] theorem map_toValue_eq_iff {α : Type} [Encode α] {a b : List α} :
    a.map Encode.toValue = b.map Encode.toValue ↔ a = b :=
  List.map_inj_right fun _ _ h => Encode.toValue_injective h

@[simp] theorem optMap_sxV_eq_iff {a b : Option Signedness} :
    a.map Sim.sxV = b.map Sim.sxV ↔ a = b := Option.map_injective sxV_inj |>.eq_iff

@[simp] theorem optMap_vecSxV_eq_iff {a b : Option Signedness} :
    a.map Vec.sxV = b.map Vec.sxV ↔ a = b := Option.map_injective vecSxV_inj |>.eq_iff

theorem memargV_inj : Function.Injective memargV := by
  intro a b h
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  simp only [memargV, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, pctV_eq_iff,
    true_and, and_true] at h
  simp only [MemArg.mk.injEq]
  exact ⟨Fin.ext h.1, Fin.ext h.2⟩

@[simp] theorem memargV_eq_iff {a b : MemArg} : memargV a = memargV b ↔ a = b :=
  memargV_inj.eq_iff

theorem szV_inj : Function.Injective szV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [szV, pctV, PackSize.width])

@[simp] theorem szV_eq_iff {a b : PackSize} : szV a = szV b ↔ a = b := szV_inj.eq_iff

@[simp] theorem optMap_load_eq_iff {a b : Option (PackSize × Signedness)} :
    a.map (fun q => Value.case "%_%" (.tuple [szV q.1, Sim.sxV q.2])) =
      b.map (fun q => Value.case "%_%" (.tuple [szV q.1, Sim.sxV q.2])) ↔ a = b := by
  refine (Option.map_injective ?_).eq_iff
  rintro ⟨p, s⟩ ⟨p', s'⟩ h
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, szV_eq_iff, sxV_eq_iff,
    true_and, and_true] at h
  rw [h.1, h.2]

@[simp] theorem optMap_store_eq_iff {a b : Option PackSize} :
    a.map (fun q => Value.case "%" (.tuple [szV q])) =
      b.map (fun q => Value.case "%" (.tuple [szV q])) ↔ a = b := by
  refine (Option.map_injective ?_).eq_iff
  intro p p' h
  simpa only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, szV_eq_iff, true_and,
    and_true] using h

theorem laneIdxV_inj : Function.Injective Vec.laneIdxV := by
  intro a b h
  exact Fin.ext (pctV_inj h)

@[simp] theorem laneIdxV_eq_iff {a b : LaneIdx} : Vec.laneIdxV a = Vec.laneIdxV b ↔ a = b :=
  laneIdxV_inj.eq_iff

@[simp] theorem map_laneIdxV_eq_iff {a b : List LaneIdx} :
    a.map Vec.laneIdxV = b.map Vec.laneIdxV ↔ a = b :=
  List.map_inj_right fun _ _ h => laneIdxV_inj h

theorem ishV_inj : Function.Injective Vec.ishV := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [Vec.ishV, Vec.intLaneV, caseNilV])

theorem fshV_inj : Function.Injective Vec.fshV := by
  intro a b h
  cases a <;> cases b <;>
    first | rfl | exact absurd h (by simp [Vec.fshV, Vec.floatLaneV, caseNilV])

theorem ishV_ne_fshV (a : IntShape) (b : FloatShape) : Vec.ishV a ≠ Vec.fshV b := by
  cases a <;> cases b <;> simp [Vec.ishV, Vec.fshV, Vec.intLaneV, Vec.floatLaneV, caseNilV]

theorem shapeV_inj : Function.Injective Vec.shapeV := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp only [Vec.shapeV] at h
  · rw [ishV_inj h]
  · exact absurd h (ishV_ne_fshV a b)
  · exact absurd h.symm (ishV_ne_fshV b a)
  · rw [fshV_inj h]

theorem ishapeV_inj : Function.Injective Vec.ishapeV := by
  intro a b h
  simp only [Vec.ishapeV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
    and_true] at h
  exact ishV_inj h

@[simp] theorem ishV_eq_iff {a b : IntShape} : Vec.ishV a = Vec.ishV b ↔ a = b := ishV_inj.eq_iff
@[simp] theorem fshV_eq_iff {a b : FloatShape} : Vec.fshV a = Vec.fshV b ↔ a = b :=
  fshV_inj.eq_iff
@[simp] theorem shapeV_eq_iff {a b : Shape} : Vec.shapeV a = Vec.shapeV b ↔ a = b :=
  shapeV_inj.eq_iff
@[simp] theorem ishapeV_eq_iff {a b : IntShape} : Vec.ishapeV a = Vec.ishapeV b ↔ a = b :=
  ishapeV_inj.eq_iff

/-- Injectivity of a finite operator encoding, by cases on both sides. -/
macro "fin_inj" : tactic => `(tactic| (
  intro a b h
  cases a <;> cases b <;>
    simp_all [Vec.vvunopV, Vec.vvbinopV, Vec.vvternopV, Vec.vvtestopV, Vec.vIntUnOpV,
      Vec.vFloatUnOpV, Vec.vIntBinOpV, Vec.vFloatBinOpV, Vec.vIntTernOpV, Vec.vFloatTernOpV,
      Vec.vIntRelOpV, Vec.vFloatRelOpV, Vec.vShiftOpV, Vec.vSwizzleOpV, Vec.vExtUnOpV,
      Vec.vExtBinOpV, Vec.vExtTernOpV, Vec.vConvertOpV, caseNilV] <;>
    first | rfl | (split at h <;> split at h <;> simp_all) | skip))

theorem vvunopV_inj : Function.Injective Vec.vvunopV := by fin_inj
theorem vvbinopV_inj : Function.Injective Vec.vvbinopV := by fin_inj
theorem vvternopV_inj : Function.Injective Vec.vvternopV := by fin_inj
theorem vvtestopV_inj : Function.Injective Vec.vvtestopV := by fin_inj
theorem vIntUnOpV_inj : Function.Injective Vec.vIntUnOpV := by fin_inj
theorem vFloatUnOpV_inj : Function.Injective Vec.vFloatUnOpV := by fin_inj
theorem vIntBinOpV_inj : Function.Injective Vec.vIntBinOpV := by fin_inj
theorem vFloatBinOpV_inj : Function.Injective Vec.vFloatBinOpV := by fin_inj
theorem vIntTernOpV_inj : Function.Injective Vec.vIntTernOpV := by fin_inj
theorem vFloatTernOpV_inj : Function.Injective Vec.vFloatTernOpV := by fin_inj
theorem vIntRelOpV_inj : Function.Injective Vec.vIntRelOpV := by fin_inj
theorem vShiftOpV_inj : Function.Injective Vec.vShiftOpV := by fin_inj
theorem vSwizzleOpV_inj : Function.Injective Vec.vSwizzleOpV := by fin_inj
theorem vExtUnOpV_inj : Function.Injective Vec.vExtUnOpV := by fin_inj
theorem vExtBinOpV_inj : Function.Injective Vec.vExtBinOpV := by fin_inj
theorem vExtTernOpV_inj : Function.Injective Vec.vExtTernOpV := by fin_inj
theorem vConvertOpV_inj : Function.Injective Vec.vConvertOpV := by fin_inj

@[simp] theorem vvunopV_eq_iff {a b} : Vec.vvunopV a = Vec.vvunopV b ↔ a = b := vvunopV_inj.eq_iff
@[simp] theorem vvbinopV_eq_iff {a b} : Vec.vvbinopV a = Vec.vvbinopV b ↔ a = b :=
  vvbinopV_inj.eq_iff
@[simp] theorem vvternopV_eq_iff {a b} : Vec.vvternopV a = Vec.vvternopV b ↔ a = b :=
  vvternopV_inj.eq_iff
@[simp] theorem vvtestopV_eq_iff {a b} : Vec.vvtestopV a = Vec.vvtestopV b ↔ a = b :=
  vvtestopV_inj.eq_iff
@[simp] theorem vIntUnOpV_eq_iff {a b} : Vec.vIntUnOpV a = Vec.vIntUnOpV b ↔ a = b :=
  vIntUnOpV_inj.eq_iff
@[simp] theorem vFloatUnOpV_eq_iff {a b} : Vec.vFloatUnOpV a = Vec.vFloatUnOpV b ↔ a = b :=
  vFloatUnOpV_inj.eq_iff
@[simp] theorem vIntBinOpV_eq_iff {a b} : Vec.vIntBinOpV a = Vec.vIntBinOpV b ↔ a = b :=
  vIntBinOpV_inj.eq_iff
@[simp] theorem vFloatBinOpV_eq_iff {a b} : Vec.vFloatBinOpV a = Vec.vFloatBinOpV b ↔ a = b :=
  vFloatBinOpV_inj.eq_iff
@[simp] theorem vIntTernOpV_eq_iff {a b} : Vec.vIntTernOpV a = Vec.vIntTernOpV b ↔ a = b :=
  vIntTernOpV_inj.eq_iff
@[simp] theorem vFloatTernOpV_eq_iff {a b} : Vec.vFloatTernOpV a = Vec.vFloatTernOpV b ↔ a = b :=
  vFloatTernOpV_inj.eq_iff
@[simp] theorem vIntRelOpV_eq_iff {a b} : Vec.vIntRelOpV a = Vec.vIntRelOpV b ↔ a = b :=
  vIntRelOpV_inj.eq_iff
@[simp] theorem vFloatRelOpV_eq_iff {a b} : Vec.vFloatRelOpV a = Vec.vFloatRelOpV b ↔ a = b :=
  vFloatRelOpV_inj.eq_iff
@[simp] theorem vShiftOpV_eq_iff {a b} : Vec.vShiftOpV a = Vec.vShiftOpV b ↔ a = b :=
  vShiftOpV_inj.eq_iff
@[simp] theorem vSwizzleOpV_eq_iff {a b} : Vec.vSwizzleOpV a = Vec.vSwizzleOpV b ↔ a = b :=
  vSwizzleOpV_inj.eq_iff
@[simp] theorem vExtUnOpV_eq_iff {a b} : Vec.vExtUnOpV a = Vec.vExtUnOpV b ↔ a = b :=
  vExtUnOpV_inj.eq_iff
@[simp] theorem vExtBinOpV_eq_iff {a b} : Vec.vExtBinOpV a = Vec.vExtBinOpV b ↔ a = b :=
  vExtBinOpV_inj.eq_iff
@[simp] theorem vExtTernOpV_eq_iff {a b} : Vec.vExtTernOpV a = Vec.vExtTernOpV b ↔ a = b :=
  vExtTernOpV_inj.eq_iff
@[simp] theorem vConvertOpV_eq_iff {a b} : Vec.vConvertOpV a = Vec.vConvertOpV b ↔ a = b :=
  vConvertOpV_inj.eq_iff

/-- `select`, with or without its annotation. -/
theorem iv_select (o : Option (List ValType)) :
    instrToV (.select o) =
      .case "SELECT" (.opt (o.map fun ts => .list (ts.map Encode.toValue))) := by
  cases o <;> rfl

/-! ## The memory SIMD instructions (schema encoding) -/

/-- Evaluate `schemaV` on the schema values of the memory SIMD immediates. -/
macro "sch" : tactic => `(tactic| simp [schemaV, encodeUnsigned, node, nat,
    Silmaril.Formats.TExpr.ofList, SpecTec.encodeMemArg, SpecTec.encodeVecType,
    SpecTec.encodePackSize, SpecTec.encodeVecLoadOp, SpecTec.encodeSignedness, Fin.ext_iff,
    Idx.toNat, PackSize.width] at *)

/-- Unfold a memory SIMD image to its components. -/
macro "unf_sch" : tactic => `(tactic| simp only [instrToV, schemaInstrV,
    Silmaril.Wasm.SpecTec.encodeInstruction, List.map, SpecTec.field, Value.case.injEq,
    Value.tuple.injEq, List.cons.injEq, true_and, and_true] at *)

theorem schVlop_inj {a b : VecLoadOp}
    (h : schemaV (SpecTec.encodeVecLoadOp a) = schemaV (SpecTec.encodeVecLoadOp b)) : a = b := by
  cases a <;> cases b <;> (try rename_i x y; cases x <;> cases y) <;> sch

theorem schIdx_inj {k : IndexKind} {a b : Idx k}
    (h : schemaV (encodeUnsigned a.toNat) = schemaV (encodeUnsigned b.toNat)) : a = b := by
  sch
  obtain ⟨⟨a, _⟩⟩ := a
  obtain ⟨⟨b, _⟩⟩ := b
  simp_all

theorem schMemArg_inj {a b : MemArg}
    (h : schemaV (SpecTec.encodeMemArg a) = schemaV (SpecTec.encodeMemArg b)) : a = b := by
  sch
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  simp_all [Fin.ext_iff]

theorem schPackSize_inj {a b : PackSize}
    (h : schemaV (SpecTec.encodePackSize a) = schemaV (SpecTec.encodePackSize b)) : a = b := by
  cases a <;> cases b <;> sch

theorem schLane_inj {a b : LaneIdx}
    (h : schemaV (encodeUnsigned a.val) = schemaV (encodeUnsigned b.val)) : a = b := by
  apply Fin.ext
  sch
  omega

theorem vecLoad_inj {p q : VecLoadOp × MemIdx × MemArg}
    (h : instrToV (.vecLoad q.1 q.2.1 q.2.2) = instrToV (.vecLoad p.1 p.2.1 p.2.2)) : q = p := by
  obtain ⟨o, m, a⟩ := p
  obtain ⟨o', m', a'⟩ := q
  unf_sch
  rw [schVlop_inj h.1, schIdx_inj h.2.1, schMemArg_inj h.2.2]

theorem vecLoadLane_inj {p q : PackSize × MemIdx × MemArg × LaneIdx}
    (h : instrToV (.vecLoadLane q.1 q.2.1 q.2.2.1 q.2.2.2) =
      instrToV (.vecLoadLane p.1 p.2.1 p.2.2.1 p.2.2.2)) : q = p := by
  obtain ⟨o, m, a, l⟩ := p
  obtain ⟨o', m', a', l'⟩ := q
  unf_sch
  rw [schPackSize_inj h.1, schIdx_inj h.2.1, schMemArg_inj h.2.2.1, schLane_inj h.2.2.2]

theorem vecStore_inj {p q : MemIdx × MemArg}
    (h : instrToV (.vecStore q.1 q.2) = instrToV (.vecStore p.1 p.2)) : q = p := by
  obtain ⟨m, a⟩ := p
  obtain ⟨m', a'⟩ := q
  unf_sch
  rw [schIdx_inj h.1, schMemArg_inj h.2]

theorem vecStoreLane_inj {p q : PackSize × MemIdx × MemArg × LaneIdx}
    (h : instrToV (.vecStoreLane q.1 q.2.1 q.2.2.1 q.2.2.2) =
      instrToV (.vecStoreLane p.1 p.2.1 p.2.2.1 p.2.2.2)) : q = p := by
  obtain ⟨o, m, a, l⟩ := p
  obtain ⟨o', m', a', l'⟩ := q
  unf_sch
  rw [schPackSize_inj h.1, schIdx_inj h.2.1, schMemArg_inj h.2.2.1, schLane_inj h.2.2.2]

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2
