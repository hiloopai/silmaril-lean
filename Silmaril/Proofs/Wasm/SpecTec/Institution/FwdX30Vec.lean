module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs
public import Silmaril.Wasm.SpecTec.Institution.Cover.Thms
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Convert.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms

/-!
# The forward direction at wasm-3.0, extended: the vector rules of `Step_pure`

At the concrete primitives `Round4Int.BI`, every Core `VectorStep` from `AdminsSel` code (code
without `FloatMissel` instructions, part 's domain) is a `Step_pure` fact of the
declarative reading, at typed code.

The `spureV_*` lemmas are the bodies of the convert forward leaves
(`Round5.Convert.fwdN_vec*`, themselves copies of family V's), stopped before the lift with
`Step/pure`; `spureV_vecConvertSel` is `Cover.fwd_vecConvertSel` before the lift: on
`AdminsSel` code the only `vcvtop` operators are the `extend` ones, where Core's relation is a
function, so the step is exact.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules vconstV)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (constV i32V caseNilV pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Vec
open Silmaril.Wasm.SpecTec.Sim.Round5.Convert (VecAgreeNC)

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}

section Leaves

set_option linter.unusedSectionVars false

variable (T : TypingFacts env hn) (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env)
  (A : VecAgreeNC env P)
include T V Ty A

/-- `fwdN_vecUnOp`, before the lift. -/
theorem spureV_vecUnOp (op : VecUnOp) (a : V128)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecUnOp op)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecUnOp op)]))
      (adminsToV ([vconst (vvunop op a)])) :=
  (spure_vvunop V.vvunop (Ty.vec a) (Ty.vvunop op) (Ty.vec _) (A.vvunop op a)
    List.mem_cons_self)

/-- `fwdN_vecBinOp`, before the lift. -/
theorem spureV_vecBinOp (op : VecBinOp) (a b : V128)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecBinOp op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecBinOp op)]))
      (adminsToV ([vconst (vvbinop op a b)])) :=
  (spure_vvbinop V.vvbinop (Ty.vec a) (Ty.vec b) (Ty.vvbinop op) (Ty.vec _)
    (A.vvbinop op a b) List.mem_cons_self)

/-- `fwdN_vecTernOp`, before the lift. -/
theorem spureV_vecTernOp (op : VecTernOp) (a b c : V128)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecTernOp op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecTernOp op)]))
      (adminsToV ([vconst (vvternop op a b c)])) :=
  (spure_vvternop V.vvternop (Ty.vec a) (Ty.vec b) (Ty.vec c) (Ty.vvternop op)
    (Ty.vec _) (A.vvternop op a b c) List.mem_cons_self)

/-- `fwdN_vecTestOp`, before the lift. -/
theorem spureV_vecTestOp (op : VecTestOp) (a : V128)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecTestOp op)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecTestOp op)]))
      (adminsToV ([constI32 (vvtestop op a)])) := by
  cases op
  obtain ⟨n, hn', ha⟩ := A.vvtestop .anyTrue a
  exact (spure_vvtestop V.vvtestop (Ty.vec a) (Ty.i32 _) hn' ha)

/-- `fwdN_vecIntUnOp`, before the lift. -/
theorem spureV_vecIntUnOp (sh : IntShape) (op : VecIntUnOp) (a : V128)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecIntUnOp sh op)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecIntUnOp sh op)]))
      (adminsToV ([vconst (vecIntUnOp sh op a)])) := by
  have hi : InstrTyped env (.vecIntUnOp sh op) := typed_last2 T (hcode)
  exact (spure_vunopVal V.vunopVal (Ty.vec a) (Ty.shape (.int sh))
    (Ty.intUnOp sh op hi) (Ty.vec _) (A.intUnOp sh op a) List.mem_cons_self)

/-- `fwdN_vecFloatUnOp`, before the lift. -/
theorem spureV_vecFloatUnOp {sh : FloatShape} {op : FloatUnOp} {a r : V128}
    (h : VecFloatUnOpRel P sh op a r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecFloatUnOp sh op)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecFloatUnOp sh op)]))
      (adminsToV ([vconst r])) := by
  have hi : InstrTyped env (.vecFloatUnOp sh op) := typed_last2 T (hcode)
  obtain ⟨L, ha, hL⟩ := A.floatUnOp sh op a
  have hm : vecV r ∈ L := (hL _).2 ⟨r, h, rfl⟩
  exact (spure_vunopVal V.vunopVal (Ty.vec a) (Ty.shape (.float sh))
    (Ty.floatUnOp sh op hi) (Ty.vec r) ha hm)

/-- `fwdN_vecFloatUnOpTrap`, before the lift. -/
theorem spureV_vecFloatUnOpTrap {sh : FloatShape} {op : FloatUnOp} {a : V128}
    (h : ∀ r, ¬ VecFloatUnOpRel P sh op a r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecFloatUnOp sh op)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecFloatUnOp sh op)]))
      (adminsToV ([.trap])) := by
  have hi : InstrTyped env (.vecFloatUnOp sh op) := typed_last2 T (hcode)
  obtain ⟨L, ha, hL⟩ := A.floatUnOp sh op a
  have hnil : L = [] := list_eq_nil_of_iff hL fun c ⟨r, hr', _⟩ => h r hr'
  have ha' : Applies env "vunop_" [.val (fshV sh), .val (vFloatUnOpV op), .val (vecV a)]
      (.list []) := hnil ▸ ha
  exact (spure_vunopTrap V.vunopTrap (Ty.vec a) (Ty.shape (.float sh))
    (Ty.floatUnOp sh op hi) ha')

/-- `fwdN_vecIntBinOp`, before the lift. -/
theorem spureV_vecIntBinOp (sh : IntShape) (op : VecIntBinOp) (a b : V128)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecIntBinOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecIntBinOp sh op)]))
      (adminsToV ([vconst (vecIntBinOp P sh op a b)])) := by
  have hi : InstrTyped env (.vecIntBinOp sh op) := typed_last3 T (hcode)
  exact (spure_vbinopVal V.vbinopVal (Ty.vec a) (Ty.vec b) (Ty.shape (.int sh))
    (Ty.intBinOp sh op hi) (Ty.vec _) (A.intBinOp sh op a b) List.mem_cons_self)

/-- `fwdN_vecFloatBinOp`, before the lift. -/
theorem spureV_vecFloatBinOp {sh : FloatShape} {op : VecFloatBinOp} {a b r : V128}
    (h : VecFloatBinOpRel P sh op a b r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecFloatBinOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecFloatBinOp sh op)]))
      (adminsToV ([vconst r])) := by
  have hi : InstrTyped env (.vecFloatBinOp sh op) := typed_last3 T (hcode)
  obtain ⟨L, ha, hL⟩ := A.floatBinOp sh op a b
  have hm : vecV r ∈ L := (hL _).2 ⟨r, h, rfl⟩
  exact (spure_vbinopVal V.vbinopVal (Ty.vec a) (Ty.vec b)
    (Ty.shape (.float sh)) (Ty.floatBinOp sh op hi) (Ty.vec r) ha hm)

/-- `fwdN_vecFloatBinOpTrap`, before the lift. -/
theorem spureV_vecFloatBinOpTrap {sh : FloatShape} {op : VecFloatBinOp} {a b : V128}
    (h : ∀ r, ¬ VecFloatBinOpRel P sh op a b r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecFloatBinOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecFloatBinOp sh op)]))
      (adminsToV ([.trap])) := by
  have hi : InstrTyped env (.vecFloatBinOp sh op) := typed_last3 T (hcode)
  obtain ⟨L, ha, hL⟩ := A.floatBinOp sh op a b
  have hnil : L = [] := list_eq_nil_of_iff hL fun c ⟨r, hr', _⟩ => h r hr'
  have ha' : Applies env "vbinop_"
      [.val (fshV sh), .val (vFloatBinOpV op), .val (vecV a), .val (vecV b)] (.list []) :=
    hnil ▸ ha
  exact (spure_vbinopTrap V.vbinopTrap (Ty.vec a) (Ty.vec b)
    (Ty.shape (.float sh)) (Ty.floatBinOp sh op hi) ha')

/-- `fwdN_vecIntTernOp`, before the lift. -/
theorem spureV_vecIntTernOp (sh : IntShape) (op : VecIntTernOp) (a b c : V128)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecIntTernOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecIntTernOp sh op)]))
      (adminsToV ([vconst (vecIntTernOp P sh op a b c)])) := by
  have hi : InstrTyped env (.vecIntTernOp sh op) := typed_last4 T (hcode)
  exact (spure_vternopVal V.vternopVal (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.shape (.int sh)) (Ty.intTernOp sh op hi) (Ty.vec _) (A.intTernOp sh op a b c)
    List.mem_cons_self)

/-- `fwdN_vecFloatTernOp`, before the lift. -/
theorem spureV_vecFloatTernOp {sh : FloatShape} {op : VecFloatTernOp} {a b c r : V128}
    (h : VecFloatTernOpRel P sh op a b c r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)]))
      (adminsToV ([vconst r])) := by
  have hi : InstrTyped env (.vecFloatTernOp sh op) := typed_last4 T (hcode)
  obtain ⟨L, ha, hL⟩ := A.floatTernOp sh op a b c
  have hm : vecV r ∈ L := (hL _).2 ⟨r, h, rfl⟩
  exact (spure_vternopVal V.vternopVal (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.shape (.float sh)) (Ty.floatTernOp sh op hi) (Ty.vec r) ha hm)

/-- `fwdN_vecFloatTernOpTrap`, before the lift. -/
theorem spureV_vecFloatTernOpTrap {sh : FloatShape} {op : VecFloatTernOp} {a b c : V128}
    (h : ∀ r, ¬ VecFloatTernOpRel P sh op a b c r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)]))
      (adminsToV ([.trap])) := by
  have hi : InstrTyped env (.vecFloatTernOp sh op) := typed_last4 T (hcode)
  obtain ⟨L, ha, hL⟩ := A.floatTernOp sh op a b c
  have hnil : L = [] := list_eq_nil_of_iff hL fun d ⟨r, hr', _⟩ => h r hr'
  have ha' : Applies env "vternop_" [.val (fshV sh), .val (vFloatTernOpV op), .val (vecV a),
      .val (vecV b), .val (vecV c)] (.list []) := hnil ▸ ha
  exact (spure_vternopTrap V.vternopTrap (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.shape (.float sh)) (Ty.floatTernOp sh op hi) ha')

/-- `fwdN_vecIntRelOp`, before the lift. -/
theorem spureV_vecIntRelOp (sh : IntShape) (op : IntRelOp) (a b : V128)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecIntRelOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecIntRelOp sh op)]))
      (adminsToV ([vconst (vecIntRelOp sh op a b)])) := by
  have hi : InstrTyped env (.vecIntRelOp sh op) := typed_last3 T (hcode)
  exact (spure_vrelop V.vrelop (Ty.vec a) (Ty.vec b) (Ty.shape (.int sh))
    (Ty.intRelOp sh op hi) (Ty.vec _) (A.intRelOp sh op a b))

/-- `fwdN_vecFloatRelOp`, before the lift. -/
theorem spureV_vecFloatRelOp (sh : FloatShape) (op : FloatRelOp) (a b : V128)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecFloatRelOp sh op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecFloatRelOp sh op)]))
      (adminsToV ([vconst (vecFloatRelOp sh op a b)])) := by
  have hi : InstrTyped env (.vecFloatRelOp sh op) := typed_last3 T (hcode)
  exact (spure_vrelop V.vrelop (Ty.vec a) (Ty.vec b) (Ty.shape (.float sh))
    (Ty.floatRelOp sh op hi) (Ty.vec _) (A.floatRelOp sh op a b))

/-- `fwdN_vecShiftOp`, before the lift. -/
theorem spureV_vecShiftOp (sh : IntShape) (op : VecShiftOp) (a : V128) (n : BitVec 32)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, constI32 n, .plain (.vecShiftOp sh op)])))) :
    SPure env (adminsToV ([vconst a, constI32 n, .plain (.vecShiftOp sh op)]))
      (adminsToV ([vconst (vecShiftOp sh op a n)])) := by
  have hi : InstrTyped env (.vecShiftOp sh op) := typed_last3 T (hcode)
  exact (spure_vshiftop V.vshiftop (Ty.vec a) (Ty.i32 n) (Ty.ishape sh)
    (Ty.shiftOp sh op hi) (Ty.vec _) (A.shiftOp sh op a n))

/-- `fwdN_vecBitmask`, before the lift. -/
theorem spureV_vecBitmask (sh : IntShape) (a : V128)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecBitmask sh)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecBitmask sh)]))
      (adminsToV ([constI32 (vecBitmask sh a)])) :=
  (spure_vbitmask V.vbitmask (Ty.vec a) (Ty.ishape sh) (Ty.i32 _)
    (A.bitmask sh a))

/-- `fwdN_vecSwizzle`, before the lift. -/
theorem spureV_vecSwizzle (a b : V128)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecSwizzle .swizzle)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecSwizzle .swizzle)]))
      (adminsToV ([vconst (vecSwizzle a b)])) := by
  have hi : InstrTyped env (.vecSwizzle .swizzle) := typed_last3 T (hcode)
  exact (spure_vswizzlop V.vswizzlop (Ty.vec a) (Ty.vec b) Ty.bshape
    (Ty.swizzle .swizzle hi) (Ty.vec _) (A.swizzle a b))

/-- `fwdN_vecRelaxedSwizzle`, before the lift. -/
theorem spureV_vecRelaxedSwizzle (a b : V128)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecSwizzle .relaxedSwizzle)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecSwizzle .relaxedSwizzle)]))
      (adminsToV ([vconst (vecRelaxedSwizzle P a b)])) := by
  have hi : InstrTyped env (.vecSwizzle .relaxedSwizzle) := typed_last3 T (hcode)
  exact (spure_vswizzlop V.vswizzlop (Ty.vec a) (Ty.vec b) Ty.bshape
    (Ty.swizzle .relaxedSwizzle hi) (Ty.vec _) (A.relaxedSwizzle a b))

/-- `fwdN_vecShuffle`, before the lift. -/
theorem spureV_vecShuffle (idx : List LaneIdx) (a b : V128) (hidx : ∀ j ∈ idx, j.val < 32)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecShuffle idx)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecShuffle idx)]))
      (adminsToV ([vconst (vecShuffle idx a b)])) := by
  have hi : InstrTyped env (.vecShuffle idx) := typed_last3 T (hcode)
  exact (spure_vshuffle V.vshuffle (Ty.vec a) (Ty.vec b) Ty.bshape
    (Ty.shuffle idx hi) (Ty.vec _) ((A.shuffle idx a b _).2 ⟨hidx, rfl⟩))

/-- `fwdN_vecExtUnOp`, before the lift. -/
theorem spureV_vecExtUnOp {sh₁ sh₂ : IntShape} {op : VecExtUnOp} {a r : V128}
    (h : VecExtUnOpRel sh₁ sh₂ op a r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecExtUnOp sh₁ sh₂ op)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecExtUnOp sh₁ sh₂ op)]))
      (adminsToV ([vconst r])) := by
  have hi : InstrTyped env (.vecExtUnOp sh₁ sh₂ op) := typed_last2 T (hcode)
  exact (spure_vextunop V.vextunop (Ty.vec a) (Ty.ishape sh₂) (Ty.ishape sh₁)
    (Ty.extUnOp sh₁ sh₂ op hi) (Ty.vec r) ((A.extUnOp sh₁ sh₂ op a _).2 ⟨r, h, rfl⟩))

/-- `fwdN_vecExtBinOp`, before the lift. -/
theorem spureV_vecExtBinOp {sh₁ sh₂ : IntShape} {op : VecExtBinOp} {a b r : V128}
    (h : VecExtBinOpRel P sh₁ sh₂ op a b r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecExtBinOp sh₁ sh₂ op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecExtBinOp sh₁ sh₂ op)]))
      (adminsToV ([vconst r])) := by
  have hi : InstrTyped env (.vecExtBinOp sh₁ sh₂ op) := typed_last3 T (hcode)
  exact (spure_vextbinop V.vextbinop (Ty.vec a) (Ty.vec b) (Ty.ishape sh₂)
    (Ty.ishape sh₁) (Ty.extBinOp sh₁ sh₂ op hi) (Ty.vec r)
    ((A.extBinOp sh₁ sh₂ op a b _).2 ⟨r, h, rfl⟩))

/-- `fwdN_vecExtTernOp`, before the lift. -/
theorem spureV_vecExtTernOp {sh₁ sh₂ : IntShape} {op : VecExtTernOp} {a b c r : V128}
    (h : VecExtTernOpRel P sh₁ sh₂ op a b c r)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecExtTernOp sh₁ sh₂ op)])))) :
    SPure env (adminsToV ([vconst a, vconst b, vconst c, .plain (.vecExtTernOp sh₁ sh₂ op)]))
      (adminsToV ([vconst r])) := by
  have hi : InstrTyped env (.vecExtTernOp sh₁ sh₂ op) := typed_last4 T (hcode)
  exact (spure_vextternop V.vextternop (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.ishape sh₂) (Ty.ishape sh₁) (Ty.extTernOp sh₁ sh₂ op hi) (Ty.vec r)
    ((A.extTernOp sh₁ sh₂ op a b c _).2 ⟨r, h, rfl⟩))

/-- `fwdN_vecNarrow`, before the lift. -/
theorem spureV_vecNarrow {sh₁ sh₂ : IntShape} {sx : Signedness} {a b r : V128}
    (h : VecNarrowRel sh₁ sh₂ sx a b r)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, vconst b, .plain (.vecNarrow sh₁ sh₂ sx)])))) :
    SPure env (adminsToV ([vconst a, vconst b, .plain (.vecNarrow sh₁ sh₂ sx)]))
      (adminsToV ([vconst r])) :=
  (spure_vnarrow V.vnarrow (Ty.vec a) (Ty.vec b) (Ty.ishape sh₂)
    (Ty.ishape sh₁) (Ty.sx sx) (Ty.vec r) ((A.narrow sh₁ sh₂ sx a b _).2 ⟨r, h, rfl⟩))


/-- `fwdN_vecReplaceLane`, before the lift. -/
theorem spureV_vecReplaceLane (sh : Shape) (i : LaneIdx) (a : V128) (x : BitVec sh.unpacked.width)
    (hi : i.val < sh.lanes)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin,
      .plain (.vecReplaceLane sh i)])))) :
    SPure env (adminsToV ([vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin,
      .plain (.vecReplaceLane sh i)]))
      (adminsToV ([vconst (vecReplaceLane sh i.val a x)])) := by
  obtain ⟨ls, l, u, hu, hl, hp, hs, hinv⟩ := A.replaceLane sh a i.val x hi
  have hl' : Applies env "lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes])),
      .val (vecV a)] (.list ls) := shapeV_eq sh ▸ hl
  have hinv' : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh,
      pctV sh.lanes])), .val u] (vecV (vecReplaceLane sh i.val a x)) := shapeV_eq sh ▸ hinv
  have hsp : SPure env [vconstV (vecV a), constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
      .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]),
        pctV i.val])] [vconstV (vecV (vecReplaceLane sh i.val a x))] :=
    spure_vreplaceLane V.vreplaceLane (Ty.vec a) (Ty.lnn sh) (Ty.numLunpack sh x) (Ty.dim sh)
      (Ty.laneidx i) (Ty.vec _) hu hl' hp hs hinv'
  have e₁ : adminsToV [vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin,
      .plain (.vecReplaceLane sh i)] =
      [vconstV (vecV a), constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
        .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]),
          pctV i.val])] := by
    simp only [adminsToV, adminToV_valNum]
    rw [← shapeV_eq]
    rfl
  exact (e₁ ▸ hsp)

/-- `fwdN_vecSplat`, before the lift. -/
theorem spureV_vecSplat (sh : Shape) (x : BitVec sh.unpacked.width)
    (_hcode : TypedV env instrsT (.list (adminsToV ([(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)])))) :
    SPure env (adminsToV ([(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)]))
      (adminsToV ([vconst (vecSplat sh x)])) := by
  obtain ⟨l, hu, hp, hinv⟩ := A.splat sh x
  have hinv' : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh,
      pctV sh.lanes])), .val (.list (List.replicate sh.lanes l))] (vecV (vecSplat sh x)) :=
    shapeV_eq sh ▸ hinv
  have hsp : SPure env [constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
      .case "VSPLAT" (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]))]
      [vconstV (vecV (vecSplat sh x))] :=
    spure_vsplat V.vsplat (Ty.lnn sh) (Ty.numLunpack sh x) (Ty.dim sh) (Ty.vec _) hu hp hinv'
  have e₁ : adminsToV [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)] =
      [constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
        .case "VSPLAT" (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]))] := by
    simp only [adminsToV, adminToV_valNum]
    rw [← shapeV_eq]
    rfl
  exact (e₁ ▸ hsp)

/-- `fwdN_vecAllTrue`, before the lift. -/
theorem spureV_vecAllTrue (sh : IntShape) (a : V128)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecAllTrue sh)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecAllTrue sh)]))
      (adminsToV ([constI32 (vecAllTrue sh a)])) := by
  obtain ⟨ls, jsz, bs, hl, hjs, hz, hp⟩ := A.allTrue sh a
  exact (spure_vtestop V.vtestop (Ty.vec a) (Ty.jnn sh) (Ty.dim (.int sh))
    (Ty.i32 _) (Ty.lanes sh a ls hl) hl hjs hz hp)


/-- `vcvtop` at the concrete primitives (`Round5.Convert.fwdN_vecConvertR`, before the
lift). -/
theorem spureV_vecConvertR {sh₁ sh₂ : Shape} {op : VecConvertOp} {a r : V128}
    (ha : Applies env "vcvtop__" [.val (Vec.shapeV sh₁), .val (Vec.shapeV sh₂),
      .val (Vec.vConvertOpV op), .val (Vec.vecV a)] (Vec.vecV r))
    (hcode : TypedV env instrsT
      (.list (adminsToV [vconst a, .plain (.vecConvert sh₁ sh₂ op)]))) :
    SPure env (adminsToV [vconst a, .plain (.vecConvert sh₁ sh₂ op)]) (adminsToV [vconst r]) :=
  have hi : InstrTyped env (.vecConvert sh₁ sh₂ op) := typed_last2 T hcode
  spure_vcvtop V.vcvtop (Ty.vec a) (Ty.shape sh₂) (Ty.shape sh₁) (Ty.convert sh₁ sh₂ op hi)
    (Ty.vec r) ha

end Leaves

section Lanes

set_option linter.unusedSectionVars false

variable (T : TypingFacts env hn) (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env)
  (A : VecAgreeNC env P) (Fy : FloatTyping env)
include T V Ty A Fy

/-- `fwdN_vecExtractLaneNum`, before the lift. -/
theorem spureV_vecExtractLaneNum (sh : Shape) (i : LaneIdx) (a : V128) (hi : i.val < sh.lanes)
    (hw : 32 ≤ sh.laneWidth)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecExtractLane sh none i)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecExtractLane sh none i)]))
      (adminsToV ([(Val.num ⟨sh.unpacked, vecExtractLane sh none i.val a⟩).toAdmin])) := by
  obtain ⟨ls, ha, hk⟩ := A.extractNum sh a i.val hi hw
  rcases sh with sh | sh <;> cases sh
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)
  · exact (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.int .i32)) (Ty.dim (.int .i32x4)) (Ty.laneidx i) (Fy.num "nt" ⟨.int .i32, _⟩)
      ha hk)
  · exact (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.int .i64)) (Ty.dim (.int .i64x2)) (Ty.laneidx i) (Fy.num "nt" ⟨.int .i64, _⟩)
      ha hk)
  · exact (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.float .f32)) (Ty.dim (.float .f32x4)) (Ty.laneidx i)
      (Fy.num "nt" ⟨.float .f32, _⟩) ha hk)
  · exact (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.float .f64)) (Ty.dim (.float .f64x2)) (Ty.laneidx i)
      (Fy.num "nt" ⟨.float .f64, _⟩) ha hk)

/-- `fwdN_vecExtractLanePack`, before the lift. -/
theorem spureV_vecExtractLanePack (sh : IntShape) (sx : Signedness) (i : LaneIdx) (a : V128)
    (hi : i.val < sh.lanes) (hw : sh.laneWidth < 32)
    (_hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecExtractLane (.int sh) (some sx) i)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecExtractLane (.int sh) (some sx) i)]))
      (adminsToV ([(Val.num ⟨(Shape.int sh).unpacked,
        vecExtractLane (.int sh) (some sx) i.val a⟩).toAdmin])) := by
  obtain ⟨ls, l, n, ha, hk, hn', he⟩ := A.extractPack sh sx a i.val hi hw
  cases sh
  · exact (spure_vextractLanePack V.vextractLanePack (Ty.vec a)
      (Ty.packtype _ hw) (Ty.dim (.int .i8x16)) (Ty.sx sx) (Ty.laneidx i) (Ty.i32 _) ha hk hn' he)
  · exact (spure_vextractLanePack V.vextractLanePack (Ty.vec a)
      (Ty.packtype _ hw) (Ty.dim (.int .i16x8)) (Ty.sx sx) (Ty.laneidx i) (Ty.i32 _) ha hk hn' he)
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

/-- `fwdN_vecExtractLane`, before the lift. -/
theorem spureV_vecExtractLane (sh : Shape) (sx : Option Signedness) (i : LaneIdx) (a : V128)
    (hi : i.val < sh.lanes)
    (hcode : TypedV env instrsT (.list (adminsToV ([vconst a, .plain (.vecExtractLane sh sx i)])))) :
    SPure env (adminsToV ([vconst a, .plain (.vecExtractLane sh sx i)]))
      (adminsToV ([(Val.num ⟨sh.unpacked, vecExtractLane sh sx i.val a⟩).toAdmin])) := by
  have hty : InstrTyped env (.vecExtractLane sh sx i) := typed_last2 T (hcode)
  have hsx : sx = none ↔ 32 ≤ sh.laneWidth := Ty.extractSx sh sx i hty
  cases sx with
  | none => exact spureV_vecExtractLaneNum T V Ty A Fy sh i a hi (hsx.1 rfl) hcode
  | some x =>
      have hw : ¬ 32 ≤ sh.laneWidth := fun h => by cases hsx.2 h
      cases sh with
      | int sh =>
          exact spureV_vecExtractLanePack T V Ty A Fy sh x i a hi (by
            simp only [Shape.laneWidth] at hw; omega) hcode
      | float sh => cases sh <;> exact absurd (by decide) hw


end Lanes

/-! ## The vector family at `BI` -/

section Dispatch

open Round4Int (BI)
open Round5.Target (AdminsSel AdminSel instrSel)

variable (hn : H → String) (host : HostSemantics H)

/-- `vcvtop` from `AdminsSel` code, exactly (`Cover.fwd_vecConvertSel`, before the lift). -/
theorem spureV_vecConvertSel {sh₁ sh₂ : Shape} {op : VecConvertOp} {a r : V128}
    (hc : VecConvertRel P sh₁ sh₂ op a r)
    (hsel : AdminsSel [vconst a, .plain (.vecConvert sh₁ sh₂ op)])
    (hcode : TypedV (simEnv (BI P hn host)) instrsT
      (.list (adminsToV [vconst a, .plain (.vecConvert sh₁ sh₂ op)]))) :
    SPure (simEnv (BI P hn host)) (adminsToV [vconst a, .plain (.vecConvert sh₁ sh₂ op)])
      (adminsToV [vconst r]) := by
  have hi : instrSel (.vecConvert sh₁ sh₂ op) = true := by
    simpa only [AdminsSel, AdminSel, and_true] using hsel.2
  obtain ⟨hf, sg, rfl⟩ := Cover.extend_of_instrSel hi
  have C : Round5.Simd.VecConvertR (simEnv (BI P hn host)) P :=
    Round5.Convert.vecConvertR_builtins
  obtain ⟨c, hcv⟩ := C.total sh₁ sh₂ _ a r hc
  obtain ⟨r', hr', rfl⟩ := C.sound sh₁ sh₂ _ a c hcv
  obtain rfl : r = r' := Cover.vecConvertRel_extend_fun hc hr'
  exact spureV_vecConvertR (Typing.typingFacts_simEnv _ hn) (Vec.hasVectorRules_simEnv _)
    (Round5.SimdTy.vecTypingL P hn host) Round5.Convert.vecAgreeNC_builtins hcv hcode

/-- **The vector family**, as `Step_pure` facts at the concrete primitives, from `AdminsSel`
code (`Cover.fwd_vectorSel` before the lift). -/
theorem spure_of_vector {is is' : List Admin} (h : VectorStep P is is') (hsel : AdminsSel is)
    (hcode : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV is))) :
    SPure (simEnv (BI P hn host)) (adminsToV is) (adminsToV is') := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have V : HasVectorRules (simEnv (BI P hn host)) := Vec.hasVectorRules_simEnv _
  have Ty : Round5.SimdTy.VecTypingL (simEnv (BI P hn host)) :=
    Round5.SimdTy.vecTypingL P hn host
  have A : VecAgreeNC (simEnv (BI P hn host)) P := Round5.Convert.vecAgreeNC_builtins
  cases h with
  | vecConvert hc => exact spureV_vecConvertSel hn host hc hsel hcode
  | vecUnOp op a => exact spureV_vecUnOp T V Ty A op a hcode
  | vecBinOp op a b => exact spureV_vecBinOp T V Ty A op a b hcode
  | vecTernOp op a b c => exact spureV_vecTernOp T V Ty A op a b c hcode
  | vecTestOp op a => exact spureV_vecTestOp T V Ty A op a hcode
  | vecIntUnOp sh op a => exact spureV_vecIntUnOp T V Ty A sh op a hcode
  | vecFloatUnOp h => exact spureV_vecFloatUnOp T V Ty A h hcode
  | vecFloatUnOpTrap h => exact spureV_vecFloatUnOpTrap T V Ty A h hcode
  | vecIntBinOp sh op a b => exact spureV_vecIntBinOp T V Ty A sh op a b hcode
  | vecFloatBinOp h => exact spureV_vecFloatBinOp T V Ty A h hcode
  | vecFloatBinOpTrap h => exact spureV_vecFloatBinOpTrap T V Ty A h hcode
  | vecIntTernOp sh op a b c => exact spureV_vecIntTernOp T V Ty A sh op a b c hcode
  | vecFloatTernOp h => exact spureV_vecFloatTernOp T V Ty A h hcode
  | vecFloatTernOpTrap h => exact spureV_vecFloatTernOpTrap T V Ty A h hcode
  | vecAllTrue sh a => exact spureV_vecAllTrue T V Ty A sh a hcode
  | vecIntRelOp sh op a b => exact spureV_vecIntRelOp T V Ty A sh op a b hcode
  | vecFloatRelOp sh op a b => exact spureV_vecFloatRelOp T V Ty A sh op a b hcode
  | vecShiftOp sh op a n => exact spureV_vecShiftOp T V Ty A sh op a n hcode
  | vecBitmask sh a => exact spureV_vecBitmask T V Ty A sh a hcode
  | vecSwizzle a b => exact spureV_vecSwizzle T V Ty A a b hcode
  | vecRelaxedSwizzle a b => exact spureV_vecRelaxedSwizzle T V Ty A a b hcode
  | vecShuffle idx a b hidx => exact spureV_vecShuffle T V Ty A idx a b hidx hcode
  | vecSplat sh x => exact spureV_vecSplat T V Ty A sh x hcode
  | vecExtractLane sh sx i a hi =>
    exact spureV_vecExtractLane T V Ty A (Floats.floatTyping_simEnv _) sh sx i a hi hcode
  | vecReplaceLane sh i a x hi => exact spureV_vecReplaceLane T V Ty A sh i a x hi hcode
  | vecExtUnOp h => exact spureV_vecExtUnOp T V Ty A h hcode
  | vecExtBinOp h => exact spureV_vecExtBinOp T V Ty A h hcode
  | vecExtTernOp h => exact spureV_vecExtTernOp T V Ty A h hcode
  | vecNarrow h => exact spureV_vecNarrow T V Ty A h hcode

end Dispatch

end Silmaril.Wasm.SpecTec.Institution.FwdX30
