module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Rules
public import Silmaril.Wasm.SpecTec.Sim.Round5.VecTyL.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Lift
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Provenance

/-!
# Family V: Core's `VectorStep`, simulated forward

One lemma per constructor of `Silmaril.Wasm.Execution.Core.VectorStep` (except the four listed
below): between typed configurations, the Core step is a SpecTec `Step` of the images, through
`Step/pure` and the matching vector rule of `Step_pure`. Each lemma assumes the rule provenance
(`HasVectorRules`, discharged for `simEnv B` by `hasVectorRules_simEnv`), the encoding's
`TypingFacts`, the vector typing facts `VecTyping` and the operator agreement `VecAgree`.

`Assembly.lean` puts them together into the `Forward.vector` obligation.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}

/-! ## Plumbing -/

/-- Every vector rule fact about the pinned script holds of `simEnv B`. -/
theorem hasVectorRules_simEnv (B : Builtins) : HasVectorRules (simEnv B) := by
  have h := Silmaril.SpecTec.Equiv.ExecVector.hasVectorRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- A `Step_pure` step of the images is a forward step, through `Step/pure`. -/
theorem fwd_of_spure (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : SPure env (adminsToV is) (adminsToV is')) : FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  have hst : TypedV env stateT (stateV hn s f) := ((T.config _).1 hc).1
  have hcode : TypedV env instrsT (.list (adminsToV is)) := ((T.config _).1 hc).2
  have hcode' : TypedV env instrsT (.list (adminsToV is')) := ((T.config _).1 hc').2
  exact sstep_pure hr hst hcode hcode' h

/-- The code of a typed configuration is typed. -/
theorem typed_code (T : TypingFacts env hn) {s : Store H} {f : Frame} {is : List Admin}
    (hc : Typed env hn ⟨s, f, is⟩) : TypedV env instrsT (.list (adminsToV is)) :=
  ((T.config _).1 hc).2

/-- The last of two typed instructions is typed. -/
theorem typed_last2 (T : TypingFacts env hn) {x y : Value}
    (h : TypedV env instrsT (.list [x, y])) : TypedV env instrsT (.list [y]) :=
  ((T.append [x] [y]).1 h).2

/-- The last of three typed instructions is typed. -/
theorem typed_last3 (T : TypingFacts env hn) {x y z : Value}
    (h : TypedV env instrsT (.list [x, y, z])) : TypedV env instrsT (.list [z]) :=
  ((T.append [x, y] [z]).1 h).2

/-- The last of four typed instructions is typed. -/
theorem typed_last4 (T : TypingFacts env hn) {x y z w : Value}
    (h : TypedV env instrsT (.list [x, y, z, w])) : TypedV env instrsT (.list [w]) :=
  ((T.append [x, y, z] [w]).1 h).2

/-- A result list that `↔`-characterises an empty relation is empty. -/
theorem list_eq_nil_of_iff {L : List Value} {R : Value → Prop} (hL : ∀ c, c ∈ L ↔ R c)
    (hR : ∀ c, ¬ R c) : L = [] := by
  cases L with
  | nil => rfl
  | cons c _ => exact absurd ((hL c).1 List.mem_cons_self) (hR c)

/-! ## The bitwise operators (`vv*`) -/

section

variable (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgree env P)
  {s : Store H} {f : Frame}

include T hr V Ty A

/-- `VectorStep.vecUnOp`, forward (`Step_pure/vvunop`). -/
theorem fwd_vecUnOp (op : VecUnOp) (a : V128) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecUnOp op)]⟩ ⟨s, f, [vconst (vvunop op a)]⟩ :=
  fwd_of_spure T hr (spure_vvunop V.vvunop (Ty.vec a) (Ty.vvunop op) (Ty.vec _) (A.vvunop op a)
    List.mem_cons_self)

/-- `VectorStep.vecBinOp`, forward (`Step_pure/vvbinop`). -/
theorem fwd_vecBinOp (op : VecBinOp) (a b : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecBinOp op)]⟩
      ⟨s, f, [vconst (vvbinop op a b)]⟩ :=
  fwd_of_spure T hr (spure_vvbinop V.vvbinop (Ty.vec a) (Ty.vec b) (Ty.vvbinop op) (Ty.vec _)
    (A.vvbinop op a b) List.mem_cons_self)

/-- `VectorStep.vecTernOp`, forward (`Step_pure/vvternop`). -/
theorem fwd_vecTernOp (op : VecTernOp) (a b c : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, vconst c, .plain (.vecTernOp op)]⟩
      ⟨s, f, [vconst (vvternop op a b c)]⟩ :=
  fwd_of_spure T hr (spure_vvternop V.vvternop (Ty.vec a) (Ty.vec b) (Ty.vec c) (Ty.vvternop op)
    (Ty.vec _) (A.vvternop op a b c) List.mem_cons_self)

/-- `VectorStep.vecTestOp`, forward (`Step_pure/vvtestop`). -/
theorem fwd_vecTestOp (op : VecTestOp) (a : V128) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecTestOp op)]⟩ ⟨s, f, [constI32 (vvtestop op a)]⟩ := by
  cases op
  obtain ⟨n, hn', ha⟩ := A.vvtestop .anyTrue a
  exact fwd_of_spure T hr (spure_vvtestop V.vvtestop (Ty.vec a) (Ty.i32 _) hn' ha)

end

/-! ## The shape-indexed operators -/

section

variable (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgree env P)
  {s : Store H} {f : Frame}

include T hr V Ty A

/-- `VectorStep.vecIntUnOp`, forward (`Step_pure/vunop-val`). -/
theorem fwd_vecIntUnOp (sh : IntShape) (op : VecIntUnOp) (a : V128) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecIntUnOp sh op)]⟩
      ⟨s, f, [vconst (vecIntUnOp sh op a)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecIntUnOp sh op) := typed_last2 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vunopVal V.vunopVal (Ty.vec a) (Ty.shape (.int sh))
    (Ty.intUnOp sh op hi) (Ty.vec _) (A.intUnOp sh op a) List.mem_cons_self) hc hc'

/-- `VectorStep.vecFloatUnOp`, forward (`Step_pure/vunop-val`). -/
theorem fwd_vecFloatUnOp {sh : FloatShape} {op : FloatUnOp} {a r : V128}
    (h : VecFloatUnOpRel P sh op a r) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecFloatUnOp sh op)]⟩ ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecFloatUnOp sh op) := typed_last2 T (typed_code T hc)
  obtain ⟨L, ha, hL⟩ := A.floatUnOp sh op a
  have hm : vecV r ∈ L := (hL _).2 ⟨r, h, rfl⟩
  exact fwd_of_spure T hr (spure_vunopVal V.vunopVal (Ty.vec a) (Ty.shape (.float sh))
    (Ty.floatUnOp sh op hi) (Ty.vec r) ha hm) hc hc'

/-- `VectorStep.vecFloatUnOpTrap`, forward (`Step_pure/vunop-trap`). -/
theorem fwd_vecFloatUnOpTrap {sh : FloatShape} {op : FloatUnOp} {a : V128}
    (h : ∀ r, ¬ VecFloatUnOpRel P sh op a r) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecFloatUnOp sh op)]⟩ ⟨s, f, [.trap]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecFloatUnOp sh op) := typed_last2 T (typed_code T hc)
  obtain ⟨L, ha, hL⟩ := A.floatUnOp sh op a
  have hnil : L = [] := list_eq_nil_of_iff hL fun c ⟨r, hr', _⟩ => h r hr'
  have ha' : Applies env "vunop_" [.val (fshV sh), .val (vFloatUnOpV op), .val (vecV a)]
      (.list []) := hnil ▸ ha
  exact fwd_of_spure T hr (spure_vunopTrap V.vunopTrap (Ty.vec a) (Ty.shape (.float sh))
    (Ty.floatUnOp sh op hi) ha') hc hc'

/-- `VectorStep.vecIntBinOp`, forward (`Step_pure/vbinop-val`). -/
theorem fwd_vecIntBinOp (sh : IntShape) (op : VecIntBinOp) (a b : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecIntBinOp sh op)]⟩
      ⟨s, f, [vconst (vecIntBinOp P sh op a b)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecIntBinOp sh op) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vbinopVal V.vbinopVal (Ty.vec a) (Ty.vec b) (Ty.shape (.int sh))
    (Ty.intBinOp sh op hi) (Ty.vec _) (A.intBinOp sh op a b) List.mem_cons_self) hc hc'

/-- `VectorStep.vecFloatBinOp`, forward (`Step_pure/vbinop-val`). -/
theorem fwd_vecFloatBinOp {sh : FloatShape} {op : VecFloatBinOp} {a b r : V128}
    (h : VecFloatBinOpRel P sh op a b r) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecFloatBinOp sh op)]⟩
      ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecFloatBinOp sh op) := typed_last3 T (typed_code T hc)
  obtain ⟨L, ha, hL⟩ := A.floatBinOp sh op a b
  have hm : vecV r ∈ L := (hL _).2 ⟨r, h, rfl⟩
  exact fwd_of_spure T hr (spure_vbinopVal V.vbinopVal (Ty.vec a) (Ty.vec b)
    (Ty.shape (.float sh)) (Ty.floatBinOp sh op hi) (Ty.vec r) ha hm) hc hc'

/-- `VectorStep.vecFloatBinOpTrap`, forward (`Step_pure/vbinop-trap`). -/
theorem fwd_vecFloatBinOpTrap {sh : FloatShape} {op : VecFloatBinOp} {a b : V128}
    (h : ∀ r, ¬ VecFloatBinOpRel P sh op a b r) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecFloatBinOp sh op)]⟩ ⟨s, f, [.trap]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecFloatBinOp sh op) := typed_last3 T (typed_code T hc)
  obtain ⟨L, ha, hL⟩ := A.floatBinOp sh op a b
  have hnil : L = [] := list_eq_nil_of_iff hL fun c ⟨r, hr', _⟩ => h r hr'
  have ha' : Applies env "vbinop_"
      [.val (fshV sh), .val (vFloatBinOpV op), .val (vecV a), .val (vecV b)] (.list []) :=
    hnil ▸ ha
  exact fwd_of_spure T hr (spure_vbinopTrap V.vbinopTrap (Ty.vec a) (Ty.vec b)
    (Ty.shape (.float sh)) (Ty.floatBinOp sh op hi) ha') hc hc'

/-- `VectorStep.vecIntTernOp`, forward (`Step_pure/vternop-val`). -/
theorem fwd_vecIntTernOp (sh : IntShape) (op : VecIntTernOp) (a b c : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, vconst c, .plain (.vecIntTernOp sh op)]⟩
      ⟨s, f, [vconst (vecIntTernOp P sh op a b c)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecIntTernOp sh op) := typed_last4 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vternopVal V.vternopVal (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.shape (.int sh)) (Ty.intTernOp sh op hi) (Ty.vec _) (A.intTernOp sh op a b c)
    List.mem_cons_self) hc hc'

/-- `VectorStep.vecFloatTernOp`, forward (`Step_pure/vternop-val`). -/
theorem fwd_vecFloatTernOp {sh : FloatShape} {op : VecFloatTernOp} {a b c r : V128}
    (h : VecFloatTernOpRel P sh op a b c r) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)]⟩
      ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecFloatTernOp sh op) := typed_last4 T (typed_code T hc)
  obtain ⟨L, ha, hL⟩ := A.floatTernOp sh op a b c
  have hm : vecV r ∈ L := (hL _).2 ⟨r, h, rfl⟩
  exact fwd_of_spure T hr (spure_vternopVal V.vternopVal (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.shape (.float sh)) (Ty.floatTernOp sh op hi) (Ty.vec r) ha hm) hc hc'

/-- `VectorStep.vecFloatTernOpTrap`, forward (`Step_pure/vternop-trap`). -/
theorem fwd_vecFloatTernOpTrap {sh : FloatShape} {op : VecFloatTernOp} {a b c : V128}
    (h : ∀ r, ¬ VecFloatTernOpRel P sh op a b c r) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecFloatTernOp sh op) := typed_last4 T (typed_code T hc)
  obtain ⟨L, ha, hL⟩ := A.floatTernOp sh op a b c
  have hnil : L = [] := list_eq_nil_of_iff hL fun d ⟨r, hr', _⟩ => h r hr'
  have ha' : Applies env "vternop_" [.val (fshV sh), .val (vFloatTernOpV op), .val (vecV a),
      .val (vecV b), .val (vecV c)] (.list []) := hnil ▸ ha
  exact fwd_of_spure T hr (spure_vternopTrap V.vternopTrap (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.shape (.float sh)) (Ty.floatTernOp sh op hi) ha') hc hc'

/-- `VectorStep.vecIntRelOp`, forward (`Step_pure/vrelop`). -/
theorem fwd_vecIntRelOp (sh : IntShape) (op : IntRelOp) (a b : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecIntRelOp sh op)]⟩
      ⟨s, f, [vconst (vecIntRelOp sh op a b)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecIntRelOp sh op) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vrelop V.vrelop (Ty.vec a) (Ty.vec b) (Ty.shape (.int sh))
    (Ty.intRelOp sh op hi) (Ty.vec _) (A.intRelOp sh op a b)) hc hc'

/-- `VectorStep.vecFloatRelOp`, forward (`Step_pure/vrelop`). -/
theorem fwd_vecFloatRelOp (sh : FloatShape) (op : FloatRelOp) (a b : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecFloatRelOp sh op)]⟩
      ⟨s, f, [vconst (vecFloatRelOp sh op a b)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecFloatRelOp sh op) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vrelop V.vrelop (Ty.vec a) (Ty.vec b) (Ty.shape (.float sh))
    (Ty.floatRelOp sh op hi) (Ty.vec _) (A.floatRelOp sh op a b)) hc hc'

/-- `VectorStep.vecShiftOp`, forward (`Step_pure/vshiftop`). -/
theorem fwd_vecShiftOp (sh : IntShape) (op : VecShiftOp) (a : V128) (n : BitVec 32) :
    FwdP env hn ⟨s, f, [vconst a, constI32 n, .plain (.vecShiftOp sh op)]⟩
      ⟨s, f, [vconst (vecShiftOp sh op a n)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecShiftOp sh op) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vshiftop V.vshiftop (Ty.vec a) (Ty.i32 n) (Ty.ishape sh)
    (Ty.shiftOp sh op hi) (Ty.vec _) (A.shiftOp sh op a n)) hc hc'

/-- `VectorStep.vecBitmask`, forward (`Step_pure/vbitmask`). -/
theorem fwd_vecBitmask (sh : IntShape) (a : V128) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecBitmask sh)]⟩
      ⟨s, f, [constI32 (vecBitmask sh a)]⟩ :=
  fwd_of_spure T hr (spure_vbitmask V.vbitmask (Ty.vec a) (Ty.ishape sh) (Ty.i32 _)
    (A.bitmask sh a))

/-- `VectorStep.vecSwizzle`, forward (`Step_pure/vswizzlop`, `SWIZZLE`). -/
theorem fwd_vecSwizzle (a b : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecSwizzle .swizzle)]⟩
      ⟨s, f, [vconst (vecSwizzle a b)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecSwizzle .swizzle) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vswizzlop V.vswizzlop (Ty.vec a) (Ty.vec b) Ty.bshape
    (Ty.swizzle .swizzle hi) (Ty.vec _) (A.swizzle a b)) hc hc'

/-- `VectorStep.vecRelaxedSwizzle`, forward (`Step_pure/vswizzlop`, `RELAXED_SWIZZLE`). -/
theorem fwd_vecRelaxedSwizzle (a b : V128) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecSwizzle .relaxedSwizzle)]⟩
      ⟨s, f, [vconst (vecRelaxedSwizzle P a b)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecSwizzle .relaxedSwizzle) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vswizzlop V.vswizzlop (Ty.vec a) (Ty.vec b) Ty.bshape
    (Ty.swizzle .relaxedSwizzle hi) (Ty.vec _) (A.relaxedSwizzle a b)) hc hc'

/-- `VectorStep.vecShuffle`, forward (`Step_pure/vshuffle`). -/
theorem fwd_vecShuffle (idx : List LaneIdx) (a b : V128) (hidx : ∀ j ∈ idx, j.val < 32) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecShuffle idx)]⟩
      ⟨s, f, [vconst (vecShuffle idx a b)]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecShuffle idx) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vshuffle V.vshuffle (Ty.vec a) (Ty.vec b) Ty.bshape
    (Ty.shuffle idx hi) (Ty.vec _) ((A.shuffle idx a b _).2 ⟨hidx, rfl⟩)) hc hc'

/-- `VectorStep.vecExtUnOp`, forward (`Step_pure/vextunop`). -/
theorem fwd_vecExtUnOp {sh₁ sh₂ : IntShape} {op : VecExtUnOp} {a r : V128}
    (h : VecExtUnOpRel sh₁ sh₂ op a r) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecExtUnOp sh₁ sh₂ op)]⟩ ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecExtUnOp sh₁ sh₂ op) := typed_last2 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vextunop V.vextunop (Ty.vec a) (Ty.ishape sh₂) (Ty.ishape sh₁)
    (Ty.extUnOp sh₁ sh₂ op hi) (Ty.vec r) ((A.extUnOp sh₁ sh₂ op a _).2 ⟨r, h, rfl⟩)) hc hc'

/-- `VectorStep.vecExtBinOp`, forward (`Step_pure/vextbinop`). -/
theorem fwd_vecExtBinOp {sh₁ sh₂ : IntShape} {op : VecExtBinOp} {a b r : V128}
    (h : VecExtBinOpRel P sh₁ sh₂ op a b r) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecExtBinOp sh₁ sh₂ op)]⟩
      ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecExtBinOp sh₁ sh₂ op) := typed_last3 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vextbinop V.vextbinop (Ty.vec a) (Ty.vec b) (Ty.ishape sh₂)
    (Ty.ishape sh₁) (Ty.extBinOp sh₁ sh₂ op hi) (Ty.vec r)
    ((A.extBinOp sh₁ sh₂ op a b _).2 ⟨r, h, rfl⟩)) hc hc'

/-- `VectorStep.vecExtTernOp`, forward (`Step_pure/vextternop`). -/
theorem fwd_vecExtTernOp {sh₁ sh₂ : IntShape} {op : VecExtTernOp} {a b c r : V128}
    (h : VecExtTernOpRel P sh₁ sh₂ op a b c r) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, vconst c, .plain (.vecExtTernOp sh₁ sh₂ op)]⟩
      ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecExtTernOp sh₁ sh₂ op) := typed_last4 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vextternop V.vextternop (Ty.vec a) (Ty.vec b) (Ty.vec c)
    (Ty.ishape sh₂) (Ty.ishape sh₁) (Ty.extTernOp sh₁ sh₂ op hi) (Ty.vec r)
    ((A.extTernOp sh₁ sh₂ op a b c _).2 ⟨r, h, rfl⟩)) hc hc'

/-- `VectorStep.vecNarrow`, forward (`Step_pure/vnarrow`). -/
theorem fwd_vecNarrow {sh₁ sh₂ : IntShape} {sx : Signedness} {a b r : V128}
    (h : VecNarrowRel sh₁ sh₂ sx a b r) :
    FwdP env hn ⟨s, f, [vconst a, vconst b, .plain (.vecNarrow sh₁ sh₂ sx)]⟩
      ⟨s, f, [vconst r]⟩ :=
  fwd_of_spure T hr (spure_vnarrow V.vnarrow (Ty.vec a) (Ty.vec b) (Ty.ishape sh₂)
    (Ty.ishape sh₁) (Ty.sx sx) (Ty.vec r) ((A.narrow sh₁ sh₂ sx a b _).2 ⟨r, h, rfl⟩))

/-- `VectorStep.vecConvert`, forward (`Step_pure/vcvtop`). -/
theorem fwd_vecConvert {sh₁ sh₂ : Shape} {op : VecConvertOp} {a r : V128}
    (h : VecConvertRel P sh₁ sh₂ op a r) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecConvert sh₁ sh₂ op)]⟩ ⟨s, f, [vconst r]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.vecConvert sh₁ sh₂ op) := typed_last2 T (typed_code T hc)
  exact fwd_of_spure T hr (spure_vcvtop V.vcvtop (Ty.vec a) (Ty.shape sh₂) (Ty.shape sh₁)
    (Ty.convert sh₁ sh₂ op hi) (Ty.vec r) ((A.convert sh₁ sh₂ op a _).2 ⟨r, h, rfl⟩)) hc hc'

end

end Silmaril.Wasm.SpecTec.Sim.Vec
