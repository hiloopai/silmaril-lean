module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflCtx

/-!
# Reflecting Core typings of single non-control 2.0 instructions

For every non-control Wasm 2.0 instruction `i` with Core image `c`, a Core typing
`InstrOk D c it` in an image context (`Rel C D`) gives the 2.0 typing
`InstrsOk C [i] (erT it)` of the read-back type. Each lemma inverts the Core rule (the delegating
constructor of `InstrOk`, then the family relation) and applies the matching 2.0 rule; the
side conditions are the same predicates on both sides, up to the argument order of the vector
shape operators.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC)
open Silmaril.Wasm.Validation (TypeCtx TyOk)

/-- Core 3.0 validation contexts. -/
abbrev KCtx := Silmaril.Wasm.Validation.Context
/-- Wasm 2.0 validation contexts. -/
abbrev VCtx := Silmaril.Wasm.V2.Validation.Context
/-- Core 3.0 instruction typing. -/
abbrev KOk := Silmaril.Wasm.Validation.InstrOk
/-- Wasm 2.0 instruction-sequence typing. -/
abbrev VSeq := Silmaril.Wasm.V2.Validation.InstrsOk

/-- The read-back of a Core instruction type (its `inits` are dropped). -/
def erT (Δ : TypeCtx) (it : Silmaril.Wasm.Validation.InstrType) :
    Silmaril.Wasm.V2.Validation.InstrType :=
  ⟨ers Δ it.params, ers Δ it.results⟩

/-- Invert a Core typing of a non-control instruction: the delegating constructor of `InstrOk`,
then the family relation. -/
local macro "kinv " h:ident : tactic =>
  `(tactic| (cases $h:ident <;> rename_i $h:ident <;> cases $h:ident))

variable {C : VCtx} {D : KCtx} {it : Silmaril.Wasm.Validation.InstrType}

/-- A 2.0 rule as a sequence typing. -/
theorem vone {i : Silmaril.Wasm.V2.Instr} {u : Silmaril.Wasm.V2.Validation.InstrType}
    (h : Silmaril.Wasm.V2.Validation.InstrOk C i u) : VSeq C [i] u := .instr h

/-! ## Parametric -/

theorem r_nop (h : KOk D .nop it) : VSeq C [.nop] (erT D.toTypeCtx it) := by
  kinv h; exact vone .nop

theorem r_unreachable (h : KOk D .unreachable it) :
    VSeq C [.unreachable] (erT D.toTypeCtx it) := by
  kinv h; exact vone .unreachable

theorem r_drop (h : KOk D .drop it) : VSeq C [.drop] (erT D.toTypeCtx it) := by
  kinv h; exact vone .drop

/-- `select` with an annotation: Core and 2.0 both need exactly one type. -/
theorem r_selectExpl (ts : List Silmaril.Wasm.V2.ValType)
    (h : KOk D (.select (some (Silmaril.Wasm.V2.ResultType.toCore ts))) it) :
    VSeq C [.select (some ts)] (erT D.toTypeCtx it) := by
  match ts, h with
  | [t], h =>
    kinv h
    have e : D.closeVal t.toCore = Silmaril.Wasm.V2.ValType.toC t :=
      Silmaril.Wasm.V2.Validation.closeVal_toCore D t
    show VSeq C _ ⟨ers _ [D.closeVal t.toCore, D.closeVal t.toCore, _], ers _ [D.closeVal t.toCore]⟩
    rw [e]
    simp only [ers, List.map_cons, List.map_nil, er_toC]
    exact vone (.selectExpl (t := t))
  | [], h => kinv h
  | _ :: _ :: _, h => kinv h

/-- A numeric-or-vector Core type reads back as a 2.0 numeric-or-vector type. -/
theorem isNumOrVec_er (Δ : TypeCtx) {t : KVal} (h : t.IsNumOrVec) :
    ∃ t' : Silmaril.Wasm.V2.ValType, er Δ t = .val t' ∧
      Silmaril.Wasm.V2.Validation.NumOrVec t' := by
  cases t with
  | num t => exact ⟨.num t, rfl, .inl ⟨t, rfl⟩⟩
  | vec t => exact ⟨.vec t, rfl, .inr ⟨t, rfl⟩⟩
  | refv _ => exact absurd h (by simp [Silmaril.Wasm.Validation.Ty.IsNumOrVec])
  | botv => exact absurd h (by simp [Silmaril.Wasm.Validation.Ty.IsNumOrVec])

/-- A numeric-or-vector type is well formed. -/
theorem isNumOrVec_ok (Δ : TypeCtx) {t : KVal} (h : t.IsNumOrVec) : TyOk Δ t := by
  cases t with
  | num t => exact .num t
  | vec t => exact .vec t
  | refv _ => exact absurd h (by simp [Silmaril.Wasm.Validation.Ty.IsNumOrVec])
  | botv => exact absurd h (by simp [Silmaril.Wasm.Validation.Ty.IsNumOrVec])

/-- `select` without an annotation. -/
theorem r_selectImpl (hR : Rel C D) (h : KOk D (.select none) it) :
    VSeq C [.select none] (erT D.toTypeCtx it) := by
  kinv h
  rename_i t t' hok hs hnv
  obtain ⟨u, hu, hnu⟩ := isNumOrVec_er D.toTypeCtx hnv
  have hsub : (er D.toTypeCtx t).Sub (.val u) :=
    hu ▸ er_sub hR.typesOk hR.recs hok (isNumOrVec_ok _ hnv) hs
  exact vone (.selectImpl hsub hnu)

/-! ## Numeric -/

theorem r_intConst {t : Silmaril.Wasm.IntType} {b : BitVec t.width}
    (h : KOk D (.intConst t b) it) : VSeq C [.intConst t b] (erT D.toTypeCtx it) := by
  kinv h; exact vone .intConst

theorem r_floatConst {t : Silmaril.Wasm.FloatType} {b : BitVec t.width}
    (h : KOk D (.floatConst t b) it) : VSeq C [.floatConst t b] (erT D.toTypeCtx it) := by
  kinv h; exact vone .floatConst

theorem r_intUnOp {t op} (h : KOk D (.intUnOp t op) it) :
    VSeq C [.intUnOp t op] (erT D.toTypeCtx it) := by
  kinv h; exact vone (.intUnOp ‹_›)

theorem r_floatUnOp {t op} (h : KOk D (.floatUnOp t op) it) :
    VSeq C [.floatUnOp t op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .floatUnOp

theorem r_intBinOp {t op} (h : KOk D (.intBinOp t op) it) :
    VSeq C [.intBinOp t op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .intBinOp

theorem r_floatBinOp {t op} (h : KOk D (.floatBinOp t op) it) :
    VSeq C [.floatBinOp t op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .floatBinOp

theorem r_intTestOp {t op} (h : KOk D (.intTestOp t op) it) :
    VSeq C [.intTestOp t op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .intTestOp

theorem r_intRelOp {t op} (h : KOk D (.intRelOp t op) it) :
    VSeq C [.intRelOp t op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .intRelOp

theorem r_floatRelOp {t op} (h : KOk D (.floatRelOp t op) it) :
    VSeq C [.floatRelOp t op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .floatRelOp

/-- A defined conversion relates two different number types. -/
theorem cvt_ne {t₁ t₂ : Silmaril.Wasm.NumType} {op : Silmaril.Wasm.V2.CvtOp}
    {c : Silmaril.Wasm.ConvertOp} (h : Silmaril.Wasm.V2.CvtOp.toCore t₁ t₂ op = some c) :
    t₁ ≠ t₂ := by
  rintro rfl
  revert h
  rcases t₁ with t | t <;> cases t <;> cases op <;>
    simp [Silmaril.Wasm.V2.CvtOp.toCore, Silmaril.Wasm.V2.CvtOp.toShared]

/-- `cvtop`: 2.0's `/cvtop-convert` rule covers every defined conversion. -/
theorem r_cvtOp {t₁ t₂ op} {c : Silmaril.Wasm.ConvertOp}
    (hc : Silmaril.Wasm.V2.CvtOp.toCore t₁ t₂ op = some c) (h : KOk D (.convert c) it) :
    VSeq C [.cvtOp t₁ t₂ op] (erT D.toTypeCtx it) := by
  obtain ⟨hs, ht⟩ := Silmaril.Wasm.V2.Validation.cvtOp_toCore_types hc
  have hdef : (op.toShared t₁ t₂).isSome := by
    change (Silmaril.Wasm.V2.CvtOp.toCore t₁ t₂ op).isSome
    rw [hc]; rfl
  kinv h
  show VSeq C _ ⟨[er _ (.num c.source)], [er _ (.num c.target)]⟩
  rw [hs, ht]
  exact vone (.cvtOpConvert (cvt_ne hc) hdef)

/-! ## Vector -/

theorem r_vecConst {b} (h : KOk D (.vecConst b) it) :
    VSeq C [.vecConst b] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecConst

theorem r_vvUnOp {op} (h : KOk D (.vecUnOp op) it) : VSeq C [.vvUnOp op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vvUnOp

theorem r_vvBinOp {op} (h : KOk D (.vecBinOp op) it) :
    VSeq C [.vvBinOp op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vvBinOp

theorem r_vvTernOp {op} (h : KOk D (.vecTernOp op) it) :
    VSeq C [.vvTernOp op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vvTernOp

theorem r_vvTestOp {op} (h : KOk D (.vecTestOp op) it) :
    VSeq C [.vvTestOp op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vvTestOp

theorem r_vecIntUnOp {s op} (h : KOk D (.vecIntUnOp s op) it) :
    VSeq C [.vecIntUnOp s op] (erT D.toTypeCtx it) := by
  kinv h; exact vone (.vecIntUnOp ‹_›)

theorem r_vecFloatUnOp {s op} (h : KOk D (.vecFloatUnOp s op) it) :
    VSeq C [.vecFloatUnOp s op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecFloatUnOp

theorem r_vecIntBinOp {s} {op : Silmaril.Wasm.V2.VecIntBinOp}
    (h : KOk D (.vecIntBinOp s op.toCore) it) :
    VSeq C [.vecIntBinOp s op] (erT D.toTypeCtx it) := by
  kinv h
  rename_i hv
  exact vone (.vecIntBinOp (by simpa using hv))

theorem r_vecFloatBinOp {s} {op : Silmaril.Wasm.V2.VecFloatBinOp}
    (h : KOk D (.vecFloatBinOp s op.toCore) it) :
    VSeq C [.vecFloatBinOp s op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecFloatBinOp

theorem r_vecAllTrue {s} (h : KOk D (.vecAllTrue s) it) :
    VSeq C [.vecAllTrue s] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecAllTrue

theorem r_vecIntRelOp {s op} (h : KOk D (.vecIntRelOp s op) it) :
    VSeq C [.vecIntRelOp s op] (erT D.toTypeCtx it) := by
  kinv h; exact vone (.vecIntRelOp ‹_›)

theorem r_vecFloatRelOp {s op} (h : KOk D (.vecFloatRelOp s op) it) :
    VSeq C [.vecFloatRelOp s op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecFloatRelOp

theorem r_vecShiftOp {s op} (h : KOk D (.vecShiftOp s op) it) :
    VSeq C [.vecShiftOp s op] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecShiftOp

theorem r_vecBitmask {s} (h : KOk D (.vecBitmask s) it) :
    VSeq C [.vecBitmask s] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecBitmask

theorem r_vecSwizzle (h : KOk D (.vecSwizzle .swizzle) it) :
    VSeq C [.vecSwizzle] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecSwizzle

theorem r_vecShuffle {lanes} (h : KOk D (.vecShuffle lanes) it) :
    VSeq C [.vecShuffle lanes] (erT D.toTypeCtx it) := by
  kinv h; exact vone (.vecShuffle ‹_› ‹_›)

theorem r_vecSplat {s} (h : KOk D (.vecSplat s) it) :
    VSeq C [.vecSplat s] (erT D.toTypeCtx it) := by
  kinv h; exact vone .vecSplat

theorem r_vecExtractLane {s sx i} (h : KOk D (.vecExtractLane s sx i) it) :
    VSeq C [.vecExtractLane s sx i] (erT D.toTypeCtx it) := by
  kinv h; exact vone (.vecExtractLane ‹_› ‹_›)

theorem r_vecReplaceLane {s i} (h : KOk D (.vecReplaceLane s i) it) :
    VSeq C [.vecReplaceLane s i] (erT D.toTypeCtx it) := by
  kinv h; exact vone (.vecReplaceLane ‹_›)

/-- Core's `vextunop` side condition is 2.0's (the lower bound `16` is implied). -/
theorem extUnOp_valid2 {target source : Silmaril.Wasm.IntShape} {op : Silmaril.Wasm.VecExtUnOp}
    (h : op.valid source target = true) :
    Silmaril.Wasm.V2.VecExtUnOp.valid2 target source op = true := by
  revert h
  cases target <;> cases source <;> cases op <;> rename_i sx <;> cases sx <;> decide

theorem r_vecExtUnOp {t s op} (h : KOk D (.vecExtUnOp s t op) it) :
    VSeq C [.vecExtUnOp t s op] (erT D.toTypeCtx it) := by
  kinv h
  rename_i hv
  exact vone (.vecExtUnOp (extUnOp_valid2 hv))

theorem r_vecExtBinOp {t s} {op : Silmaril.Wasm.V2.VecExtBinOp}
    (h : KOk D (.vecExtBinOp s t op.toCore) it) :
    VSeq C [.vecExtBinOp t s op] (erT D.toTypeCtx it) := by
  kinv h
  rename_i hv
  exact vone (.vecExtBinOp (by simpa using hv))

theorem r_vecNarrow {t s sx} (h : KOk D (.vecNarrow s t sx) it) :
    VSeq C [.vecNarrow t s sx] (erT D.toTypeCtx it) := by
  kinv h
  rename_i hv
  exact vone (.vecNarrow hv.1 hv.2)

theorem r_vecCvtOp {t s} {op : Silmaril.Wasm.V2.VecCvtOp}
    (h : KOk D (.vecConvert s t op.toCore) it) :
    VSeq C [.vecCvtOp t s op] (erT D.toTypeCtx it) := by
  kinv h
  rename_i hv
  exact vone (.vecCvtOp (by simpa using hv))

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
