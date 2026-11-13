module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30Table
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30Agg
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30Mem
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30Ctrl
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30Vec
public import Silmaril.Wasm.SpecTec.Sim.Round4.Thms
public import Silmaril.Wasm.SpecTec.Sim.ConfigOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms
public import Silmaril.Wasm.SpecTec.Sim.Aggregates.Thms
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms

/-!
# The forward direction at wasm-3.0, extended: the declarative facts

At the concrete primitives `Round4Int.BI P hn host`, every `PureHeadX P is is'` with typed `is`
is a `Step_pure` fact of the declarative reading `SPure`, and every `ReadHeadX P c is'` from a
typed, bounded configuration is a `Step_read` fact `SRead`.

The proofs are the bodies of the forward leaves of rounds 2–5 (`IntNumeric.fwd_int*`,
`Vec.fwd_float*`, `Vec.fwd_convert*`, `Round6.Target.fwd_referenceNC`, `Aggregates.fwd_arrayNew`,
`Sim.fwd_brOnNullAddr`, `Sim.fwd_brOnNonNullAddr`, `Exn.fwd_handlerVals`), stopped before the
leaf lifts the fact to `Step` with `Step/pure` or `Step/read`. Those leaves state only the lifted
`FwdP` fact, so their bodies are copied here. The primitives' laws are the proved ones at `BI`:
`Prims.intB_builtins`, `Prims.floatB_builtins`, `Prims.rFuns_builtins`,
`Round5.Fwd.rStore_builtins`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Execution (constV trapV i32V pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Round4Int (BI)

variable {H : Type}

/-! ## Integer numerics (`IntNumeric.fwd_int*`), at any `B` with `IntB B` -/

section Int

variable {B : Builtins} (hB : IntNumeric.IntB B)

include hB in
/-- `binop-val` at an integer type. -/
theorem spure_intBinOp {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
    (h : intBinOp t op x y = .ok z) :
    SPure (simEnv B) (adminsToV [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intBinOp t op)]) (adminsToV [.plain (.intConst t z)]) := by
  have TY := IntNumeric.intTyping_simEnv B
  have hz : ibinop_ t.width op x y = some z := by rw [ibinop_agree, h]; rfl
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "binop_"
      [.val (IntNumeric.ntV t), .val (IntNumeric.ibinopV op), .val (bvV x), .val (bvV y)]
      (.list [bvV z]) := by
    simpa [hz] using IntNumeric.applies_binop_int hB t op x y
  have hρ := IntNumeric.valsOnly_bindVals
    [("nt", IntNumeric.ntV t), ("c_1", bvV x), ("c_2", bvV y), ("binop", IntNumeric.ibinopV op),
      ("c", bvV z)]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), adminToV (.plain (.intConst t y)),
    instrToV (.intBinOp t op)] [adminToV (.plain (.intConst t z))]
  rw [IntNumeric.instrToV_intBinOp]
  simp only [IntNumeric.adminToV_intConst]
  exact IntNumeric.spure_binopVal (IntNumeric.hasNumericRules_simEnv B).binopVal
    (TY.numtype _ t hρ) (TY.num _ _ t x hρ (Sem.evalExp_var rfl)) (TY.num _ _ t y hρ (Sem.evalExp_var rfl))
    (TY.binop _ _ t op hρ (Sem.evalExp_var rfl)) (TY.num _ _ t z hρ (Sem.evalExp_var rfl)) happ
    (by simp [memValue])

include hB in
/-- `binop-trap` at an integer type. -/
theorem spure_intBinOpTrap {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {e : IntTrap}
    (h : intBinOp t op x y = .error e) :
    SPure (simEnv B) (adminsToV [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intBinOp t op)]) (adminsToV [.trap]) := by
  have TY := IntNumeric.intTyping_simEnv B
  have hz : ibinop_ t.width op x y = none := by rw [ibinop_agree, h]; rfl
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "binop_"
      [.val (IntNumeric.ntV t), .val (IntNumeric.ibinopV op), .val (bvV x), .val (bvV y)]
      (.list []) := by
    simpa [hz] using IntNumeric.applies_binop_int hB t op x y
  have hρ := IntNumeric.valsOnly_bindVals
    [("nt", IntNumeric.ntV t), ("c_1", bvV x), ("c_2", bvV y), ("binop", IntNumeric.ibinopV op)]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), adminToV (.plain (.intConst t y)),
    instrToV (.intBinOp t op)] [.case "TRAP" (.tuple [])]
  rw [IntNumeric.instrToV_intBinOp]
  simp only [IntNumeric.adminToV_intConst]
  exact IntNumeric.spure_binopTrap (IntNumeric.hasNumericRules_simEnv B).binopTrap
    (TY.numtype _ t hρ) (TY.num _ _ t x hρ (Sem.evalExp_var rfl)) (TY.num _ _ t y hρ (Sem.evalExp_var rfl))
    (TY.binop _ _ t op hρ (Sem.evalExp_var rfl)) happ

include hB in
/-- `unop-val` at an integer type, for an operator valid at the type. -/
theorem spure_intUnOp {t : IntType} {op : IntUnOp} {x : BitVec t.width}
    (hv : op.valid t = true) :
    SPure (simEnv B) (adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)])
      (adminsToV [.plain (.intConst t (Numerics.intUnOp t op x))]) := by
  have TY := IntNumeric.intTyping_simEnv B
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "unop_"
      [.val (IntNumeric.ntV t), .val (IntNumeric.iunopV op), .val (bvV x)]
      (.list [bvV (Numerics.intUnOp t op x)]) := by
    simpa [iunop_agree] using IntNumeric.applies_unop_int hB t op hv x
  have hρ := IntNumeric.valsOnly_bindVals
    [("nt", IntNumeric.ntV t), ("c_1", bvV x), ("unop", IntNumeric.iunopV op),
      ("c", bvV (Numerics.intUnOp t op x))]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), instrToV (.intUnOp t op)]
    [adminToV (.plain (.intConst t (Numerics.intUnOp t op x)))]
  rw [IntNumeric.instrToV_intUnOp t op hv]
  simp only [IntNumeric.adminToV_intConst]
  exact IntNumeric.spure_unopVal (IntNumeric.hasNumericRules_simEnv B).unopVal
    (TY.numtype _ t hρ) (TY.num _ _ t x hρ (Sem.evalExp_var rfl))
    (TY.unop _ _ t op hv hρ (Sem.evalExp_var rfl)) (TY.num _ _ t _ hρ (Sem.evalExp_var rfl)) happ
    (by simp [memValue])

omit hB in
/-- `unop` at an operator not valid at the type: the code is not typed. -/
theorem spure_intUnOp_invalid {t : IntType} {op : IntUnOp} {x : BitVec t.width} {js : List Value}
    (hv : op.valid t = false)
    (hc : TypedV (simEnv B) instrsT
      (.list (adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)]))) :
    SPure (simEnv B) (adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)]) js := by
  have hj : adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)] =
      [adminToV (.plain (.intConst t x))] ++ .tuple [] :: [] := by
    show [_, instrToV (.intUnOp t op)] = _
    rw [IntNumeric.instrToV_intUnOp_invalid t op hv]
    rfl
  rw [hj] at hc
  exact (IntNumeric.not_typedV_junk B [] hc).elim

omit hB in
/-- `testop` at an integer type. -/
theorem spure_intTestOp {t : IntType} {op : IntTestOp} {x : BitVec t.width} :
    SPure (simEnv B) (adminsToV [.plain (.intConst t x), .plain (.intTestOp t op)])
      (adminsToV [constI32 (Numerics.intTestOp t op x)]) := by
  have TY := IntNumeric.intTyping_simEnv B
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "testop_"
      [.val (IntNumeric.ntV t), .val (IntNumeric.itestopV op), .val (bvV x)]
      (bvV (Numerics.intTestOp t op x)) := by
    simpa [itestop_agree] using IntNumeric.applies_testop_int (B := B) t op x
  have hρ := IntNumeric.valsOnly_bindVals
    [("nt", IntNumeric.ntV t), ("c_1", bvV x), ("testop", IntNumeric.itestopV op),
      ("c", bvV (Numerics.intTestOp t op x))]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), instrToV (.intTestOp t op)]
    [adminToV (constI32 (Numerics.intTestOp t op x))]
  rw [IntNumeric.instrToV_intTestOp, IntNumeric.adminToV_constI32]
  simp only [IntNumeric.adminToV_intConst]
  exact IntNumeric.spure_testop (IntNumeric.hasNumericRules_simEnv B).testop (TY.numtype _ t hρ)
    (TY.num _ _ t x hρ (Sem.evalExp_var rfl)) (TY.testop _ _ t op hρ (Sem.evalExp_var rfl))
    (TY.num _ _ .i32 _ hρ IntNumeric.evalExp_i32) happ

omit hB in
/-- `relop` at an integer type. -/
theorem spure_intRelOp {t : IntType} {op : IntRelOp} {x y : BitVec t.width} :
    SPure (simEnv B) (adminsToV [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intRelOp t op)]) (adminsToV [constI32 (Numerics.intRelOp t op x y)]) := by
  have TY := IntNumeric.intTyping_simEnv B
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "relop_"
      [.val (IntNumeric.ntV t), .val (IntNumeric.irelopV op), .val (bvV x), .val (bvV y)]
      (bvV (Numerics.intRelOp t op x y)) := by
    simpa [irelop_agree] using IntNumeric.applies_relop_int (B := B) t op x y
  have hρ := IntNumeric.valsOnly_bindVals
    [("nt", IntNumeric.ntV t), ("c_1", bvV x), ("c_2", bvV y), ("relop", IntNumeric.irelopV op),
      ("c", bvV (Numerics.intRelOp t op x y))]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), adminToV (.plain (.intConst t y)),
    instrToV (.intRelOp t op)] [adminToV (constI32 (Numerics.intRelOp t op x y))]
  rw [IntNumeric.instrToV_intRelOp, IntNumeric.adminToV_constI32]
  simp only [IntNumeric.adminToV_intConst]
  exact IntNumeric.spure_relop (IntNumeric.hasNumericRules_simEnv B).relop (TY.numtype _ t hρ)
    (TY.num _ _ t x hρ (Sem.evalExp_var rfl)) (TY.num _ _ t y hρ (Sem.evalExp_var rfl))
    (TY.relop _ _ t op hρ (Sem.evalExp_var rfl)) (TY.num _ _ .i32 _ hρ IntNumeric.evalExp_i32) happ

end Int

/-! ## Floats and conversions (`Vec.fwd_float*`, `Vec.fwd_convert*`), at any `env` -/

section Float

open Silmaril.SpecTec.Equiv.ExecNumeric (Applies HasNumericRules)
open Silmaril.Wasm.SpecTec.Sim.Vec

variable {env : Env} {P : Profile} (N : HasNumericRules env) (Ty : FloatTyping env)
  (A : FloatAgree env P)

include N Ty A

/-- `unop-val` at a float type. -/
theorem spure_floatUnOp {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
    (h : floatUnOpP P t op x z) :
    SPure env (adminsToV [.plain (.floatConst t x), .plain (.floatUnOp t op)])
      (adminsToV [.plain (.floatConst t z)]) := by
  obtain ⟨L, ha, hL⟩ := A.unop t op x
  have hm : floatV t z ∈ L := (hL _).2 ⟨z, h, rfl⟩
  have hs : SPure env [constV (numTypeV (.float t)) (floatV t x),
      .case "UNOP" (.tuple [numTypeV (.float t), fUnOpV op])]
      [constV (numTypeV (.float t)) (floatV t z)] :=
    Vec.spure_unopVal N.unopVal (Ty.numtype _) (Ty.num "nt" ⟨.float t, x⟩) (Ty.unop t op)
      (Ty.num "nt" ⟨.float t, z⟩) ha hm
  have e₁ : adminsToV [.plain (.floatConst t x), .plain (.floatUnOp t op)] =
      [constV (numTypeV (.float t)) (floatV t x),
        .case "UNOP" (.tuple [numTypeV (.float t), fUnOpV op])] := by
    simp only [adminsToV, adminToV, instrToV_floatConst, instrToV_floatUnOp]
  have e₂ : adminsToV [.plain (.floatConst t z)] = [constV (numTypeV (.float t)) (floatV t z)] := by
    simp only [adminsToV, adminToV, instrToV_floatConst]
  exact e₁ ▸ e₂ ▸ hs

/-- `binop-val` at a float type. -/
theorem spure_floatBinOp {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
    (h : floatBinOpP P t op x y z) :
    SPure env (adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatBinOp t op)]) (adminsToV [.plain (.floatConst t z)]) := by
  obtain ⟨L, ha, hL⟩ := A.binop t op x y
  have hm : floatV t z ∈ L := (hL _).2 ⟨z, h, rfl⟩
  have hs : SPure env [constV (numTypeV (.float t)) (floatV t x),
      constV (numTypeV (.float t)) (floatV t y),
      .case "BINOP" (.tuple [numTypeV (.float t), fBinOpV op])]
      [constV (numTypeV (.float t)) (floatV t z)] :=
    Vec.spure_binopVal N.binopVal (Ty.numtype _) (Ty.num "nt" ⟨.float t, x⟩)
      (Ty.num "nt" ⟨.float t, y⟩) (Ty.binop t op) (Ty.num "nt" ⟨.float t, z⟩) ha hm
  have e₁ : adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatBinOp t op)] =
      [constV (numTypeV (.float t)) (floatV t x), constV (numTypeV (.float t)) (floatV t y),
        .case "BINOP" (.tuple [numTypeV (.float t), fBinOpV op])] := by
    simp only [adminsToV, adminToV, instrToV_floatConst, instrToV_floatBinOp]
  have e₂ : adminsToV [.plain (.floatConst t z)] = [constV (numTypeV (.float t)) (floatV t z)] := by
    simp only [adminsToV, adminToV, instrToV_floatConst]
  exact e₁ ▸ e₂ ▸ hs

/-- `relop` at a float type. -/
theorem spure_floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} :
    SPure env (adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatRelOp t op)]) (adminsToV [constI32 (floatRelOp t op x y)]) := by
  have hs : SPure env [constV (numTypeV (.float t)) (floatV t x),
      constV (numTypeV (.float t)) (floatV t y),
      .case "RELOP" (.tuple [numTypeV (.float t), vFloatRelOpV op])]
      [constV i32V (i32NV (floatRelOp t op x y))] :=
    Vec.spure_relop N.relop (Ty.numtype _) (Ty.num "nt" ⟨.float t, x⟩)
      (Ty.num "nt" ⟨.float t, y⟩) (Ty.relop t op) (Ty.i32 _) (A.relop t op x y)
  have e₁ : adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatRelOp t op)] =
      [constV (numTypeV (.float t)) (floatV t x), constV (numTypeV (.float t)) (floatV t y),
        .case "RELOP" (.tuple [numTypeV (.float t), vFloatRelOpV op])] := by
    simp only [adminsToV, adminToV, instrToV_floatConst, instrToV_floatRelOp]
  exact e₁ ▸ hs

/-- `cvtop-val`, for every `ConvertOp`, at typed code. -/
theorem spure_convert {hn : H → String} (T : TypingFacts env hn) {op : ConvertOp}
    {x : BitVec op.source.width} {z : BitVec op.target.width} (h : convertP P op x (.ok z))
    (hc : TypedV env instrsT
      (.list (adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]))) :
    SPure env (adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)])
      (adminsToV [(Val.num ⟨op.target, z⟩).toAdmin]) := by
  have hi : InstrTyped env (.convert op) := typed_last2 T hc
  obtain ⟨L, ha, hL, -⟩ := A.cvtop op x
  have hm : numV ⟨op.target, z⟩ ∈ L := (hL _).2 ⟨z, h, rfl⟩
  have hs : SPure env [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
      .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])]
      [constV (numTypeV op.target) (numV ⟨op.target, z⟩)] :=
    spure_cvtopVal N.cvtopVal (Ty.numtype _) (Ty.numtype _) (Ty.num "nt_1" ⟨op.source, x⟩)
      (Ty.cvtop op hi) (Ty.num "nt_2" ⟨op.target, z⟩) ha hm
  have e₁ : adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] =
      [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
        .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])] := by
    simp only [adminsToV, adminToV_valNum]
    rfl
  have e₂ : adminsToV [(Val.num ⟨op.target, z⟩).toAdmin] =
      [constV (numTypeV op.target) (numV ⟨op.target, z⟩)] := by
    simp only [adminsToV, adminToV_valNum]
  exact e₁ ▸ e₂ ▸ hs

/-- `cvtop-trap`, for every `ConvertOp`, at typed code. -/
theorem spure_convertTrap {hn : H → String} (T : TypingFacts env hn) {op : ConvertOp}
    {x : BitVec op.source.width} {e : FloatTrap} (h : convertP P op x (.error e))
    (hc : TypedV env instrsT
      (.list (adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]))) :
    SPure env (adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)])
      (adminsToV [.trap]) := by
  have hi : InstrTyped env (.convert op) := typed_last2 T hc
  obtain ⟨L, ha, -, hnil⟩ := A.cvtop op x
  have hL : L = [] := hnil.2 ⟨e, h⟩
  have ha' : Applies env "cvtop__" [.val (numTypeV op.source), .val (numTypeV op.target),
      .val (cvtOpV op), .val (numV ⟨op.source, x⟩)] (.list []) := hL ▸ ha
  have hs : SPure env [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
      .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])] [trapV] :=
    spure_cvtopTrap N.cvtopTrap (Ty.numtype _) (Ty.numtype _) (Ty.num "nt_1" ⟨op.source, x⟩)
      (Ty.cvtop op hi) ha'
  have e₁ : adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] =
      [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
        .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])] := by
    simp only [adminsToV, adminToV_valNum]
    rfl
  exact e₁ ▸ hs

end Float

/-! ## The numeric family at `BI` -/

/-- **The numeric family**, as `Step_pure` facts at the concrete primitives. -/
theorem spure_numeric {P : Profile} (hn : H → String) (host : HostSemantics H)
    {is is' : List Admin} (hp : NumericStep P is is')
    (hc : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV is))) :
    SPure (simEnv (BI P hn host)) (adminsToV is) (adminsToV is') := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have hI : IntNumeric.IntB (BI P hn host) := Prims.intB_builtins hn host
  have N := Vec.hasNumericRules_simEnv (BI P hn host)
  have Fy : Vec.FloatTyping (simEnv (BI P hn host)) := Floats.floatTyping_simEnv _
  have FA : Vec.FloatAgree (simEnv (BI P hn host)) P :=
    Floats.floatAgree_simEnv (Prims.floatB_builtins hn host)
  cases hp with
  | @intUnOp t op x =>
    cases hv : op.valid t
    · exact spure_intUnOp_invalid hv hc
    · exact spure_intUnOp hI hv
  | intBinOp hz => exact spure_intBinOp hI hz
  | intBinOpTrap he => exact spure_intBinOpTrap hI he
  | intTestOp => exact spure_intTestOp
  | intRelOp => exact spure_intRelOp
  | floatUnOp hz => exact spure_floatUnOp N Fy FA hz
  | floatBinOp hz => exact spure_floatBinOp N Fy FA hz
  | floatRelOp => exact spure_floatRelOp N Fy FA
  | convert hz => exact spure_convert N Fy FA T hz hc
  | convertTrap he => exact spure_convertTrap N Fy FA T he hc

/-! ## Control: `br_on_null`/`br_on_non_null` at a non-null value, `handler` with values -/

section Ctrl

variable (B : Builtins) (hn : H → String)
include hn

/-- `br_on_null` at a non-null value (`Sim.fwd_brOnNullAddr`). -/
theorem spure_brOnNullAddrH {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [v.toAdmin, .plain (.brOnNull l)]))) :
    SPure (simEnv B) (adminsToV [v.toAdmin, .plain (.brOnNull l)]) (adminsToV [v.toAdmin]) := by
  have T := Typing.typingFacts_simEnv B hn
  have Tg := Typing.ctrlTyping_simEnv B
  have hvs := typedV_vals_prefix T (vs := [v]) (b := [.plain (.brOnNull l)]) h
  have hx : TypedV (simEnv B) valT (valV v) := by
    simpa [Sim.adminsToV_vals, Sim.adminToV_toAdmin] using
      typedV_list_single.1 (by simpa [Sim.adminsToV_vals, Sim.adminToV_toAdmin] using hvs)
  have key := spure_brOnNullAddr (simEnv_refRules B).brOnNullAddr hx (Tg.labelidx l)
    (otherwise_brOnNullAddr B (valV_ne_null hv))
  have e : adminToV (.plain (.brOnNull l)) = .case "BR_ON_NULL" (Encode.toValue l) := rfl
  simpa [Sim.adminToV_toAdmin, e] using key

/-- `br_on_non_null` at a non-null value (`Sim.fwd_brOnNonNullAddr`). -/
theorem spure_brOnNonNullAddrH {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [v.toAdmin, .plain (.brOnNonNull l)]))) :
    SPure (simEnv B) (adminsToV [v.toAdmin, .plain (.brOnNonNull l)])
      (adminsToV [v.toAdmin, .plain (.br l)]) := by
  have T := Typing.typingFacts_simEnv B hn
  have Tg := Typing.ctrlTyping_simEnv B
  have hvs := typedV_vals_prefix T (vs := [v]) (b := [.plain (.brOnNonNull l)]) h
  have hx : TypedV (simEnv B) valT (valV v) := by
    simpa [Sim.adminsToV_vals, Sim.adminToV_toAdmin] using
      typedV_list_single.1 (by simpa [Sim.adminsToV_vals, Sim.adminToV_toAdmin] using hvs)
  have key := spure_brOnNonNullAddr (simEnv_refRules B).brOnNonNullAddr hx (Tg.labelidx l)
    (otherwise_brOnNonNullAddr B (valV_ne_null hv))
  have e : adminToV (.plain (.brOnNonNull l)) = .case "BR_ON_NON_NULL" (pctV l.toNat) := rfl
  simpa [Sim.adminToV_toAdmin, Sim.toValue_idx, e] using key

/-- A handler with values (`Exn.fwd_handlerVals`). -/
theorem spure_handlerValsH {n : Nat} {cs : List Catch} {vs : List Val}
    (his : TypedV (simEnv B) instrsT (.list (adminsToV [.handler n cs (vals vs)]))) :
    SPure (simEnv B) (adminsToV [.handler n cs (vals vs)]) (adminsToV (vals vs)) := by
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨hn₀, hcs, hb⟩ := T.handler n cs _ his
  have hvs := T.vals vs hb
  rw [Exn.adminsToV_vals] at hvs
  have h := Exn.spure_handlerVals (Exn.hasPureRules_simEnv B).handlerVals hn₀ hcs hvs
  rw [Exn.adminsToV_vals]
  simpa only [adminsToV, adminToV, Exn.adminsToV_vals] using h

/-- `local.tee` (`State.fwd_localTee`), with the value's typing read off the code. -/
theorem spure_localTeeH {v : Val} {x : LocalIdx}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [v.toAdmin, .plain (.localTee x)]))) :
    SPure (simEnv B) (adminsToV [v.toAdmin, .plain (.localTee x)])
      (adminsToV [v.toAdmin, v.toAdmin, .plain (.localSet x)]) := by
  have T := Typing.typingFacts_simEnv B hn
  have St : State.StateTyping (simEnv B) := Typing.stateTyping_simEnv B
  have hvs := typedV_vals_prefix T (vs := [v]) (b := [.plain (.localTee x)]) h
  have hx : TypedV (simEnv B) valT (valV v) := by
    simpa [Sim.adminsToV_vals, Sim.adminToV_toAdmin] using
      typedV_list_single.1 (by simpa [Sim.adminsToV_vals, Sim.adminToV_toAdmin] using hvs)
  have key := State.spure_localTee (State.hasPureRules_simEnv B).localTee hx
    (St.idx _ x.value.isLt)
  show SPure _ [adminToV v.toAdmin, _] [adminToV v.toAdmin, adminToV v.toAdmin, _]
  rw [Sim.adminToV_toAdmin]
  exact key

end Ctrl

/-! ## The whole classification at `BI` -/

/-- **`PureHeadX` steps are `Step_pure` facts** of the declarative reading at the concrete
primitives, at typed code. The reference leaves are those of `Round6.Target.fwd_referenceNC`. -/
theorem spure_of_pureHeadX {P : Profile} (hn : H → String) (host : HostSemantics H)
    {is is' : List Admin} (hp : PureHeadX P is is')
    (hc : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV is))) :
    SPure (simEnv (BI P hn host)) (adminsToV is) (adminsToV is') := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv (BI P hn host) hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv (BI P hn host)
  have F : RefsGC.RFuns (simEnv (BI P hn host)) := Prims.rFuns_builtins hn host
  have rr : Equiv.ExecRef.HasRefRules (envOfScript Specs.wasm30) := Equiv.ExecRef.hasRefRules_wasm30
  have pt : ((RefsGC.relRules (simEnv (BI P hn host)) "Step_pure").map RefsGC.ruleTags).take 46 =
      RefsGC.pureTagTable := RefsGC.pureTable_simEnv (BI P hn host)
  cases hp with
  | numeric h => exact spure_numeric hn host h hc
  | vector h hsel => exact spure_of_vector hn host h hsel hc
  | refI31 i => exact RefsGC.spure_refI31 (RefsGC.refRule _ rr.refI31) R F i
  | isNullTrue =>
    exact RefsGC.spure_isNullTrue (RefsGC.refRule _ rr.refIsNullTrue)
      (R.ref _ (RefsGC.typed_head T hc))
  | isNullFalse hr =>
    exact RefsGC.spure_isNullFalse (RefsGC.refRule _ rr.refIsNullFalse)
      (RefsGC.refRule _ rr.refIsNullTrue) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullNull =>
    exact RefsGC.spure_asNonNullNull (RefsGC.refRule _ rr.refAsNonNullNull)
      (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullAddr hr =>
    exact RefsGC.spure_asNonNullAddr (RefsGC.refRule _ rr.refAsNonNullAddr)
      (RefsGC.refRule _ rr.refAsNonNullNull) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | eqNull =>
    exact RefsGC.spure_eqNull (RefsGC.refRule _ rr.refEqNull) (R.ref _ (RefsGC.typed_head T hc))
  | eqTrue hr =>
    exact RefsGC.spure_eqTrue (RefsGC.refRule _ rr.refEqTrue) (RefsGC.refRule _ rr.refEqNull) pt hr
      (R.ref _ (RefsGC.typed_head T hc))
  | eqFalse hr =>
    exact RefsGC.spure_eqFalse (RefsGC.refRule _ rr.refEqFalse) (RefsGC.refRule _ rr.refEqNull)
      (RefsGC.refRule _ rr.refEqTrue) pt hr (R.ref _ (RefsGC.typed_head T hc))
      (R.ref _ (RefsGC.typed_head T (RefsGC.typed_tail T hc)))
  | i31GetNull sx => exact RefsGC.spure_i31GetNull (RefsGC.refRule _ rr.i31GetNull) R sx
  | i31GetNum sx i => exact RefsGC.spure_i31GetNum (RefsGC.refRule _ rr.i31GetNum) R F sx i
  | externConvertNull =>
    exact RefsGC.spure_externConvertNull (RefsGC.refRule _ rr.externConvertAnyNull)
      (R.ref _ (RefsGC.typed_head T hc))
  | externConvertAddr hr =>
    exact RefsGC.spure_externConvertAddr (RefsGC.refRule _ rr.externConvertAnyAddr)
      (RefsGC.refRule _ rr.externConvertAnyNull) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | anyConvertNull => exact RefsGC.spure_anyConvertNull (RefsGC.refRule _ rr.anyConvertExternNull)
  | anyConvertAddr r =>
    exact RefsGC.spure_anyConvertAddr (RefsGC.refRule _ rr.anyConvertExternAddr)
      (R.externArg r (RefsGC.typed_head T hc))
  | arrayNew v n =>
    exact Aggregates.spure_arrayNew
      (hasRuleAt_simEnv _ Equiv.ExecPureArrayNew.hasArrayNew_wasm30) T R v n hc
  | brOnNullAddr hv => exact spure_brOnNullAddrH _ hn hv hc
  | brOnNonNullAddr hv => exact spure_brOnNonNullAddrH _ hn hv hc
  | localTee => exact spure_localTeeH _ hn hc
  | handlerVals => exact spure_handlerValsH _ hn hc

/-- **`ReadHeadX` steps are `Step_read` facts** of the declarative reading at the concrete
primitives, from a typed, bounded configuration to typed code (the leaves of `Round6.Target.fwd_referenceNC` and
of `Memory.fwd_table_bounded`, `Round5.Fwd.fwd_memory5` and `Round5.Fwd.fwd_aggregate5`). -/
theorem sread_of_readHeadX {P : Profile} (hn : H → String) (host : HostSemantics H)
    {c : Config H} {is' : List Admin} (hr : ReadHeadX P c is') (hb : Round4.Bounded c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hc' : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV is'))) :
    SRead (simEnv (BI P hn host)) (configV hn c) (adminsToV is') := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv (BI P hn host) hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  have hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn c.store c.frame) :=
    ((T.config c).1 hc).1
  have hcode : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV c.code)) :=
    ((T.config c).1 hc).2
  cases hr with
  | refNull ht => exact RefsGC.sread_refNull (hasRuleAt_simEnv _ rd.refNull) R hz hcode
  | refFunc ha => exact RefsGC.sread_refFunc (hasRuleAt_simEnv _ rd.refFunc) R G ha hz hcode
  | table h =>
    exact sread_of_tableStep _ T (Typing.stateTyping_simEnv _) (ConfigOk.memTyping_simEnv _) h.1
      h.2 hb.store.tables hc
  | memory h => exact sread_of_memStep hn host h.1 h.2 hb hc
  | aggregate h => exact sread_of_aggStep hn host h.1 h.2 hb hc
  | ctrl h => exact sread_of_ctrlRead hn host h hb.frame hz hcode hc'

end Silmaril.Wasm.SpecTec.Institution.FwdX30
