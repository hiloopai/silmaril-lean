module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Ops
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly

/-!
# Integer numerics: Core → SpecTec, constructor by constructor

Each `fwd_*` is the `Forward` obligation for one constructor of Core's `ParametricStep` or of the
integer part of `NumericStep`, at `env := simEnv B`, under `IntB B` (the integer primitives),
`IntTyping (simEnv B)` (the typing of the quantified values) and `TypingFacts`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type} {hn : H → String} {B : Builtins}

/-! ## The encodings of the integer instructions -/

theorem instrToV_intBinOp (t : IntType) (op : IntBinOp) :
    instrToV (.intBinOp t op) = .case "BINOP" (.tuple [ntV t, ibinopV op]) := by
  cases t <;> cases op <;> (try rename_i s; cases s) <;> rfl

theorem instrToV_intRelOp (t : IntType) (op : IntRelOp) :
    instrToV (.intRelOp t op) = .case "RELOP" (.tuple [ntV t, irelopV op]) := by
  cases t <;> cases op <;> (try rename_i s; cases s) <;> rfl

theorem instrToV_intTestOp (t : IntType) (op : IntTestOp) :
    instrToV (.intTestOp t op) = .case "TESTOP" (.tuple [ntV t, itestopV op]) := by
  cases t <;> cases op <;> rfl

/-- A valid integer unary operator. -/
theorem instrToV_intUnOp (t : IntType) (op : IntUnOp) (hv : op.valid t = true) :
    instrToV (.intUnOp t op) = .case "UNOP" (.tuple [ntV t, iunopV op]) := by
  cases t <;> cases op <;> (try rename_i p; cases p) <;>
    first | rfl | (simp [IntUnOp.valid, PackSize.width, IntType.width] at hv)

/-- An integer constant. -/
theorem adminToV_intConst (t : IntType) (b : BitVec t.width) :
    adminToV (.plain (.intConst t b)) = .case "CONST" (.tuple [ntV t, bvV b]) := rfl

/-- An `i32` constant. -/
theorem adminToV_constI32 (r : BitVec 32) :
    adminToV (constI32 r) = .case "CONST" (.tuple [ntV .i32, bvV r]) := rfl

/-- A Core value's instruction is its value. -/
theorem adminToV_toAdmin (v : Val) : adminToV v.toAdmin = valV v := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> rfl

/-- An integer unary operator not valid at the type (`extendN_s` with `N` not below the width)
has no `instr` image: `instrToV` sends it to the junk `.tuple []`. -/
theorem instrToV_intUnOp_invalid (t : IntType) (op : IntUnOp) (hv : op.valid t = false) :
    instrToV (.intUnOp t op) = .tuple [] := by
  cases t <;> cases op <;> (try rename_i p; cases p) <;>
    first | rfl | (simp [IntUnOp.valid, PackSize.width, IntType.width] at hv)

set_option maxRecDepth 100000 in
/-- `instr` is a variant type in the fixed script. -/
theorem findTyp_instr (B : Builtins) :
    ∃ cs, (simEnv B).findTyp? "instr" = some ([], [.instD [] [] (.variantT cs)]) := ⟨_, rfl⟩

/-- Nothing but an injection inhabits `instr`. -/
theorem not_hasTyp_instr_tuple (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) (vs : List Value) :
    ¬ HasTyp (simEnv B) ρ (.varT "instr" []) (.tuple vs) := by
  intro h
  obtain ⟨cs, hcs⟩ := findTyp_instr B
  have hl : localTyp? ρ "instr" [] = none := by
    simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [hcs] at htd
  cases htd
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hi'
  · obtain ⟨op, w, he, -⟩ := hasTypDef_variantT_iff.1 hd
    cases he
  · exact not_hasTypInsts_nil hi'

/-- A typed instruction sequence holds no junk. -/
theorem not_typedV_junk (B : Builtins) {a b : List Value} (vs : List Value)
    (h : TypedV (simEnv B) instrsT (.list (a ++ .tuple vs :: b))) : False := by
  have hρ : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 (h _ hρ)
  cases hl
  exact not_hasTyp_instr_tuple B hρ vs (hasTypList_iff.1 hall _ (by simp))

/-! ## From a `Step_pure` derivation to `FwdP` -/

/-- A `Step_pure` derivation between the images of two instruction sequences is a whole-machine
step between the configurations, at any store and frame. -/
theorem fwd_of_spure {env : Env} (T : TypingFacts env hn)
    (R : Equiv.Validation.HasRuleAt env "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : SPure env (adminsToV is) (adminsToV is')) : FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨-, hcode'⟩ := (T.config _).1 hc'
  exact sstep_pure R hst hcode hcode' h

/-- The scope of a rule instance binds term variables only. -/
theorem valsOnly_bindVals (σ : List (IL.Id × Value)) : ValsOnly (VarEnv.empty.bindVals σ) :=
  ⟨rfl, rfl, rfl⟩

/-! ## The integer constructors of `NumericStep` -/

section Numeric

variable (hB : IntB B) (TY : IntTyping (simEnv B)) (T : TypingFacts (simEnv B) hn)
include hB TY T

/-- `NumericStep.intBinOp`: `binop-val`. -/
theorem fwd_intBinOp {s : Store H} {f : Frame} {t : IntType} {op : IntBinOp}
    {x y z : BitVec t.width} (h : intBinOp t op x y = .ok z) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intBinOp t op)]⟩ ⟨s, f, [.plain (.intConst t z)]⟩ := by
  refine fwd_of_spure T (hasStepRules_simEnv B).pure ?_
  have hz : ibinop_ t.width op x y = some z := by rw [ibinop_agree, h]; rfl
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "binop_"
      [.val (ntV t), .val (ibinopV op), .val (bvV x), .val (bvV y)] (.list [bvV z]) := by
    simpa [hz] using applies_binop_int hB t op x y
  have hρ := valsOnly_bindVals
    [("nt", ntV t), ("c_1", bvV x), ("c_2", bvV y), ("binop", ibinopV op), ("c", bvV z)]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), adminToV (.plain (.intConst t y)),
    instrToV (.intBinOp t op)] [adminToV (.plain (.intConst t z))]
  rw [instrToV_intBinOp]
  simp only [adminToV_intConst]
  exact spure_binopVal (hasNumericRules_simEnv B).binopVal (TY.numtype _ t hρ)
    (TY.num _ _ t x hρ (evalExp_var rfl)) (TY.num _ _ t y hρ (evalExp_var rfl))
    (TY.binop _ _ t op hρ (evalExp_var rfl)) (TY.num _ _ t z hρ (evalExp_var rfl)) happ
    (by simp [memValue])

/-- `NumericStep.intBinOpTrap`: `binop-trap` (division by zero, signed overflow). -/
theorem fwd_intBinOpTrap {s : Store H} {f : Frame} {t : IntType} {op : IntBinOp}
    {x y : BitVec t.width} {e : IntTrap} (h : intBinOp t op x y = .error e) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intBinOp t op)]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwd_of_spure T (hasStepRules_simEnv B).pure ?_
  have hz : ibinop_ t.width op x y = none := by rw [ibinop_agree, h]; rfl
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "binop_"
      [.val (ntV t), .val (ibinopV op), .val (bvV x), .val (bvV y)] (.list []) := by
    simpa [hz] using applies_binop_int hB t op x y
  have hρ := valsOnly_bindVals
    [("nt", ntV t), ("c_1", bvV x), ("c_2", bvV y), ("binop", ibinopV op)]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), adminToV (.plain (.intConst t y)),
    instrToV (.intBinOp t op)] [.case "TRAP" (.tuple [])]
  rw [instrToV_intBinOp]
  simp only [adminToV_intConst]
  exact spure_binopTrap (hasNumericRules_simEnv B).binopTrap (TY.numtype _ t hρ)
    (TY.num _ _ t x hρ (evalExp_var rfl)) (TY.num _ _ t y hρ (evalExp_var rfl))
    (TY.binop _ _ t op hρ (evalExp_var rfl)) happ

/-- `NumericStep.intUnOp`, for an operator valid at the type: `unop-val`. -/
theorem fwd_intUnOp {s : Store H} {f : Frame} {t : IntType} {op : IntUnOp}
    {x : BitVec t.width} (hv : op.valid t = true) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.intConst t x), .plain (.intUnOp t op)]⟩
      ⟨s, f, [.plain (.intConst t (Numerics.intUnOp t op x))]⟩ := by
  refine fwd_of_spure T (hasStepRules_simEnv B).pure ?_
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "unop_"
      [.val (ntV t), .val (iunopV op), .val (bvV x)] (.list [bvV (Numerics.intUnOp t op x)]) := by
    simpa [iunop_agree] using applies_unop_int hB t op hv x
  have hρ := valsOnly_bindVals
    [("nt", ntV t), ("c_1", bvV x), ("unop", iunopV op), ("c", bvV (Numerics.intUnOp t op x))]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), instrToV (.intUnOp t op)]
    [adminToV (.plain (.intConst t (Numerics.intUnOp t op x)))]
  rw [instrToV_intUnOp t op hv]
  simp only [adminToV_intConst]
  exact spure_unopVal (hasNumericRules_simEnv B).unopVal (TY.numtype _ t hρ)
    (TY.num _ _ t x hρ (evalExp_var rfl)) (TY.unop _ _ t op hv hρ (evalExp_var rfl))
    (TY.num _ _ t _ hρ (evalExp_var rfl)) happ (by simp [memValue])

omit hB TY in
/-- `NumericStep.intUnOp` at an operator *not* valid at the type: the configuration is not
typed, so the obligation holds vacuously. -/
theorem fwd_intUnOp_invalid {s : Store H} {f : Frame} {t : IntType} {op : IntUnOp}
    {x : BitVec t.width} {c' : Config H} (hv : op.valid t = false) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.intConst t x), .plain (.intUnOp t op)]⟩ c' := by
  intro hc _
  obtain ⟨-, hcode⟩ := (T.config _).1 hc
  have hj : adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)] =
      [adminToV (.plain (.intConst t x))] ++ .tuple [] :: [] := by
    show [_, instrToV (.intUnOp t op)] = _
    rw [instrToV_intUnOp_invalid t op hv]
    rfl
  rw [hj] at hcode
  exact (not_typedV_junk B [] hcode).elim

omit hB in
/-- `NumericStep.intTestOp`: `testop`. -/
theorem fwd_intTestOp {s : Store H} {f : Frame} {t : IntType} {op : IntTestOp}
    {x : BitVec t.width} :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.intConst t x), .plain (.intTestOp t op)]⟩
      ⟨s, f, [constI32 (Numerics.intTestOp t op x)]⟩ := by
  refine fwd_of_spure T (hasStepRules_simEnv B).pure ?_
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "testop_"
      [.val (ntV t), .val (itestopV op), .val (bvV x)] (bvV (Numerics.intTestOp t op x)) := by
    simpa [itestop_agree] using applies_testop_int (B := B) t op x
  have hρ := valsOnly_bindVals
    [("nt", ntV t), ("c_1", bvV x), ("testop", itestopV op),
      ("c", bvV (Numerics.intTestOp t op x))]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), instrToV (.intTestOp t op)]
    [adminToV (constI32 (Numerics.intTestOp t op x))]
  rw [instrToV_intTestOp, adminToV_constI32]
  simp only [adminToV_intConst]
  exact spure_testop (hasNumericRules_simEnv B).testop (TY.numtype _ t hρ)
    (TY.num _ _ t x hρ (evalExp_var rfl)) (TY.testop _ _ t op hρ (evalExp_var rfl))
    (TY.num _ _ .i32 _ hρ evalExp_i32) happ

omit hB in
/-- `NumericStep.intRelOp`: `relop`. -/
theorem fwd_intRelOp {s : Store H} {f : Frame} {t : IntType} {op : IntRelOp}
    {x y : BitVec t.width} :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.intConst t x), .plain (.intConst t y),
      .plain (.intRelOp t op)]⟩ ⟨s, f, [constI32 (Numerics.intRelOp t op x y)]⟩ := by
  refine fwd_of_spure T (hasStepRules_simEnv B).pure ?_
  have happ : Equiv.ExecNumeric.Applies (simEnv B) "relop_"
      [.val (ntV t), .val (irelopV op), .val (bvV x), .val (bvV y)]
      (bvV (Numerics.intRelOp t op x y)) := by
    simpa [irelop_agree] using applies_relop_int (B := B) t op x y
  have hρ := valsOnly_bindVals
    [("nt", ntV t), ("c_1", bvV x), ("c_2", bvV y), ("relop", irelopV op),
      ("c", bvV (Numerics.intRelOp t op x y))]
  show SPure (simEnv B) [adminToV (.plain (.intConst t x)), adminToV (.plain (.intConst t y)),
    instrToV (.intRelOp t op)] [adminToV (constI32 (Numerics.intRelOp t op x y))]
  rw [instrToV_intRelOp, adminToV_constI32]
  simp only [adminToV_intConst]
  exact spure_relop (hasNumericRules_simEnv B).relop (TY.numtype _ t hρ)
    (TY.num _ _ t x hρ (evalExp_var rfl)) (TY.num _ _ t y hρ (evalExp_var rfl))
    (TY.relop _ _ t op hρ (evalExp_var rfl)) (TY.num _ _ .i32 _ hρ evalExp_i32) happ

/-- **`Forward.numeric`**, from the integer constructors proved here and the float and
conversion constructors as `OtherNumericFwd`. -/
theorem fwd_numeric {P : Profile} (O : OtherNumericFwd (simEnv B) hn P) :
    ∀ {s : Store H} {f : Frame} {is is' : List Admin} (_ : NumericStep P is is'),
      FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is is' h
  cases h with
  | intUnOp =>
      rename_i t op x
      cases hv : op.valid t
      · exact fwd_intUnOp_invalid T hv
      · exact fwd_intUnOp hB TY T hv
  | floatUnOp h => exact O.floatUnOp h
  | intBinOp h => exact fwd_intBinOp hB TY T h
  | intBinOpTrap h => exact fwd_intBinOpTrap hB TY T h
  | floatBinOp h => exact O.floatBinOp h
  | intTestOp => exact fwd_intTestOp TY T
  | intRelOp => exact fwd_intRelOp TY T
  | floatRelOp => exact O.floatRelOp
  | convert h => exact O.convert h
  | convertTrap h => exact O.convertTrap h

end Numeric

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
