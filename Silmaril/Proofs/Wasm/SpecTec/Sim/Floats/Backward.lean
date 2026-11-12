module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Convert
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Backward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Tags
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms

/-!
# Float track: the scalar numeric rules, SpecTec → Core

The integer half of `Step_pure` 46–51 is family N's (`IntNumeric.bwd_*`), which leaves the float
operators as a disjunct. Here the float disjunct is closed, so each rule is inverted completely
at the image of a Core sequence: whatever the rule derives is the image of a Core `NumericStep`.
The float premises are read back through `applies_*_float` and the uniqueness of `Applies`; the
`-trap` rules never fire on a float operator, because the profile's result sets are never empty
(`floatUnOpP_nonempty`, `floatBinOpP_nonempty`). The conversion rules 52 and 53 are inverted
here for every `ConvertOp`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three evalArgs_four)
open Silmaril.SpecTec.Equiv.Execution (constV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

variable {H : Type} {B : Builtins} {P : Profile} {host : HostSemantics H}

/-! ## Decoding float constants and conversions -/

/-- A constant at a float type is a float constant. -/
theorem dec_floatConst {a : Admin} {t : FloatType} {c : Value}
    (h : adminToV a = .case "CONST" (.tuple [Vec.numTypeV (.float t), c])) :
    ∃ b : BitVec t.width, a = .plain (.floatConst t b) ∧ c = floatV t b := by
  obtain ⟨i, rfl, hi⟩ := IntNumeric.dec_admin_plain h (by decide)
  rcases IntNumeric.dec_const hi with ⟨t', b, rfl, hp⟩ | ⟨t', b, rfl⟩
  · have h1 : Vec.numTypeV (.float t) = IntNumeric.ntV t' :=
      (List.cons.inj (Value.tuple.inj hp)).1
    exact absurd (by rw [Typing.toValue_numType]; exact h1) (IntNumeric.float_ne_ntV t t')
  · have hp : Vec.numTypeV (.float t') = Vec.numTypeV (.float t) ∧ floatV t' b = c := by
      simpa only [Vec.instrToV_floatConst, constV, Value.case.injEq, Value.tuple.injEq,
        List.cons.injEq, and_true, true_and] using hi
    obtain rfl : t' = t := NumType.float.inj (numTypeV_injective hp.1)
    exact ⟨b, rfl, hp.2.symm⟩

/-- A constant at any number type is a numeric value. -/
theorem dec_numConst {a : Admin} {t : NumType} {c : Value}
    (h : adminToV a = .case "CONST" (.tuple [Vec.numTypeV t, c])) :
    ∃ b : BitVec t.width, a = (Val.num ⟨t, b⟩).toAdmin ∧ c = numV ⟨t, b⟩ := by
  rcases t with i | f
  · obtain ⟨b, rfl, rfl⟩ := IntNumeric.dec_intConst (t := i) (by rw [ntV_eq]; exact h)
    exact ⟨b, rfl, rfl⟩
  · obtain ⟨b, rfl, rfl⟩ := dec_floatConst h
    exact ⟨b, rfl, rfl⟩

/-- A float constant at the type bound to `nt`. -/
theorem floatConst_at {ρ : VarEnv} {a : Admin} {t : FloatType} {x : IL.Id}
    (hnt : ρ.findVal? "nt" = some (Vec.numTypeV (.float t))) (h : IntNumeric.OpAt ρ a "CONST" "nt" x) :
    ∃ b : BitVec t.width, a = .plain (.floatConst t b) ∧ ρ.findVal? x = some (floatV t b) := by
  obtain ⟨u, c, hu, hc, ha⟩ := h
  have hu' : u = Vec.numTypeV (.float t) := Option.some.inj (hu.symm.trans hnt)
  obtain ⟨b, rfl, rfl⟩ := dec_floatConst (hu' ▸ ha)
  exact ⟨b, rfl, hc⟩

/-- The operator of a float instruction `o (nt, op)`. -/
theorem floatOp_at {ρ : VarEnv} {i : Instr} {o : MixopS} {x : IL.Id} {nt opv : Value}
    (he : instrToV i = .case o (.tuple [nt, opv])) (h : IntNumeric.OpAt ρ (.plain i) o "nt" x) :
    ρ.findVal? "nt" = some nt ∧ ρ.findVal? x = some opv := by
  obtain ⟨u, v, hu, hv, ha⟩ := h
  have hp : u = nt ∧ v = opv := by
    have := ha.symm.trans he
    simpa only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true, true_and] using this
  exact ⟨hp.1 ▸ hu, hp.2 ▸ hv⟩

/-! ## Unary operators (46, 47) -/

/-- `unop-val`'s premise and right-hand side, at a float operator. -/
theorem unopValF_finish (hF : FloatB P B) {σ : List (IL.Id × Value)} {t : FloatType}
    {uop : FloatUnOp} {x : BitVec t.width} {w : Value} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (Vec.numTypeV (.float t)))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (floatV t x))
    (hop : (VarEnv.empty.bindVals σ).findVal? "unop" = some (Vec.fUnOpV uop))
    (hr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c"])]) w)
    (hp : ∀ pr ∈ [Prem.ifPr (.memE (.varE "c") (.callE "unop_" [.expA (.varE "nt"),
      .expA (.varE "unop"), .expA (.varE "c_1")]))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    ∃ z, floatUnOpP P t uop x z ∧ w = .list (adminsToV [.plain (.floatConst t z)]) := by
  obtain ⟨u, c, hu, hc, hw⟩ := IntNumeric.rhs_const_inv hr
  have hu' : u = Vec.numTypeV (.float t) := Option.some.inj (hu.symm.trans hnt)
  obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 (IntNumeric.prem_if hp)
  have hv₁' : v₁ = c := Option.some.inj ((evalExp_varE_iff.1 hv₁).symm.trans hc)
  have happ : Applies (simEnv B) "unop_" [.val (Vec.numTypeV (.float t)), .val (Vec.fUnOpV uop),
      .val (floatV t x)] v₂ :=
    (applies_iff_callDef rfl (evalArgs_three hnt hop hx)).2 (evalExp_callE_iff.1 hv₂)
  have hv₂eq : v₂ = unRes P t uop x := happ.unique (applies_unop_float hF t uop x)
  have hmem' : memValue c (unRes P t uop x) = .ok (.bool true) := by
    rw [← hv₁', ← hv₂eq]
    exact hmem
  have hm : c ∈ (bitsWhere t.width (floatUnOpP P t uop x)).map (floatV t) :=
    IntNumeric.memValue_list_true hmem'
  obtain ⟨z, hz, rfl⟩ := mem_map_bitsWhere.1 hm
  refine ⟨z, hz, ?_⟩
  rw [hw, hu']
  simp only [adminsToV, adminToV, Vec.instrToV_floatConst]
  rfl

/-- `unop-trap`'s premise never holds at a float operator: the result set is never empty. -/
theorem unopTrapF_finish (hF : FloatB P B) {σ : List (IL.Id × Value)} {t : FloatType}
    {uop : FloatUnOp} {x : BitVec t.width} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (Vec.numTypeV (.float t)))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (floatV t x))
    (hop : (VarEnv.empty.bindVals σ).findVal? "unop" = some (Vec.fUnOpV uop))
    (hp : ∀ pr ∈ [Prem.ifPr (.cmpE .eqOp .boolT (.callE "unop_" [.expA (.varE "nt"),
      .expA (.varE "unop"), .expA (.varE "c_1")]) (.listE []))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := IntNumeric.evalExp_eq_true (IntNumeric.prem_if hp)
  have happ : Applies (simEnv B) "unop_" [.val (Vec.numTypeV (.float t)), .val (Vec.fUnOpV uop),
      .val (floatV t x)] v :=
    (applies_iff_callDef rfl (evalArgs_three hnt hop hx)).2 (evalExp_callE_iff.1 hv₁)
  have hveq : v = unRes P t uop x := happ.unique (applies_unop_float hF t uop x)
  have hnil : v = .list [] := by
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hv₂
    rw [Equiv.Validation.evalExps_nil_iff.1 hvs]
  obtain ⟨z, hz⟩ := floatUnOpP_nonempty P t uop x
  have hm : floatV t z ∈ (bitsWhere t.width (floatUnOpP P t uop x)).map (floatV t) :=
    mem_map_bitsWhere.2 ⟨z, hz, rfl⟩
  have hl : (bitsWhere t.width (floatUnOpP P t uop x)).map (floatV t) = [] :=
    Value.list.inj (hveq.symm.trans hnil)
  exact absurd (hl ▸ hm) List.not_mem_nil

/-- The float unary operator sequence. -/
theorem unopF_dec {ρ : VarEnv} {a₁ : Admin} {t : FloatType} {uop : FloatUnOp}
    (h₁ : IntNumeric.OpAt ρ a₁ "CONST" "nt" "c_1") (h₂ : IntNumeric.OpAt ρ (.plain (.floatUnOp t uop)) "UNOP" "nt" "unop") :
    ∃ x : BitVec t.width, a₁ = .plain (.floatConst t x) ∧
      ρ.findVal? "nt" = some (Vec.numTypeV (.float t)) ∧ ρ.findVal? "c_1" = some (floatV t x) ∧
      ρ.findVal? "unop" = some (Vec.fUnOpV uop) := by
  obtain ⟨hnt, hop⟩ := floatOp_at (Vec.instrToV_floatUnOp t uop) h₂
  obtain ⟨x, rfl, hx⟩ := floatConst_at hnt h₁
  exact ⟨x, rfl, hnt, hx, hop⟩

/-- **`Step_pure/unop-val` (46), backward, every number type.** -/
theorem bwd_unopVal (hI : IntNumeric.IntB B) (hF : FloatB P B) {s : Store H} {f : Frame}
    {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 46 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := IntNumeric.fires_body (IntNumeric.hasNumericRules_simEnv B).unopVal hf
  obtain ⟨hl, hr⟩ := IntNumeric.evalExp_tup2_inv he
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := IntNumeric.list2_inv hl
  rcases IntNumeric.unop_dec h₁ h₂ with ⟨t, uop, x, hv, rfl, rfl, hnt, hx, hop⟩ | ⟨t, uop, rfl⟩
  · exact ⟨_, IntNumeric.unopVal_finish hI hv hnt hx hop hr hp, .numeric .intUnOp⟩
  · obtain ⟨x, rfl, hnt, hx, hop⟩ := unopF_dec h₁ h₂
    obtain ⟨z, hz, hw⟩ := unopValF_finish hF hnt hx hop hr hp
    exact ⟨_, hw, .numeric (.floatUnOp hz)⟩

/-- **`Step_pure/unop-trap` (47), backward**: it never fires at the image of a Core sequence. -/
theorem bwd_unopTrap (hI : IntNumeric.IntB B) (hF : FloatB P B) {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 47 (.tuple [.list (adminsToV is), w])) : False := by
  obtain ⟨σ, -, he, hp⟩ := IntNumeric.fires_body (IntNumeric.hasNumericRules_simEnv B).unopTrap hf
  obtain ⟨hl, -⟩ := IntNumeric.evalExp_tup2_inv he
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := IntNumeric.list2_inv hl
  rcases IntNumeric.unop_dec h₁ h₂ with ⟨t, uop, x, hv, rfl, rfl, hnt, hx, hop⟩ | ⟨t, uop, rfl⟩
  · exact IntNumeric.unopTrap_finish hI hv hnt hx hop hp
  · obtain ⟨x, rfl, hnt, hx, hop⟩ := unopF_dec h₁ h₂
    exact unopTrapF_finish hF hnt hx hop hp

/-! ## Binary operators (48, 49) and comparisons (51) -/

/-- The float binary operator or comparison sequence. -/
theorem binF_dec {ρ : VarEnv} {a₁ a₂ : Admin} {i : Instr} {o : MixopS} {y : IL.Id}
    {t : FloatType} {opv : Value}
    (he : instrToV i = .case o (.tuple [Vec.numTypeV (.float t), opv]))
    (h₁ : IntNumeric.OpAt ρ a₁ "CONST" "nt" "c_1") (h₂ : IntNumeric.OpAt ρ a₂ "CONST" "nt" "c_2")
    (h₃ : IntNumeric.OpAt ρ (.plain i) o "nt" y) :
    ∃ x x' : BitVec t.width, a₁ = .plain (.floatConst t x) ∧ a₂ = .plain (.floatConst t x') ∧
      ρ.findVal? "nt" = some (Vec.numTypeV (.float t)) ∧ ρ.findVal? "c_1" = some (floatV t x) ∧
      ρ.findVal? "c_2" = some (floatV t x') ∧ ρ.findVal? y = some opv := by
  obtain ⟨hnt, hop⟩ := floatOp_at he h₃
  obtain ⟨x, rfl, hx⟩ := floatConst_at hnt h₁
  obtain ⟨x', rfl, hx'⟩ := floatConst_at hnt h₂
  exact ⟨x, x', rfl, rfl, hnt, hx, hx', hop⟩

/-- `binop-val`'s premise and right-hand side, at a float operator. -/
theorem binopValF_finish (hF : FloatB P B) {σ : List (IL.Id × Value)} {t : FloatType}
    {bop : FloatBinOp} {x y : BitVec t.width} {w : Value} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (Vec.numTypeV (.float t)))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (floatV t x))
    (hy : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (floatV t y))
    (hop : (VarEnv.empty.bindVals σ).findVal? "binop" = some (Vec.fBinOpV bop))
    (hr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c"])]) w)
    (hp : ∀ pr ∈ [Prem.ifPr (.memE (.varE "c") (.callE "binop_" [.expA (.varE "nt"),
      .expA (.varE "binop"), .expA (.varE "c_1"), .expA (.varE "c_2")]))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    ∃ z, floatBinOpP P t bop x y z ∧ w = .list (adminsToV [.plain (.floatConst t z)]) := by
  obtain ⟨u, c, hu, hc, hw⟩ := IntNumeric.rhs_const_inv hr
  have hu' : u = Vec.numTypeV (.float t) := Option.some.inj (hu.symm.trans hnt)
  obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 (IntNumeric.prem_if hp)
  have hv₁' : v₁ = c := Option.some.inj ((evalExp_varE_iff.1 hv₁).symm.trans hc)
  have happ : Applies (simEnv B) "binop_" [.val (Vec.numTypeV (.float t)),
      .val (Vec.fBinOpV bop), .val (floatV t x), .val (floatV t y)] v₂ :=
    (applies_iff_callDef rfl (evalArgs_four hnt hop hx hy)).2 (evalExp_callE_iff.1 hv₂)
  have hv₂eq : v₂ = binRes P t bop x y := happ.unique (applies_binop_float hF t bop x y)
  have hmem' : memValue c (binRes P t bop x y) = .ok (.bool true) := by
    rw [← hv₁', ← hv₂eq]
    exact hmem
  have hm : c ∈ (bitsWhere t.width (floatBinOpP P t bop x y)).map (floatV t) :=
    IntNumeric.memValue_list_true hmem'
  obtain ⟨z, hz, rfl⟩ := mem_map_bitsWhere.1 hm
  refine ⟨z, hz, ?_⟩
  rw [hw, hu']
  simp only [adminsToV, adminToV, Vec.instrToV_floatConst]
  rfl

/-- `binop-trap`'s premise never holds at a float operator. -/
theorem binopTrapF_finish (hF : FloatB P B) {σ : List (IL.Id × Value)} {t : FloatType}
    {bop : FloatBinOp} {x y : BitVec t.width} {els : Prop}
    (hnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (Vec.numTypeV (.float t)))
    (hx : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (floatV t x))
    (hy : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (floatV t y))
    (hop : (VarEnv.empty.bindVals σ).findVal? "binop" = some (Vec.fBinOpV bop))
    (hp : ∀ pr ∈ [Prem.ifPr (.cmpE .eqOp .boolT (.callE "binop_" [.expA (.varE "nt"),
      .expA (.varE "binop"), .expA (.varE "c_1"), .expA (.varE "c_2")]) (.listE []))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) : False := by
  obtain ⟨v, hv₁, hv₂⟩ := IntNumeric.evalExp_eq_true (IntNumeric.prem_if hp)
  have happ : Applies (simEnv B) "binop_" [.val (Vec.numTypeV (.float t)),
      .val (Vec.fBinOpV bop), .val (floatV t x), .val (floatV t y)] v :=
    (applies_iff_callDef rfl (evalArgs_four hnt hop hx hy)).2 (evalExp_callE_iff.1 hv₁)
  have hveq : v = binRes P t bop x y := happ.unique (applies_binop_float hF t bop x y)
  have hnil : v = .list [] := by
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hv₂
    rw [Equiv.Validation.evalExps_nil_iff.1 hvs]
  obtain ⟨z, hz⟩ := floatBinOpP_nonempty P t bop x y
  have hm : floatV t z ∈ (bitsWhere t.width (floatBinOpP P t bop x y)).map (floatV t) :=
    mem_map_bitsWhere.2 ⟨z, hz, rfl⟩
  have hl : (bitsWhere t.width (floatBinOpP P t bop x y)).map (floatV t) = [] :=
    Value.list.inj (hveq.symm.trans hnil)
  exact absurd (hl ▸ hm) List.not_mem_nil

/-- **`Step_pure/binop-val` (48), backward, every number type.** -/
theorem bwd_binopVal (hI : IntNumeric.IntB B) (hF : FloatB P B) {s : Store H} {f : Frame}
    {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 48 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := IntNumeric.fires_body (IntNumeric.hasNumericRules_simEnv B).binopVal hf
  obtain ⟨hl, hr⟩ := IntNumeric.evalExp_tup2_inv he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := IntNumeric.list3_inv hl
  rcases IntNumeric.binop_dec h₁ h₂ h₃ with ⟨t, bop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩ |
    ⟨t, bop, rfl⟩
  · obtain ⟨z, hz, rfl⟩ := IntNumeric.binopVal_finish hI hnt hx hy hop hr hp
    exact ⟨_, rfl, .numeric (.intBinOp hz)⟩
  · obtain ⟨x, y, rfl, rfl, hnt, hx, hy, hop⟩ := binF_dec (Vec.instrToV_floatBinOp t bop) h₁ h₂ h₃
    obtain ⟨z, hz, hw⟩ := binopValF_finish hF hnt hx hy hop hr hp
    exact ⟨_, hw, .numeric (.floatBinOp hz)⟩

/-- **`Step_pure/binop-trap` (49), backward, every number type**: only integer division and
remainder trap. -/
theorem bwd_binopTrap (hI : IntNumeric.IntB B) (hF : FloatB P B) {s : Store H} {f : Frame}
    {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 49 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := IntNumeric.fires_body (IntNumeric.hasNumericRules_simEnv B).binopTrap hf
  obtain ⟨hl, hr⟩ := IntNumeric.evalExp_tup2_inv he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := IntNumeric.list3_inv hl
  rcases IntNumeric.binop_dec h₁ h₂ h₃ with ⟨t, bop, x, y, rfl, rfl, rfl, hnt, hx, hy, hop⟩ |
    ⟨t, bop, rfl⟩
  · obtain ⟨e, he⟩ := IntNumeric.binopTrap_finish hI hnt hx hy hop hp
    exact ⟨[.trap], IntNumeric.rhs_trap_inv hr, .numeric (.intBinOpTrap he)⟩
  · obtain ⟨x, y, rfl, rfl, hnt, hx, hy, hop⟩ := binF_dec (Vec.instrToV_floatBinOp t bop) h₁ h₂ h₃
    exact (binopTrapF_finish hF hnt hx hy hop hp).elim

/-- **`Step_pure/relop` (51), backward, every number type.** -/
theorem bwd_relop (hF : FloatB P B) {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 51 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := IntNumeric.fires_body (IntNumeric.hasNumericRules_simEnv B).relop hf
  obtain ⟨hl, hr⟩ := IntNumeric.evalExp_tup2_inv he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := IntNumeric.list3_inv hl
  rcases IntNumeric.relop_dec h₁ h₂ h₃ with ⟨t, rop, x, y, rfl, rfl, rfl, -⟩ | ⟨t, rop, rfl⟩
  · rcases IntNumeric.bwd_relop (P := P) (host := host) (s := s) (f := f) hf with h | ⟨_, _, hm⟩
    · exact h
    · exact absurd hm (by simp)
  · obtain ⟨x, y, rfl, rfl, hnt, hx, hy, hop⟩ :=
      binF_dec (Vec.instrToV_floatRelOp t rop) h₁ h₂ h₃
    have hw := IntNumeric.cmp_finish (r := Vec.i32NV (floatRelOp t rop x y)) (fun v hv =>
      ((applies_iff_callDef rfl (evalArgs_four hnt hop hx hy)).2
        (evalExp_callE_iff.1 hv)).unique (applies_relop_float hF t rop x y)) hr hp
    exact ⟨[constI32 (floatRelOp t rop x y)], hw, .numeric .floatRelOp⟩

/-! ## Conversions (52, 53) -/

/-- `o (x, y, z)` with variables, inverted. -/
theorem evalExp_op3Vars_inv {env : Env} {ρ : VarEnv} {op : MixopS} {x y z : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE op (.tupE [.varE x, .varE y, .varE z])) v) :
    ∃ a b c, ρ.findVal? x = some a ∧ ρ.findVal? y = some b ∧ ρ.findVal? z = some c ∧
      v = .case op (.tuple [a, b, c]) := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨a, xs, rfl, ha, hxs⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, ys, rfl, hb, hys⟩ := Equiv.Validation.evalExps_cons_iff.1 hxs
  obtain ⟨c, zs, rfl, hc, hzs⟩ := Equiv.Validation.evalExps_cons_iff.1 hys
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hzs
  exact ⟨a, b, c, evalExp_varE_iff.1 ha, evalExp_varE_iff.1 hb, evalExp_varE_iff.1 hc, rfl⟩

/-- An administrative instruction with the head `CVTOP` is a conversion. -/
theorem head_cvtop {a : Admin} (h : Typing.adminHead a = "CVTOP") :
    ∃ op, a = .plain (.convert op) := by
  revert h
  admin_head_inv

/-- The image of a conversion instruction, read back. -/
theorem convert_image {op : ConvertOp} {u₂ u₁ o : Value}
    (h : adminToV (.plain (.convert op)) = .case "CVTOP" (.tuple [u₂, u₁, o])) :
    u₂ = Vec.numTypeV op.target ∧ u₁ = Vec.numTypeV op.source ∧ o = Vec.cvtOpV op := by
  have h' : Vec.convertInstrV op = .case "CVTOP" (.tuple [u₂, u₁, o]) := h
  simp only [Vec.convertInstrV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
    true_and] at h'
  exact ⟨h'.1.symm, h'.2.1.symm, h'.2.2.symm⟩

/-- The left-hand side of `cvtop-val`/`cvtop-trap` at the image of a Core sequence. -/
theorem cvt_lhs_inv {ρ : VarEnv} {is : List Admin}
    (h : EvalExp (simEnv B) ρ (.listE [.caseE "CONST" (.tupE [.varE "nt_1", .varE "c_1"]),
      .caseE "CVTOP" (.tupE [.varE "nt_2", .varE "nt_1", .varE "cvtop"])])
      (.list (adminsToV is))) :
    ∃ (op : ConvertOp) (x : BitVec op.source.width),
      is = [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] ∧
      ρ.findVal? "nt_1" = some (Vec.numTypeV op.source) ∧
      ρ.findVal? "nt_2" = some (Vec.numTypeV op.target) ∧
      ρ.findVal? "cvtop" = some (Vec.cvtOpV op) ∧ ρ.findVal? "c_1" = some (numV ⟨op.source, x⟩) := by
  obtain ⟨vs, hvs, h2⟩ := IntNumeric.evalExp_listE_inv h
  rcases h2 with _ | ⟨e₁, _ | ⟨e₂, h2⟩⟩
  cases h2
  obtain ⟨a₁, a₂, rfl, ha₁, ha₂⟩ := IntNumeric.adminsToV_eq_two (Value.list.inj hvs)
  obtain ⟨u₂, u₁, o, hu₂, hu₁, ho, he₂⟩ := evalExp_op3Vars_inv (ha₂ ▸ e₂)
  obtain ⟨op, rfl⟩ := head_cvtop (Typing.adminToV_case he₂).symm
  obtain ⟨rfl, rfl, rfl⟩ := convert_image he₂
  obtain ⟨u, c, hu, hc, ha⟩ := IntNumeric.opAt_of_eval (ha₁ ▸ e₁)
  have hu' : u = Vec.numTypeV op.source := Option.some.inj (hu.symm.trans hu₁)
  obtain ⟨x, rfl, rfl⟩ := dec_numConst (hu' ▸ ha)
  exact ⟨op, x, rfl, hu₁, hu₂, ho, hc⟩

/-- `cvtop-val`'s premise and right-hand side. -/
theorem cvtopVal_finish (hF : FloatB P B) {σ : List (IL.Id × Value)} {op : ConvertOp}
    {x : BitVec op.source.width} {w : Value} {els : Prop}
    (h₁ : (VarEnv.empty.bindVals σ).findVal? "nt_1" = some (Vec.numTypeV op.source))
    (h₂ : (VarEnv.empty.bindVals σ).findVal? "nt_2" = some (Vec.numTypeV op.target))
    (h₃ : (VarEnv.empty.bindVals σ).findVal? "cvtop" = some (Vec.cvtOpV op))
    (h₄ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV ⟨op.source, x⟩))
    (hr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt_2", .varE "c"])]) w)
    (hp : ∀ pr ∈ [Prem.ifPr (.memE (.varE "c") (.callE "cvtop__" [.expA (.varE "nt_1"),
      .expA (.varE "nt_2"), .expA (.varE "cvtop"), .expA (.varE "c_1")]))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    ∃ z, convertP P op x (.ok z) ∧ w = .list (adminsToV [(Val.num ⟨op.target, z⟩).toAdmin]) := by
  obtain ⟨u, c, hu, hc, hw⟩ := IntNumeric.rhs_const_inv hr
  have hu' : u = Vec.numTypeV op.target := Option.some.inj (hu.symm.trans h₂)
  obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 (IntNumeric.prem_if hp)
  have hv₁' : v₁ = c := Option.some.inj ((evalExp_varE_iff.1 hv₁).symm.trans hc)
  have happ : Applies (simEnv B) "cvtop__" (cvtArgs op x) v₂ :=
    (applies_iff_callDef rfl (evalArgs_four h₁ h₂ h₃ h₄)).2 (evalExp_callE_iff.1 hv₂)
  obtain ⟨L, hL, hok⟩ := cvtop_agree hF op x
  have hv₂eq : v₂ = .list L := happ.unique hL
  have hmem' : memValue c (.list L) = .ok (.bool true) := by
    rw [← hv₁', ← hv₂eq]
    exact hmem
  obtain ⟨z, hz, rfl⟩ := (hok.1 c).1 (IntNumeric.memValue_list_true hmem')
  refine ⟨z, hz, ?_⟩
  rw [hw, hu']
  simp only [adminsToV, Vec.adminToV_valNum]
  rfl

/-- **`Step_pure/cvtop-val` (52), backward**, every Core conversion. -/
theorem bwd_cvtopVal (hF : FloatB P B) {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 52 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := IntNumeric.fires_body (IntNumeric.hasNumericRules_simEnv B).cvtopVal hf
  obtain ⟨hl, hr⟩ := IntNumeric.evalExp_tup2_inv he
  obtain ⟨op, x, rfl, h₁, h₂, h₃, h₄⟩ := cvt_lhs_inv hl
  obtain ⟨z, hz, hw⟩ := cvtopVal_finish hF h₁ h₂ h₃ h₄ hr hp
  exact ⟨_, hw, .numeric (.convert hz)⟩

/-- `cvtop-trap`'s premise: the conversion traps. -/
theorem cvtopTrap_finish (hF : FloatB P B) {σ : List (IL.Id × Value)} {op : ConvertOp}
    {x : BitVec op.source.width} {els : Prop}
    (h₁ : (VarEnv.empty.bindVals σ).findVal? "nt_1" = some (Vec.numTypeV op.source))
    (h₂ : (VarEnv.empty.bindVals σ).findVal? "nt_2" = some (Vec.numTypeV op.target))
    (h₃ : (VarEnv.empty.bindVals σ).findVal? "cvtop" = some (Vec.cvtOpV op))
    (h₄ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV ⟨op.source, x⟩))
    (hp : ∀ pr ∈ [Prem.ifPr (.cmpE .eqOp .boolT (.callE "cvtop__" [.expA (.varE "nt_1"),
      .expA (.varE "nt_2"), .expA (.varE "cvtop"), .expA (.varE "c_1")]) (.listE []))],
      PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els
        (VarEnv.empty.bindVals σ) pr) :
    ∃ e, convertP P op x (.error e) := by
  obtain ⟨v, hv₁, hv₂⟩ := IntNumeric.evalExp_eq_true (IntNumeric.prem_if hp)
  have happ : Applies (simEnv B) "cvtop__" (cvtArgs op x) v :=
    (applies_iff_callDef rfl (evalArgs_four h₁ h₂ h₃ h₄)).2 (evalExp_callE_iff.1 hv₁)
  obtain ⟨L, hL, hok⟩ := cvtop_agree hF op x
  have hveq : v = .list L := happ.unique hL
  have hnil : v = .list [] := by
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hv₂
    rw [Equiv.Validation.evalExps_nil_iff.1 hvs]
  exact hok.2.1 (Value.list.inj (hveq.symm.trans hnil))

/-- **`Step_pure/cvtop-trap` (53), backward**, every Core conversion. -/
theorem bwd_cvtopTrap (hF : FloatB P B) {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 53 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := IntNumeric.fires_body (IntNumeric.hasNumericRules_simEnv B).cvtopTrap hf
  obtain ⟨hl, hr⟩ := IntNumeric.evalExp_tup2_inv he
  obtain ⟨op, x, rfl, h₁, h₂, h₃, h₄⟩ := cvt_lhs_inv hl
  obtain ⟨e, he⟩ := cvtopTrap_finish hF h₁ h₂ h₃ h₄ hp
  exact ⟨[.trap], IntNumeric.rhs_trap_inv hr, .numeric (.convertTrap he)⟩

end Silmaril.Wasm.SpecTec.Sim.Floats
