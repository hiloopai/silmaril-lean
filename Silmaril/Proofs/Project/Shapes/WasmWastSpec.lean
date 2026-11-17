module

public import Silmaril.Project.Shapes.WasmWastSpec.Defs
public import Silmaril.Wasm.Execution.StraightLine.Thms
public import Silmaril.Wasm.Execution.Core.SpecProfile
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
import Silmaril.Proofs.Project.Shapes.WasmWast
import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# Proofs: WAST commands under the specification profile

* `canonicalBits_of_f32`, …: the repository's NaN classes (`F32.IsCanonicalNaN`,
  `F32.IsArithmeticNaN`, …) are contained in the specification's patterns (`CanonicalBits`,
  `ArithmeticBits`);
* `unSet_sound`, `binSet_sound`, `convSet_sound`: every member of `floatUnOpRel`,
  `floatBinOpRel`, `convertRel` is in the class `unSet`, `binSet`, `convSet`;
* `numericSet?_sound`: every result of `NumericStep (Profile.spec nd r) (vals args ++ [op])` is
  in `numericSet? op args`, and there is one;
* `sub_sound`: a class contained in an expectation (`NumSet.sub`) gives the outcome;
* `scriptHoldsS_of_kernel`: `scriptSK m cmds = true` gives `ScriptHoldsS nd r m cmds` for every
  `nd` and `r`, through `StraightLine.nf`, `reaches`, `not_diverges`, `extends_nf`;
* `reaches_spec`: a run at `profile o` to a result is a run at `Profile.spec nd {}`
  (`Steps.deterministic_refines_spec`), so `Reaches` gives `ReachesS`.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.WasmWastSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Numerics Silmaril.Numeric.Ieee754
  Silmaril.Project.Shapes.WasmWast Silmaril.Project.Shapes.WasmWastSpec
open Silmaril.Wasm.SingleThreaded.Exec (codeOutcome?)

/-! ## NaN classes -/

theorem isNaN_f32 {b : BitVec 32} (h : (asF32 b).IsNaN) :
    b.toNat / 2 ^ 23 % 2 ^ 8 = 2 ^ 8 - 1 := by
  simp only [F32.IsNaN, classify32, classify, decode32, decode, field, maxExponentField,
    binary32ExponentBits, binary32SignificandBits, asF32, UInt32.toNat_ofBitVec] at h
  split_ifs at h; simp_all

theorem isNaN_f64 {b : BitVec 64} (h : (asF64 b).IsNaN) :
    b.toNat / 2 ^ 52 % 2 ^ 11 = 2 ^ 11 - 1 := by
  simp only [F64.IsNaN, classify64, classify, decode64, decode, field, maxExponentField,
    binary64ExponentBits, binary64SignificandBits, asF64, UInt64.toNat_ofBitVec] at h
  split_ifs at h; simp_all

theorem canonicalBits_of_f32 {b : BitVec 32} (h : (asF32 b).IsCanonicalNaN) :
    CanonicalBits .f32 b.toNat := by
  obtain ⟨-, h⟩ := h
  have hc : (F32.canonicalNaN.bits &&& 0x7fffffff) = 0x7fc00000 := by decide +kernel
  rw [hc] at h
  have h' := congrArg UInt32.toNat h
  rw [UInt32.toNat_and, show (0x7fc00000 : UInt32).toNat = 0x7fc00000 from rfl,
    show (0x7fffffff : UInt32).toNat = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at h'
  simp only [asF32, UInt32.toNat_ofBitVec] at h'
  simp only [CanonicalBits, sigBits, expBits]
  constructor <;> omega

theorem canonicalBits_of_f64 {b : BitVec 64} (h : (asF64 b).IsCanonicalNaN) :
    CanonicalBits .f64 b.toNat := by
  obtain ⟨-, h⟩ := h
  have hc : (F64.canonicalNaN.bits &&& 0x7fffffffffffffff) = 0x7ff8000000000000 := by
    decide +kernel
  rw [hc] at h
  have h' := congrArg UInt64.toNat h
  rw [UInt64.toNat_and, show (0x7ff8000000000000 : UInt64).toNat = 0x7ff8000000000000 from rfl,
    show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h'
  simp only [asF64, UInt64.toNat_ofBitVec] at h'
  simp only [CanonicalBits, sigBits, expBits]
  constructor <;> omega

theorem arithmeticBits_of_f32 {b : BitVec 32} (h : (asF32 b).IsArithmeticNaN) :
    ArithmeticBits .f32 b.toNat := by
  obtain ⟨hn, h⟩ := h
  have := isNaN_f32 hn
  simp only [asF32, UInt32.toNat_ofBitVec, binary32SignificandBits] at h
  exact ⟨this, by simpa [sigBits] using h⟩

theorem arithmeticBits_of_f64 {b : BitVec 64} (h : (asF64 b).IsArithmeticNaN) :
    ArithmeticBits .f64 b.toNat := by
  obtain ⟨hn, h⟩ := h
  have := isNaN_f64 hn
  simp only [asF64, UInt64.toNat_ofBitVec, binary64SignificandBits] at h
  exact ⟨this, by simpa [sigBits] using h⟩

/-- Every canonical NaN is an arithmetic NaN. -/
theorem arithmeticBits_of_canonicalBits {t : FloatType} {n : Nat} (h : CanonicalBits t n) :
    ArithmeticBits t n :=
  ⟨h.1, h.2 ▸ le_rfl⟩

/-! ## Result classes -/

/-- The class of a NaN-or-exact result relation, `f32`. -/
def cls32 (isNaN canon : Bool) (r : BitVec 32) : NumSet :=
  if isNaN then nanSet .f32 canon else .exact (.num ⟨.float .f32, r⟩)

/-- The class of a NaN-or-exact result relation, `f64`. -/
def cls64 (isNaN canon : Bool) (r : BitVec 64) : NumSet :=
  if isNaN then nanSet .f64 canon else .exact (.num ⟨.float .f64, r⟩)

theorem mem_cls32 {res : F32} {canon : Prop} [Decidable canon] {z : BitVec 32}
    (h : if res.IsNaN then (if canon then (asF32 z).IsCanonicalNaN else (asF32 z).IsArithmeticNaN)
      else asF32 z = res) :
    (cls32 (decide res.IsNaN) (decide canon) res.bits.toBitVec).Mem [.plain (.floatConst .f32 z)] := by
  unfold cls32 nanSet
  by_cases hn : res.IsNaN
  · by_cases hc : canon
    · simp only [hn, hc, ite_true, decide_true] at h ⊢
      exact ⟨z, rfl, canonicalBits_of_f32 h⟩
    · simp only [hn, hc, ite_true, ite_false, decide_true, decide_false] at h ⊢
      exact ⟨z, rfl, arithmeticBits_of_f32 h⟩
  · simp only [hn, ite_false, decide_false] at h ⊢
    subst h
    rfl

theorem mem_cls64 {res : F64} {canon : Prop} [Decidable canon] {z : BitVec 64}
    (h : if res.IsNaN then (if canon then (asF64 z).IsCanonicalNaN else (asF64 z).IsArithmeticNaN)
      else asF64 z = res) :
    (cls64 (decide res.IsNaN) (decide canon) res.bits.toBitVec).Mem [.plain (.floatConst .f64 z)] := by
  unfold cls64 nanSet
  by_cases hn : res.IsNaN
  · by_cases hc : canon
    · simp only [hn, hc, ite_true, decide_true] at h ⊢
      exact ⟨z, rfl, canonicalBits_of_f64 h⟩
    · simp only [hn, hc, ite_true, ite_false, decide_true, decide_false] at h ⊢
      exact ⟨z, rfl, arithmeticBits_of_f64 h⟩
  · simp only [hn, ite_false, decide_false] at h ⊢
    subst h
    rfl

/-- Every member of `floatUnOpRel t op x` is in `unSet t op x`. -/
theorem unSet_sound {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
    (h : floatUnOpRel t op x z) : (unSet t op x).Mem [.plain (.floatConst t z)] := by
  cases op
  case abs | neg => exact congrArg (fun z => [Admin.plain (.floatConst t z)]) h
  all_goals
    cases t
    · have := mem_cls32 h
      unfold cls32 at this
      unfold unSet
      split_ifs at this ⊢ <;> simp_all [floatUnOp]
    · have := mem_cls64 h
      unfold cls64 at this
      unfold unSet
      split_ifs at this ⊢ <;> simp_all [floatUnOp]

/-- Every member of `floatBinOpRel t op x y` is in `binSet t op x y`. -/
theorem binSet_sound {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
    (h : floatBinOpRel t op x y z) : (binSet t op x y).Mem [.plain (.floatConst t z)] := by
  cases op
  case copysign => exact congrArg (fun z => [Admin.plain (.floatConst t z)]) h
  all_goals
    cases t
    · have := mem_cls32 h
      unfold cls32 at this
      unfold binSet
      split_ifs at this ⊢ <;> simp_all [floatBinOp]
    · have := mem_cls64 h
      unfold cls64 at this
      unfold binSet
      split_ifs at this ⊢ <;> simp_all [floatBinOp]

/-- The code of a conversion result. -/
def convCode (op : ConvertOp) : Except FloatTrap (NumValue op.target) → List Admin
  | .ok z => [(Val.num ⟨op.target, z⟩).toAdmin]
  | .error _ => [.trap]

/-- Every member of `convertRel op x` is in `convSet op x`. -/
theorem convSet_sound {op : ConvertOp} {x : BitVec op.source.width}
    {res : Except FloatTrap (NumValue op.target)} (h : convertRel op x res) :
    (convSet op x).Mem (convCode op res) := by
  cases op
  case demote =>
    cases res with
    | ok y =>
      have := mem_cls32 (z := y) h
      unfold cls32 at this
      simp only [decide_eq_true_eq] at this
      exact this
    | error e => simp [convertRel, convert] at h
  case promote =>
    cases res with
    | ok y =>
      have := mem_cls64 (z := y) h
      unfold cls64 at this
      simp only [decide_eq_true_eq] at this
      exact this
    | error e => simp [convertRel, convert] at h
  all_goals
    simp only [convertRel] at h
    subst h
    unfold convSet
    cases hc : convert _ x <;> simp only [hc, convCode] <;> rfl

/-! ## Numeric steps under `Profile.spec` -/

section Spec

variable {nd : Bool} {r : RelaxedChoice}

theorem inv_floatUnOp {t : FloatType} {op : FloatUnOp} {x : BitVec t.width} {is' : List Admin}
    (h : NumericStep (Profile.spec nd r) [.plain (.floatConst t x), .plain (.floatUnOp t op)] is') :
    ∃ z, floatUnOpRel t op x z ∧ is' = [.plain (.floatConst t z)] := by
  generalize hl : [Admin.plain (.floatConst t x), .plain (.floatUnOp t op)] = l at h
  cases h with
  | floatUnOp hz =>
    simp only [List.cons.injEq, Admin.plain.injEq, Instr.floatConst.injEq,
      Instr.floatUnOp.injEq, and_true] at hl
    obtain ⟨⟨rfl, hx⟩, -, rfl⟩ := hl
    cases hx
    exact ⟨_, hz, rfl⟩
  | _ => simp_all [Val.toAdmin]

theorem inv_floatBinOp {t : FloatType} {op : FloatBinOp} {x y : BitVec t.width}
    {is' : List Admin}
    (h : NumericStep (Profile.spec nd r)
      [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatBinOp t op)] is') :
    ∃ z, floatBinOpRel t op x y z ∧ is' = [.plain (.floatConst t z)] := by
  generalize hl : [Admin.plain (.floatConst t x), .plain (.floatConst t y),
    .plain (.floatBinOp t op)] = l at h
  cases h with
  | floatBinOp hz =>
    simp only [List.cons.injEq, Admin.plain.injEq, Instr.floatConst.injEq,
      Instr.floatBinOp.injEq, and_true] at hl
    obtain ⟨⟨rfl, hx⟩, ⟨-, hy⟩, -, rfl⟩ := hl
    cases hx
    cases hy
    exact ⟨_, hz, rfl⟩
  | _ => simp_all [Val.toAdmin]

theorem inv_floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width}
    {is' : List Admin}
    (h : NumericStep (Profile.spec nd r)
      [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatRelOp t op)] is') :
    is' = [constI32 (floatRelOp t op x y)] := by
  generalize hl : [Admin.plain (.floatConst t x), .plain (.floatConst t y),
    .plain (.floatRelOp t op)] = l at h
  cases h with
  | floatRelOp =>
    simp only [List.cons.injEq, Admin.plain.injEq, Instr.floatConst.injEq,
      Instr.floatRelOp.injEq, and_true] at hl
    obtain ⟨⟨rfl, hx⟩, ⟨-, hy⟩, -, rfl⟩ := hl
    cases hx
    cases hy
    rfl
  | _ => simp_all [Val.toAdmin]

theorem inv_convert {op : ConvertOp} {x : BitVec op.source.width} {is' : List Admin}
    (h : NumericStep (Profile.spec nd r) [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]
      is') :
    ∃ res, convertRel op x res ∧ is' = convCode op res := by
  generalize hl : [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] = l at h
  cases h with
  | convert hz =>
    rename_i op' x' z
    have h2 := congrArg List.getLast? hl
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq,
      Admin.plain.injEq, Instr.convert.injEq] at h2
    subst h2
    have h1 := congrArg List.head? hl
    simp only [List.head?_cons, Option.some.injEq] at h1
    have := (Det.val?_eq_some.mpr h1.symm)
    rw [Det.val?_eq_some.mpr rfl] at this
    simp only [Option.some.injEq, Val.num.injEq, NumVal.mk.injEq, heq_eq_eq, true_and] at this
    subst this
    exact ⟨_, hz, rfl⟩
  | convertTrap hz =>
    rename_i op' x' e
    have h2 := congrArg List.getLast? hl
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq,
      Admin.plain.injEq, Instr.convert.injEq] at h2
    subst h2
    have h1 := congrArg List.head? hl
    simp only [List.head?_cons, Option.some.injEq] at h1
    have := (Det.val?_eq_some.mpr h1.symm)
    rw [Det.val?_eq_some.mpr rfl] at this
    simp only [Option.some.injEq, Val.num.injEq, NumVal.mk.injEq, heq_eq_eq, true_and] at this
    subst this
    exact ⟨_, hz, rfl⟩
  | _ =>
    have h2 := congrArg List.getLast? hl
    simp at h2

/-- **The class of a numeric step under `Profile.spec`**: every result of
`NumericStep (Profile.spec nd r) (vals args ++ [op])` is in `numericSet? op args`, and there is
a result. -/
theorem numericSet?_sound {op : Instr} {args : List Val} {S : NumSet}
    (h : numericSet? op args = some S) :
    (∀ is', NumericStep (Profile.spec nd r) (vals args ++ [.plain op]) is' → S.Mem is') ∧
      ∃ is', NumericStep (Profile.spec nd r) (vals args ++ [.plain op]) is' := by
  unfold numericSet? at h
  split at h
  · rename_i t uop nt x
    split at h
    · rename_i hnt
      cases h
      subst hnt
      refine ⟨fun is' hs => ?_, ⟨_, .floatUnOp (floatUnOpRel_self t uop x)⟩⟩
      obtain ⟨z, hz, rfl⟩ := inv_floatUnOp hs
      exact unSet_sound hz
    · cases h
  · rename_i t bop nt₁ x nt₂ y
    split at h
    · rename_i hnt
      cases h
      obtain ⟨rfl, rfl⟩ := hnt
      refine ⟨fun is' hs => ?_, ⟨_, .floatBinOp (floatBinOpRel_self t bop x y)⟩⟩
      obtain ⟨z, hz, rfl⟩ := inv_floatBinOp hs
      exact binSet_sound hz
    · cases h
  · rename_i t rop nt₁ x nt₂ y
    split at h
    · rename_i hnt
      cases h
      obtain ⟨rfl, rfl⟩ := hnt
      refine ⟨fun is' hs => ?_, ⟨_, .floatRelOp⟩⟩
      rw [inv_floatRelOp hs]
      rfl
    · cases h
  · rename_i cop nt x
    split at h
    · rename_i hnt
      cases h
      subst hnt
      refine ⟨fun is' hs => ?_, ?_⟩
      · obtain ⟨res, hres, rfl⟩ := inv_convert hs
        exact convSet_sound hres
      · have hs := convertRel_self cop x
        cases hc : convert cop x with
        | ok z => exact ⟨_, .convert (by rw [hc] at hs; exact hs)⟩
        | error e => exact ⟨_, .convertTrap (by rw [hc] at hs; exact hs)⟩
    · cases h
  · cases h

end Spec

/-! ## Outcomes -/

theorem codeOutcome?_val (v : Val) : codeOutcome? [v.toAdmin] = some (.values [v]) := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> rfl

theorem codeOutcome?_trap : codeOutcome? [.trap] = some .trap := rfl

/-- A member of a class has a result as outcome. -/
theorem mem_outcome {S : NumSet} {is' : List Admin} (h : S.Mem is') :
    ∃ res, codeOutcome? is' = some res := by
  cases S with
  | exact v => rw [show is' = _ from h]; exact ⟨_, codeOutcome?_val v⟩
  | canonical t =>
    obtain ⟨b, rfl, -⟩ := h
    exact ⟨_, codeOutcome?_val (.num ⟨.float t, b⟩)⟩
  | arithmetic t =>
    obtain ⟨b, rfl, -⟩ := h
    exact ⟨_, codeOutcome?_val (.num ⟨.float t, b⟩)⟩
  | trap => rw [show is' = _ from h]; exact ⟨_, codeOutcome?_trap⟩

theorem subPat_sound {S : NumSet} {p : ValPat} (h : S.subPat p = true) {is' : List Admin}
    (hm : S.Mem is') : ∃ v, is' = [v.toAdmin] ∧ p.Matches v := by
  cases S with
  | exact v => exact ⟨v, hm, of_decide_eq_true h⟩
  | canonical t =>
    obtain ⟨b, rfl, hb⟩ := hm
    cases p <;> simp only [NumSet.subPat, beq_iff_eq, Bool.false_eq_true] at h
    · subst h; exact ⟨.num ⟨.float _, b⟩, rfl, rfl, hb⟩
    · subst h; exact ⟨.num ⟨.float _, b⟩, rfl, rfl, arithmeticBits_of_canonicalBits hb⟩
  | arithmetic t =>
    obtain ⟨b, rfl, hb⟩ := hm
    cases p <;> simp only [NumSet.subPat, beq_iff_eq, Bool.false_eq_true] at h
    subst h; exact ⟨.num ⟨.float _, b⟩, rfl, rfl, hb⟩
  | trap => simp [NumSet.subPat] at h

/-- **A class contained in an expectation**: every member's outcome is the expected one. -/
theorem sub_sound {S : NumSet} {e : ExpectS} (h : S.sub e = true) {is' : List Admin}
    (hm : S.Mem is') : ∃ res, codeOutcome? is' = some res ∧ e.Out res := by
  cases e with
  | trap =>
    simp only [NumSet.sub, beq_iff_eq] at h
    subst h
    rw [show is' = _ from hm]
    exact ⟨_, codeOutcome?_trap, rfl⟩
  | values ps =>
    match ps, h with
    | [p], h =>
      obtain ⟨v, rfl, hv⟩ := subPat_sound h hm
      exact ⟨_, codeOutcome?_val v, [v], rfl, .cons hv .nil⟩
    | [], h => simp [NumSet.sub] at h
    | _ :: _ :: _, h => simp [NumSet.sub] at h

/-! ## Commands -/

section Script

variable {nd : Bool} {r : RelaxedChoice}

/-- What the checker establishes about one action, from the store `s`. -/
structure Good (s : Store Nat) (mi : ModuleInst) (act : Action) (a : Nat) (S : NumSet) :
    Prop where
  ha : exportFunc? mi act.name = some a
  /-- every normal form is in the class, in the same store -/
  nf : ∀ (nd : Bool) (r : RelaxedChoice) c, InvokeNFS nd r s a act.args c →
    ∃ is', S.Mem is' ∧ c = ⟨s, {}, is'⟩
  /-- some normal form is reached -/
  ex : ∀ (nd : Bool) (r : RelaxedChoice), ∃ is', S.Mem is' ∧ InvokeNFS nd r s a act.args ⟨s, {}, is'⟩
  /-- no run is infinite, and every run extends to a normal form -/
  term : ∀ (nd : Bool) (r : RelaxedChoice),
    ¬ Diverges (Profile.spec nd r) Det.noHost (invoke s a act.args) ∧
    ∀ c', Steps (Profile.spec nd r) Det.noHost (invoke s a act.args) c' →
      ∃ c, Steps (Profile.spec nd r) Det.noHost c' c ∧
        ∀ x, ¬ Step (Profile.spec nd r) Det.noHost c x

theorem good_of {s : Store Nat} {mi : ModuleInst} {act : Action} {a : Nat} {fi : FuncInst Nat}
    {op : Instr} {S : NumSet} (ha : exportFunc? mi act.name = some a)
    (hf : s.funcs[a]? = some fi) (hfn : StraightLine.Fn fi act.args.length op)
    (hS : numericSet? op act.args = some S) : Good s mi act a S where
  ha := ha
  nf nd r c hc := by
    obtain ⟨hall, hex⟩ := numericSet?_sound (nd := nd) (r := r) hS
    obtain ⟨is', hn, rfl⟩ := StraightLine.nf hf hfn hex hc.1 hc.2
    exact ⟨is', hall _ hn, rfl⟩
  ex nd r := by
    obtain ⟨hall, is', hn⟩ := numericSet?_sound (nd := nd) (r := r) hS
    exact ⟨is', hall _ hn, StraightLine.reaches hf hfn hn,
      fun x => StraightLine.not_step_result hn⟩
  term nd r := ⟨StraightLine.not_diverges hf hfn, fun _ h => StraightLine.extends_nf hf hfn h⟩

theorem cmdSK_sound {s : Store Nat} {mi : ModuleInst} {cmd : CmdS}
    (h : cmdSK s mi cmd = true) :
    ∃ a S, Good s mi cmd.act a S ∧ ∀ e, cmd.expect = some e → S.sub e = true := by
  unfold cmdSK at h
  split at h
  · rename_i a ha
    split at h
    · rename_i fi hf
      split at h
      · rename_i op hop
        split at h
        · rename_i S hS
          refine ⟨a, S, good_of ha hf (StraightLine.fn?_sound hop) hS, fun e he => ?_⟩
          rw [he] at h
          exact h
        · cases h
      · cases h
    · cases h
  · cases h

/-- The store does not change along actions that the checker accepts. -/
theorem runS_eq {s : Store Nat} {mi : ModuleInst} :
    ∀ {pre : List Action} {s' : Store Nat}, (∀ act ∈ pre, ∃ a S, Good s mi act a S) →
      RunS nd r mi s pre s' → s' = s
  | [], _, _, .nil _ => rfl
  | act :: pre, s', hg, .cons ha hc _ h => by
    obtain ⟨a', S, hG⟩ := hg act (by simp)
    rw [hG.ha] at ha
    cases ha
    obtain ⟨is', -, rfl⟩ := hG.nf nd r _ hc
    exact runS_eq (fun act h => hg act (by simp [h])) h

/-- Actions that the checker accepts run from the store `s` back to `s`. -/
theorem runS_self {s : Store Nat} {mi : ModuleInst} :
    ∀ {pre : List Action}, (∀ act ∈ pre, ∃ a S, Good s mi act a S) → RunS nd r mi s pre s
  | [], _ => .nil _
  | act :: pre, hg => by
    obtain ⟨a, S, hG⟩ := hg act (by simp)
    obtain ⟨is', hm, hnf⟩ := hG.ex nd r
    obtain ⟨res, hres⟩ := mem_outcome hm
    exact .cons hG.ha hnf hres (runS_self (fun act h => hg act (by simp [h])))

theorem scriptAtS_iff {m : Module} {s : Store Nat} {mi : ModuleInst} (hI : Instance m s mi)
    {pre : List Action} (hg : ∀ act ∈ pre, ∃ a S, Good s mi act a S) {mi' : ModuleInst}
    {s' : Store Nat} : ScriptAtS nd r m pre mi' s' ↔ mi' = mi ∧ s' = s := by
  constructor
  · rintro ⟨s₀, hI', hrun⟩
    obtain ⟨rfl, rfl⟩ := WasmWast.instance_unique hI hI'
    exact ⟨rfl, runS_eq hg hrun⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, hI, runS_self hg⟩

/-- The claims of one command. -/
theorem cmd_holds {m : Module} {s : Store Nat} {mi : ModuleInst} (hI : Instance m s mi)
    {pre : List Action} (hg : ∀ act ∈ pre, ∃ a S, Good s mi act a S) {cmd : CmdS} {a : Nat}
    {S : NumSet} (hG : Good s mi cmd.act a S) (he : ∀ e, cmd.expect = some e → S.sub e = true) :
    cmd.Holds nd r m pre := by
  have hS : ScriptAtS nd r m pre mi s := (scriptAtS_iff hI hg).mpr ⟨rfl, rfl⟩
  have hterm : TerminatesAll nd r m pre cmd.act := by
    intro mi' s' a' hS' ha'
    obtain ⟨rfl, rfl⟩ := (scriptAtS_iff hI hg).mp hS'
    rw [hG.ha] at ha'
    cases ha'
    exact hG.term nd r
  have hout : ∀ e, cmd.expect = some e →
      ReachesS nd r m pre cmd.act e.Out ∧ AllS nd r m pre cmd.act e.Out := by
    intro e hce
    have hsub := he e hce
    refine ⟨?_, fun mi' s' a' c hS' ha' hc => ?_⟩
    · obtain ⟨is', hm, hnf⟩ := hG.ex nd r
      obtain ⟨res, hres, hR⟩ := sub_sound hsub hm
      exact ⟨mi, s, a, _, res, hS, hG.ha, hnf, hres, hR⟩
    · obtain ⟨rfl, rfl⟩ := (scriptAtS_iff hI hg).mp hS'
      rw [hG.ha] at ha'
      cases ha'
      obtain ⟨is', hm, rfl⟩ := hG.nf nd r c hc
      exact sub_sound hsub hm
  rcases cmd with ⟨act, _ | e⟩
  · exact hterm
  · cases e with
    | values ps => exact ⟨hout _ rfl, hterm⟩
    | trap => exact ⟨hout _ rfl, hterm⟩

/-- **One kernel evaluation proves every command of a script, under `Profile.spec nd r`, for
every `nd` and `r`.** -/
theorem scriptHoldsS_of_kernel {m : Module} {cmds : List CmdS} (h : scriptSK m cmds = true) :
    ScriptHoldsS nd r m cmds := by
  unfold scriptSK at h
  split at h
  · rename_i mt hv
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨himp, h⟩ := h
    split at h
    · rename_i s f hi
      have hI : Instance m s f.module :=
        ⟨⟨mt.exports, by rw [← himp]; exact validate?_sound hv⟩, f, hi, rfl⟩
      rw [List.all_eq_true] at h
      intro k cmd hk
      have hmem : ∀ act ∈ preS cmds k, ∃ a S, Good s f.module act a S := by
        intro act hact
        simp only [preS, List.mem_map] at hact
        obtain ⟨c, hc, rfl⟩ := hact
        obtain ⟨a, S, hG, -⟩ := cmdSK_sound (h c (List.mem_of_mem_take hc))
        exact ⟨a, S, hG⟩
      obtain ⟨a, S, hG, he⟩ := cmdSK_sound (h cmd (List.mem_of_getElem? hk))
      exact cmd_holds hI hmem hG he
    · cases h
  · cases h

theorem terminatesAll_of {m : Module} {cmds : List CmdS} (h : ScriptHoldsS nd r m cmds) (k : Nat)
    {cmd : CmdS} (hk : cmds[k]? = some cmd) : TerminatesAll nd r m (preS cmds k) cmd.act := by
  have := h k _ hk
  rcases cmd with ⟨act, _ | (_ | _)⟩
  · exact this
  · exact this.2
  · exact this.2

end Script

/-! ## From the deterministic profile: existence -/

theorem allowed_exact : ∀ vs : List Val, Allowed (vs.map .exact) vs
  | [] => .nil
  | _ :: vs => .cons rfl (allowed_exact vs)

section Lift

variable {o : GrowOracle} (nd : Bool)

/-- A result does not step, at any profile. -/
theorem not_step_of_outcome {P : Profile} {c : Config Nat} {res : Result}
    (hr : c.outcome? = some res) (x : Config Nat) : ¬ Step P Det.noHost c x := by
  rcases c with ⟨s, f, code⟩
  have hc : code = res.toAdmin := Config.outcome?_sound hr
  subst hc
  cases res with
  | values vs => exact Det.not_step_vals
  | trap => exact Det.not_step_trap
  | throw a => exact Det.not_step_throwing

theorem invokeNF_spec {s : Store Nat} {a : Nat} {args : List Val} {c : Config Nat}
    {res : Result} (h : InvokeNF o s a args c) (hr : c.outcome? = some res) :
    InvokeNFS nd {} s a args c :=
  ⟨Steps.deterministic_refines_spec nd h.1, not_step_of_outcome hr⟩

theorem run_spec {mi : ModuleInst} {s s' : Store Nat} {pre : List Action}
    (h : Run o mi s pre s') : RunS nd {} mi s pre s' := by
  induction h with
  | nil => exact .nil _
  | cons ha hc hr _ ih => exact .cons ha (invokeNF_spec nd hc hr) hr ih

/-- **A run at `profile o` to a result is a run at `Profile.spec nd {}`.** -/
theorem reaches_spec {m : Module} {pre : List Action} {act : Action} {res : Result}
    (h : Reaches o m pre act res) : ReachesS nd {} m pre act (· = res) := by
  obtain ⟨mi, s, a, c, ⟨s₀, hI, hrun⟩, ha, hc, hr⟩ := h
  exact ⟨mi, s, a, c, res, ⟨s₀, hI, run_spec nd hrun⟩, ha, invokeNF_spec nd hc hr, hr, rfl⟩

theorem returnsAllowedExists_of_returns {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : Returns o m pre act vs) :
    ReturnsAllowedExists nd {} m pre act (vs.map .exact) := by
  obtain ⟨mi, s, a, c, res, hS, ha, hc, hr, rfl⟩ := reaches_spec nd h
  exact ⟨mi, s, a, c, _, hS, ha, hc, hr, vs, rfl, allowed_exact vs⟩

end Lift

end Silmaril.Proofs.Project.Shapes.WasmWastSpec

end
