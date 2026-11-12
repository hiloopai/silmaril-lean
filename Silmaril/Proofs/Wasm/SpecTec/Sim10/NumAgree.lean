module

public import Silmaril.Wasm.SpecTec.Sim10.Num.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.NumCvt

/-!
# `NumAgree10`, discharged

With the dispatchers of `Sim10.NumInt` and `Sim10.NumCvt`, the 1.0 numeric agreement holds under
the builtins the 2.0 and 3.0 numerics take: the integer primitives (`IntB`) and the float and
conversion primitives of the profile (`FloatB P`). In particular it holds for the concrete
interpretation `Sim.Floats.floatIntB P` (`numAgree10_floatIntB`), at every profile.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB)

variable {B : Builtins} {P : Profile}

/-- A `$binop_` result list at an integer type, read as V2/V1's `intBinOp`. -/
theorem mem_ibinop {t : IntType} {op : IntBinOp} {x y : BitVec t.width} (c : Value) :
    c ∈ (ibinop_ t.width op x y).toList.map Silmaril.SpecTec.Equiv.bvV ↔
      ∃ z, intBinOp t op x y = .ok z ∧ c = Silmaril.SpecTec.Equiv.Execution.pctV z.toNat := by
  rw [ibinop_agree]
  cases intBinOp t op x y with
  | error e => simp [Except.toOption]
  | ok z =>
      simp only [Except.toOption, Option.toList_some, List.map_cons, List.map_nil,
        List.mem_singleton, Except.ok.injEq]
      exact ⟨fun hc => ⟨z, rfl, hc⟩, fun ⟨_, hz, hc⟩ => hz ▸ hc⟩

/-- **`NumAgree10` holds for the wasm-1.0 script** under `IntB` and `FloatB P`. -/
theorem numAgree10_simEnv10 (hI : IntB B) (hF : FloatB P B) : NumAgree10 (simEnv10 B) P where
  intUnOp t op x := applies_unop_int10 hI t op x
  floatUnOp t op x := ⟨_, applies_unop_float10 hF t op x, fun _ => Sim.Floats.mem_map_bitsWhere⟩
  intBinOp t op x y := ⟨_, applies_binop_int10 hI t op x y, mem_ibinop⟩
  floatBinOp t op x y :=
    ⟨_, applies_binop_float10 hF t op x y, fun _ => Sim.Floats.mem_map_bitsWhere⟩
  intTestOp t op x := applies_testop_int10 t op x
  intRelOp t op x y := applies_relop_int10 t op x y
  floatRelOp t op x y := applies_relop_float10 hF t op x y
  cvtOp op x := by
    obtain ⟨L, hL, h₁, h₂⟩ := applies_cvtop10 hF op x
    refine ⟨L, hL, fun c => ?_, h₂⟩
    rw [h₁ c]
    simp only [numV_eq_sim]

/-- In particular for the concrete interpretation of the primitives at the profile `P`. -/
theorem numAgree10_floatIntB : NumAgree10 (simEnv10 (Sim.Floats.floatIntB P)) P :=
  numAgree10_simEnv10 (Sim.Floats.intB_floatIntB P) (Sim.Floats.floatB_floatIntB P)

end Silmaril.Wasm.SpecTec.Sim10.Whole
