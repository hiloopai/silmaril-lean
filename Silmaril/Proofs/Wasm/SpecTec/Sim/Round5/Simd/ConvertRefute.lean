module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Lanes

/-!
# Round 5: `VecAgreeOps.convert` is false under the spec NaN profile

`$vcvtop__` is a function (`: vec_(V128)`), so a call denotes at most one value
(`Equiv.ExecNumeric.Applies.unique`), in every environment. Core's `VecConvertRel` under
`P.nan = .spec` is a relation: `f32x4 → f64x2` `promote_low` of a canonical NaN lane may give the
canonical NaN of either sign (`promote_two`). So the `convert` field of `VecAgreeOps`, an `↔` over
the possible results, fails for every environment (`not_convert_spec`), and with it
`VecAgreeOps`, family V's `VecAgree` and `Round5.Int2.Open2` at every `Profile.spec nd r`.

The same holds of the rule: SpecTec's `vcvtop` produces the single value `$vcvtop__(…)`, while Core
steps to either NaN, so the forward simulation of that Core step cannot hold under any builtins.
This module only proves the statement about the agreement field.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

variable {H : Type}

/-- A 128-bit pattern whose first `f32` lane is the positive canonical NaN, the others `+0`. -/
def nanLane0 : V128 := 0x7FC00000#128

/-- The positive and the negative canonical `f64` NaN, then `+0`. -/
def promotedNaN (neg : Bool) : V128 :=
  FloatShape.f64x2.invLanes [if neg then 0xFFF8000000000000#64 else 0x7FF8000000000000#64, 0]

/-- The two results differ. -/
theorem promotedNaN_ne : promotedNaN false ≠ promotedNaN true := by
  decide

set_option maxRecDepth 100000 in
/-- Each is an allowed result of `promote_low` on `nanLane0` under the spec NaN profile. -/
theorem promote_rel (neg : Bool) :
    vcvtopRel .promoteLow (.float .f32x4) (.float .f64x2) nanLane0 (promotedNaN neg) := by
  refine ⟨[if neg then 0xFFF8000000000000#64 else 0x7FF8000000000000#64, 0], ?_, rfl⟩
  change List.Forall₂ (fun x y => convertRel .promote x (.ok y))
    ([0x7FC00000#32, 0] : List (BitVec 32)) _
  refine .cons ?_ (.cons ?_ .nil) <;> cases neg <;> simp only [convertRel] <;> decide

/-- **`promote_low` has two results** on `nanLane0` when `P.nan = .spec`. -/
theorem promote_two {P : Profile} (hP : P.nan = .spec) (neg : Bool) :
    VecConvertRel P (.float .f32x4) (.float .f64x2) .promoteLow nanLane0 (promotedNaN neg) := by
  simp only [VecConvertRel, hP]
  exact promote_rel neg

/-- **`VecAgreeOps.convert` fails in every environment** when `P.nan = .spec`. -/
theorem not_convert_spec {env : Env} {P : Profile} (hP : P.nan = .spec) :
    ¬ ∀ (s t : Shape) (op : VecConvertOp) (a : V128) (c : Value), Applies env "vcvtop__"
      [.val (Vec.shapeV s), .val (Vec.shapeV t), .val (Vec.vConvertOpV op), .val (Vec.vecV a)] c ↔
      ∃ r, VecConvertRel P s t op a r ∧ c = Vec.vecV r := by
  intro h
  have a₁ := (h _ _ _ _ _).2 ⟨_, promote_two hP false, rfl⟩
  have a₂ := (h _ _ _ _ _).2 ⟨_, promote_two hP true, rfl⟩
  exact promotedNaN_ne (vecV_injective (Equiv.ExecNumeric.Applies.unique a₁ a₂))

/-- **`VecAgreeOps` is unsatisfiable under the spec NaN profile**, for every environment. -/
theorem not_vecAgreeOps_spec {env : Env} {P : Profile} (hP : P.nan = .spec) :
    ¬ VecAgreeOps env P := fun O => not_convert_spec hP O.convert

/-- **Family V's `VecAgree` is unsatisfiable under the spec NaN profile**, for every
environment. -/
theorem not_vecAgree_spec {env : Env} {P : Profile} (hP : P.nan = .spec) :
    ¬ Vec.VecAgree env P := fun A => not_convert_spec hP A.convert

/-- **`Round5.Int2.Open2` is unsatisfiable at every `Profile.spec nd r`**, through its `vecOps`
field; so `Round5.Int2.wholeStepValidOk_of_open2` is vacuous as stated. -/
theorem not_open2_spec {hn : H → String} {host : HostSemantics H} (nd : Bool)
    (r : RelaxedChoice) : ¬ Int2.Open2 hn (Profile.spec nd r) host := fun O =>
  not_vecAgreeOps_spec rfl O.vecOps

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
