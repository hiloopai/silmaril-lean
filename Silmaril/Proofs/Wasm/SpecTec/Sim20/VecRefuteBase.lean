module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.Thms

/-!
# The float-only vector operators (definitions and the fuel argument)

`FloatOnly`: the float vector instructions without an integer namesake. `not_hasTyp_of_false`:
a typing check that answers `false` at some fuel never answers `true`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecRefute

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)

set_option maxRecDepth 100000

variable {B : Builtins}

/-- A typing check that answers `false` at some fuel never answers `true`. -/
theorem not_hasTyp_of_false {env : Env} {ρ : VarEnv} {t : Typ} {v : Value} {N : Nat}
    (h : hasTyp N env ρ t v = .ok false) : ¬ HasTyp env ρ t v := by
  rintro ⟨n, hn⟩
  rcases Nat.le_total n N with hle | hle
  · have hm : hasTyp n env ρ t v ⊑ hasTyp N env ρ t v := (monoTypAt_of_le hle).typ env ρ t v
    rw [hn, h] at hm
    rcases hm with hm | hm <;> simp at hm
  · have hm : hasTyp N env ρ t v ⊑ hasTyp n env ρ t v := (monoTypAt_of_le hle).typ env ρ t v
    rw [hn, h] at hm
    rcases hm with hm | hm <;> simp at hm

/-- **The float vector instructions without an integer namesake.** -/
def FloatOnly : V2.Instr → Prop
  | .vecFloatUnOp _ op => op ∈ [.sqrt, .ceil, .floor, .trunc, .nearest]
  | .vecFloatBinOp _ op => op ∈ [.div, .min, .max, .pmin, .pmax]
  | .vecFloatRelOp _ op => op ∈ [.lt, .gt, .le, .ge]
  | _ => False

end Silmaril.Wasm.SpecTec.Sim20.VecRefute
