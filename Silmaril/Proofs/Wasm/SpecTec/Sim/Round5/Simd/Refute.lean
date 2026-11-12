module

public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs

/-!
# Round 5: `VecAgree` needs `$lanes_`

`$lanes_` and `$inv_lanes_` are declared `hint(builtin)` with no clause
(`3.2-numerics.vector.spectec`). Where `B` does not answer `$lanes_`, no call to it denotes
anything (`not_applies_lanes`), and family V's `VecAgree`, whose `extractNum` field asks
`$lanes_` for a list, is false (`not_vecAgree_of_lanes`). Until this track `Prims.builtins` was
such a `B`, so pass 1's `Round5.Int.Open` was unsatisfiable.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 100000 in
/-- `$lanes_` has no clause. -/
theorem findDef_lanes (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "lanes_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `$inv_lanes_` has no clause. -/
theorem findDef_invLanes (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "inv_lanes_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

/-- No clause list that is empty denotes a value. -/
theorem not_tryClauses_nil {env : Env} {ws : List ArgV} {v : Value} :
    ¬ ∃ n, tryClauses n env [] ws = .ok v := by
  rintro ⟨n, h⟩
  cases n <;> simp [tryClauses] at h

/-- A definition without clauses denotes exactly what `B` answers. -/
theorem applies_noClause_iff {env : Env} {x : IL.Id} {ws : List ArgV} {v : Value}
    (hd : ∃ ps t, env.findDef? x = some (ps, t, [])) :
    Applies env x ws v → env.builtins.call x ws = some v := by
  obtain ⟨ps, t, hf⟩ := hd
  rintro ⟨ps', t', cs, hf', hc⟩
  rw [hf] at hf'
  obtain rfl : ([] : List Clause) = cs := congrArg (fun p => p.2.2) (Option.some.inj hf')
  rcases hc with hc | ⟨-, hb⟩
  · exact absurd hc not_tryClauses_nil
  · exact hb

/-- **No call to `$lanes_` denotes anything** where `B` does not answer it. -/
theorem not_applies_lanes {B : Builtins} (hB : ∀ ws, B.call "lanes_" ws = none)
    (ws : List ArgV) (v : Value) : ¬ Applies (simEnv B) "lanes_" ws v := fun h => by
  have := applies_noClause_iff (findDef_lanes _) h
  rw [show (simEnv B).builtins = B from rfl, hB] at this
  exact absurd this (by simp)

/-- **Family V's `VecAgree` is false where `B` does not answer `$lanes_`**: its `extractNum`
field asks `$lanes_` for the lanes of `i32x4`. Before round 5 this was the case of the concrete
`Prims.builtins`, so pass 1's `Round5.Int.Open` was unsatisfiable through its `vecAgree` field;
`Prims.builtins` now answers `$lanes_` and `$inv_lanes_` (`Round5.Simd.lanesCall`). -/
theorem not_vecAgree_of_lanes {B : Builtins} (hB : ∀ ws, B.call "lanes_" ws = none)
    (P : Profile) : ¬ Vec.VecAgree (simEnv B) P := fun A => by
  obtain ⟨ls, h, -⟩ := A.extractNum (.int .i32x4) 0 0 (by decide) (by decide)
  exact not_applies_lanes hB _ _ h

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
