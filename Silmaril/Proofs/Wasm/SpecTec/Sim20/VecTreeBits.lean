module

public import Silmaril.Wasm.SpecTec.Sim20.VecWhole.Thms

/-!
# `v128.not`, `v128.andnot` and `v128.bitselect`: the script's primitives denote nothing at
`vecNB P`

The 2.0 script declares `$inot_`, `$iandnot_` and `$ibitselect_` `hint(builtin)` with no
clause (`3-numerics.spectec:110-131,157-161`), like round 8's `$iavgr_` and `$iq15mulr_sat_`.
`vecNB P` answers none of them (`vecNB_bitPrims`, by unfolding its chain to round 3's integer
and float primitives), so a call denotes nothing there (**`not_callDef_bitPrims`**). The
restatement is `callDef_bitPrim_of_answer`: builtins that answer them make the call compute the
answer. `$iand_`, `$ior_` and `$ixor_`, the other bitwise primitives, are answered 's
`IntNumeric.intCall` at every width (`VecWhole.intB_vecNB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV sxV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB vecNB_call_of_ne)

variable {B : Builtins}

/-- The bitwise primitives of the 2.0 script that no builtin of `vecNB P` answers. -/
def bitPrims : List IL.Id := ["inot_", "iandnot_", "ibitselect_"]

set_option maxRecDepth 100000 in
/-- None of them has a clause in `simEnv20V B` (kernel lookups). -/
theorem noClauses_bitPrims {x : IL.Id} (hx : x ∈ bitPrims) :
    Sim.IntNumeric.NoClauses (simEnv20V B) x := by
  simp only [bitPrims, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

/-- **`vecNB P` answers none of them.** -/
theorem vecNB_bitPrims (P : Profile) {x : IL.Id} (hx : x ∈ bitPrims) (ws : List ArgV) :
    (vecNB P).call x ws = none := by
  simp only [bitPrims, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    rw [vecNB_call_of_ne (by decide) (by decide) (by decide),
      VecLane.vecB_call_of_ne (by decide) (by decide), Whole.storeB_call_of_ne (by decide),
      Whole.laneB_call_of_ne (by decide) (by decide), Whole.vbytesB_call_of_ne (by decide),
      Whole.growB_call_of_ne (by decide) (by decide)] <;>
    simp [Sim.Floats.floatIntB, Sim.Floats.floatNames, Sim.IntNumeric.intCall]

variable {ρ : VarEnv} {args : List Arg}

/-- **At `vecNB P`, the script's `$inot_`, `$iandnot_` and `$ibitselect_` denote nothing**: no
clause, and no builtin answer. In the script text the only clauses of
`$vvunop_(V128, NOT, …)`, `$vvbinop_(V128, ANDNOT, …)` and `$vvternop_(V128, BITSELECT, …)` call
them (`3-numerics.spectec:369-374`); that the dispatchers fail too is not proved here. -/
theorem not_callDef_bitPrims (P : Profile) {x : IL.Id} (hx : x ∈ bitPrims)
    (hρ : ρ.findDef? x = none) {v : Value} : ¬ CallDef (simEnv20V (vecNB P)) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := noClauses_bitPrims (B := vecNB P) hx
  refine not_callDef_of_no_clauses hρ hd fun ws => ?_
  rw [simEnv20V, Env.builtins_withBuiltins]
  exact vecNB_bitPrims P hx ws

/-- The restatement: builtins that answer a bitwise primitive make the call compute that
answer. -/
theorem callDef_bitPrim_of_answer {x : IL.Id} (hx : x ∈ bitPrims) (hρ : ρ.findDef? x = none)
    {ws : List ArgV} {v : Value} (ha : EvalArgs (simEnv20V B) ρ args ws)
    (hb : B.call x ws = some v) : CallDef (simEnv20V B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := noClauses_bitPrims (B := B) hx
  refine Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha ?_
  rw [simEnv20V, Env.builtins_withBuiltins]
  exact hb

end Silmaril.Wasm.SpecTec.Sim20.VecTree
