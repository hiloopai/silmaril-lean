module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeNC
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeUn

/-!
# The script's scalar lane primitives against V2's lane functions

An earlier step stated V2's vector results lane by lane (`VecTyp.vecIntBinOpResult_lanes`, …) with V2's
lane functions (`Numerics.VecLane.iaddSat`, …). This module checks what the 2.0 script's own
lane primitives compute in the corrected script `simEnv20V B`.

**With clauses** (the script defines them): `$iadd_`, `$isub_`, `$imul_`, `$ineg_`, `$iabs_`,
`$imin_`, `$imax_`, `$iadd_sat_`, `$isub_sat_`. They are verbatim wasm-3.0's, so
`numEnvCore_simEnv20V` (24 kernel lookups) makes the shared integer library apply, and
`callDef_*_lane` give, at every builtins `B` and every lane width `N > 0`, the value of V2's lane
function (`+`, `-`, `*`, `VecLane.ineg`, `iabs`, `imin`, `imax`, `iaddSat`, `isubSat`). The
bridge from Silmaril's `IntegerN` transcription to V2's lane functions is `iabs_eq_lane`, …,
`iaddSat_eq_lane`, `isubSat_eq_lane`.

**Without clauses** (`hint(builtin)`): `$ipopcnt_` is answered through `IntNumeric.intCall`
wherever `IntB B` holds, which `vecNB P` satisfies, so it computes `VecLane.ipopcnt`
(`callDef_ipopcnt_lane`). `$iavgr_`, `$iq15mulr_sat_`, `$fpmin_` and `$fpmax_` are answered by no
builtins of this development: at `vecNB P` they **denote nothing** (`not_callDef_unanswered`).
This does not affect any step, because `vecNB P` answers the dispatchers `$vbinop_` directly, but
it means the script's own `AVGR`, `Q15MULR_SAT`, `PMIN` and `PMAX` lanes are not checked against
anything here: `callDef_of_answer` only says that builtins answering them with V2's lane function
make the call compute it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV sxV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB vecNB_call_of_ne)

variable {B : Builtins}

/-! ## `IntegerN` against V2's lane functions -/

open Silmaril.Wasm.Numerics in
theorem iabs_eq_lane {N : Nat} (a : BitVec N) : iabs_ N a = VecLane.iabs a := by
  simp only [iabs_, signed_toNat, ineg_eq, VecLane.iabs, ge_iff_le]

open Silmaril.Wasm.Numerics in
theorem imin_eq_lane {N : Nat} (sx : Signedness) (a b : BitVec N) :
    imin_ N sx a b = VecLane.imin sx a b := by
  cases sx <;> simp only [imin_, signed_toNat, VecLane.imin, VecLane.toIntSx] <;>
    exact if_congr (by simp) rfl rfl

open Silmaril.Wasm.Numerics in
theorem imax_eq_lane {N : Nat} (sx : Signedness) (a b : BitVec N) :
    imax_ N sx a b = VecLane.imax sx a b := by
  cases sx <;> simp only [imax_, signed_toNat, VecLane.imax, VecLane.toIntSx] <;>
    exact if_congr (by simp) rfl rfl

open Silmaril.Wasm.Numerics in
/-- `$sat_u_` is V2's unsigned saturation. -/
theorem satU_eq (N : Nat) (j : Int) : ((sat_u_ N j : Nat) : Int) = VecLane.satU N j := by
  have hp : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  have hc : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by push_cast; rfl
  simp only [sat_u_, VecLane.satU]
  split_ifs <;> omega

open Silmaril.Wasm.Numerics in
/-- `$sat_s_` is V2's signed saturation. -/
theorem satS_eq (N : Nat) (j : Int) : sat_s_ N j = VecLane.satS N j := by
  have hp : (0 : Int) < 2 ^ (N - 1) := by positivity
  simp only [sat_s_, VecLane.satS]
  split_ifs <;> omega

open Silmaril.Wasm.Numerics in
/-- A saturated value is the bit pattern V2's lane function builds. -/
theorem satBits_eq {N : Nat} (sx : Signedness) (j : Int) :
    (match sx with
      | .unsigned => BitVec.ofNat N (sat_u_ N j)
      | .signed => BitVec.ofNat N (invSigned_ N (sat_s_ N j))) =
      BitVec.ofInt N (VecLane.sat N sx j) := by
  cases sx
  case signed =>
    show BitVec.ofNat N (invSigned_ N (sat_s_ N j)) = BitVec.ofInt N (VecLane.satS N j)
    rw [ofNat_invSigned, satS_eq]
  case unsigned =>
    show BitVec.ofNat N (sat_u_ N j) = BitVec.ofInt N (VecLane.satU N j)
    rw [← satU_eq, BitVec.ofInt_natCast]

open Silmaril.Wasm.Numerics in
theorem iaddSat_eq_lane {N : Nat} (sx : Signedness) (a b : BitVec N) :
    iadd_sat_ N sx a b = VecLane.iaddSat sx a b := by
  have h := satBits_eq (N := N) sx (VecLane.toIntSx sx a + VecLane.toIntSx sx b)
  cases sx <;> simpa [iadd_sat_, signed_toNat, VecLane.iaddSat, VecLane.toIntSx] using h

open Silmaril.Wasm.Numerics in
theorem isubSat_eq_lane {N : Nat} (sx : Signedness) (a b : BitVec N) :
    isub_sat_ N sx a b = VecLane.isubSat sx a b := by
  have h := satBits_eq (N := N) sx (VecLane.toIntSx sx a - VecLane.toIntSx sx b)
  cases sx <;> simpa [isub_sat_, signed_toNat, VecLane.isubSat, VecLane.toIntSx] using h

/-! ## What the script computes -/

variable {ρ : VarEnv} {args : List Arg} {N : Nat}

/-- **`$iadd_` computes the `ADD` lane.** -/
theorem callDef_iadd_lane (hρ : ρ.findDef? "iadd_" = none) {a b : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (bvV a), .val (bvV b)]) :
    CallDef (simEnv20V B) ρ "iadd_" args (bvV (a + b)) := by
  simpa only [Silmaril.Wasm.Numerics.iadd_eq] using
    Equiv.NumEnvCore.callDef_iadd numEnvCore_simEnv20V hρ ha

/-- **`$isub_` computes the `SUB` lane.** -/
theorem callDef_isub_lane (hρ : ρ.findDef? "isub_" = none) {a b : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (bvV a), .val (bvV b)]) :
    CallDef (simEnv20V B) ρ "isub_" args (bvV (a - b)) := by
  simpa only [Silmaril.Wasm.Numerics.isub_eq] using
    Equiv.NumEnvCore.callDef_isub numEnvCore_simEnv20V hρ ha

/-- **`$imul_` computes the `MUL` lane.** -/
theorem callDef_imul_lane (hρ : ρ.findDef? "imul_" = none) {a b : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (bvV a), .val (bvV b)]) :
    CallDef (simEnv20V B) ρ "imul_" args (bvV (a * b)) := by
  simpa only [Silmaril.Wasm.Numerics.imul_eq] using
    Equiv.NumEnvCore.callDef_imul numEnvCore_simEnv20V hρ ha

/-- **`$ineg_` computes the `NEG` lane.** -/
theorem callDef_ineg_lane (hρ : ρ.findDef? "ineg_" = none) {a : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (bvV a)]) :
    CallDef (simEnv20V B) ρ "ineg_" args (bvV (Silmaril.Wasm.Numerics.VecLane.ineg a)) := by
  simpa only [Silmaril.Wasm.Numerics.ineg_eq, Silmaril.Wasm.Numerics.VecLane.ineg] using
    Equiv.NumEnvCore.callDef_ineg numEnvCore_simEnv20V hρ ha

/-- **`$iabs_` computes the `ABS` lane.** -/
theorem callDef_iabs_lane (hρ : ρ.findDef? "iabs_" = none) {a : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (bvV a)]) (hN : 0 < N) :
    CallDef (simEnv20V B) ρ "iabs_" args (bvV (Silmaril.Wasm.Numerics.VecLane.iabs a)) := by
  simpa only [iabs_eq_lane] using
    Equiv.NumEnvCore.callDef_iabs numEnvCore_simEnv20V hρ ha hN

/-- **`$imin_` computes the `MIN` lane.** -/
theorem callDef_imin_lane (hρ : ρ.findDef? "imin_" = none) {sx : Signedness} {a b : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (sxV sx), .val (bvV a), .val (bvV b)])
    (hN : 0 < N) :
    CallDef (simEnv20V B) ρ "imin_" args (bvV (Silmaril.Wasm.Numerics.VecLane.imin sx a b)) := by
  simpa only [imin_eq_lane] using
    Equiv.NumEnvCore.callDef_imin numEnvCore_simEnv20V hρ ha hN

/-- **`$imax_` computes the `MAX` lane.** -/
theorem callDef_imax_lane (hρ : ρ.findDef? "imax_" = none) {sx : Signedness} {a b : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (sxV sx), .val (bvV a), .val (bvV b)])
    (hN : 0 < N) :
    CallDef (simEnv20V B) ρ "imax_" args (bvV (Silmaril.Wasm.Numerics.VecLane.imax sx a b)) := by
  simpa only [imax_eq_lane] using
    Equiv.NumEnvCore.callDef_imax numEnvCore_simEnv20V hρ ha hN

/-- **`$iadd_sat_` computes the `ADD_SAT` lane.** -/
theorem callDef_iaddSat_lane (hρ : ρ.findDef? "iadd_sat_" = none) {sx : Signedness}
    {a b : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (sxV sx), .val (bvV a), .val (bvV b)])
    (hN : 0 < N) :
    CallDef (simEnv20V B) ρ "iadd_sat_" args
      (bvV (Silmaril.Wasm.Numerics.VecLane.iaddSat sx a b)) := by
  simpa only [iaddSat_eq_lane] using
    Equiv.NumEnvCore.callDef_iaddSat numEnvCore_simEnv20V hρ ha hN

/-- **`$isub_sat_` computes the `SUB_SAT` lane.** -/
theorem callDef_isubSat_lane (hρ : ρ.findDef? "isub_sat_" = none) {sx : Signedness}
    {a b : BitVec N}
    (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (sxV sx), .val (bvV a), .val (bvV b)])
    (hN : 0 < N) :
    CallDef (simEnv20V B) ρ "isub_sat_" args
      (bvV (Silmaril.Wasm.Numerics.VecLane.isubSat sx a b)) := by
  simpa only [isubSat_eq_lane] using
    Equiv.NumEnvCore.callDef_isubSat numEnvCore_simEnv20V hρ ha hN

/-! ## The clause-less lane primitives -/

/-- **`$ipopcnt_` computes the `POPCNT` lane** at every `IntB` builtins. -/
theorem callDef_ipopcnt_lane (hB : Sim.IntNumeric.IntB B) (hρ : ρ.findDef? "ipopcnt_" = none)
    {a : BitVec N} (ha : EvalArgs (simEnv20V B) ρ args [.val (natV N), .val (bvV a)]) :
    CallDef (simEnv20V B) ρ "ipopcnt_" args (bvV (Silmaril.Wasm.Numerics.VecLane.ipopcnt a)) := by
  obtain ⟨ps, t, hd⟩ := noClauses_lanePrims (B := B) (x := "ipopcnt_") (by simp [lanePrims])
  refine Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (hB _ _ _ ?_)
  simp [Sim.IntNumeric.intCall, Equiv.ExecBuiltins.unBits, natV,
    Equiv.ExecBuiltins.asBits?_bvV, Silmaril.Wasm.Numerics.ipopcnt_,
    Silmaril.Wasm.Numerics.VecLane.ipopcnt]

/-- **At `vecNB P`, the script's `$iavgr_`, `$iq15mulr_sat_`, `$fpmin_` and `$fpmax_` denote
nothing.** -/
theorem not_callDef_unanswered (P : Profile) {x : IL.Id}
    (hx : x ∈ ["iavgr_", "iq15mulr_sat_", "fpmin_", "fpmax_"]) (hρ : ρ.findDef? x = none)
    {v : Value} : ¬ CallDef (simEnv20V (vecNB P)) ρ x args v := by
  have hl : x ∈ lanePrims := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [lanePrims]
  obtain ⟨ps, t, hd⟩ := noClauses_lanePrims (B := vecNB P) hl
  refine not_callDef_of_no_clauses hρ hd fun ws => ?_
  rw [simEnv20V, Env.builtins_withBuiltins]
  exact vecNB_unanswered P hx ws

/-- The restatement: builtins that answer a clause-less lane primitive make the call compute
that answer. -/
theorem callDef_of_answer {x : IL.Id} (hx : x ∈ lanePrims) (hρ : ρ.findDef? x = none)
    {ws : List ArgV} {v : Value} (ha : EvalArgs (simEnv20V B) ρ args ws)
    (hb : B.call x ws = some v) : CallDef (simEnv20V B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := noClauses_lanePrims (B := B) hx
  refine Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha ?_
  rw [simEnv20V, Env.builtins_withBuiltins]
  exact hb

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
