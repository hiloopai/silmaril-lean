module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.MemSimd.Excl
public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Thms

/-!
# Round 6: `Step` 22–25 do not fire on bounded code, at any encoding

Round 5 discharged the memory SIMD stores (`vstore-oob`, `vstore-val`, `vstore_lane-oob`,
`vstore_lane-val`) through the provisional encoding: its memory argument has no `OFFSET` field
(`Round5.BwdStep.not_fires_vstoreOob`, …). That argument breaks as soon as the four
instructions get a real encoding. `not_fires_vstore_of_bnd` discharges them instead from the
exclusion, as track read did for the loads (`Round5.Read.bwdS_vload`): the third instruction of
each rule's left-hand side is a `VSTORE`/`VSTORE_LANE` case, which is the image only of
`vecStore`/`vecStoreLane` (by its head, `Typing.adminHead`), and those are not
`Round4.AdminBnd`. The proof reads only the instruction heads, so it survives a change of the
memory SIMD payloads.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open BwdPureStep (fires_step codes_three head_of_caseE)

variable {H : Type} {hn : H → String} {B : Builtins}

/-- An image headed `VSTORE` or `VSTORE_LANE` is not bounded. -/
theorem not_adminBnd_vstore {a : Admin}
    (h : Typing.adminHead a = "VSTORE" ∨ Typing.adminHead a = "VSTORE_LANE") :
    ¬ Round4.AdminBnd a := by
  rcases h with h | h
  · obtain ⟨m, arg, rfl⟩ : ∃ m arg, a = .plain (.vecStore m arg) := by
      revert h
      admin_head_inv
    simp [Round4.AdminBnd, Round4.instrBnd]
  · obtain ⟨sz, m, arg, l, rfl⟩ : ∃ sz m arg l, a = .plain (.vecStoreLane sz m arg l) := by
      revert h
      admin_head_inv
    simp [Round4.AdminBnd, Round4.instrBnd]

/-- Bounded three-instruction code does not end in `v128.store` or `v128.store_lane`. -/
theorem not_vstore_code {c : Config H} (hb : Round4.AdminsBnd c.code) {a₁ a₂ a₃ : Admin}
    (hcode : c.code = [a₁, a₂, a₃])
    (hh : Typing.adminHead a₃ = "VSTORE" ∨ Typing.adminHead a₃ = "VSTORE_LANE") : False := by
  rw [hcode] at hb
  exact not_adminBnd_vstore hh hb.2.2.1

/-- **`Step` 22–25 do not fire on a configuration with bounded code**, in any `simEnv B`. -/
theorem not_fires_vstore_of_bnd (i : Nat) (hi : i ∈ [22, 23, 24, 25]) {c : Config H} {w : Value}
    (hb : Round4.AdminsBnd c.code) :
    ¬ Fires (simEnv B) "Step" i (.tuple [configV hn c, w]) := by
  intro hf
  have RR := hasStepRules_simEnv B
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · obtain ⟨σ, -, -, hes, -, -⟩ := fires_step RR.vstoreOob hf
    obtain ⟨a₁, a₂, a₃, hcode, -, -, h₃⟩ := codes_three hes
    exact not_vstore_code hb hcode (.inl (head_of_caseE h₃))
  · obtain ⟨σ, -, -, hes, -, -⟩ := fires_step RR.vstoreVal hf
    obtain ⟨a₁, a₂, a₃, hcode, -, -, h₃⟩ := codes_three hes
    exact not_vstore_code hb hcode (.inl (head_of_caseE h₃))
  · obtain ⟨σ, -, -, hes, -, -⟩ := fires_step RR.vstoreLaneOob hf
    obtain ⟨a₁, a₂, a₃, hcode, -, -, h₃⟩ := codes_three hes
    exact not_vstore_code hb hcode (.inr (head_of_caseE h₃))
  · obtain ⟨σ, -, -, hes, -, -⟩ := fires_step RR.vstoreLaneVal hf
    obtain ⟨a₁, a₂, a₃, hcode, -, -, h₃⟩ := codes_three hes
    exact not_vstore_code hb hcode (.inr (head_of_caseE h₃))

/-- The same under the explicit exclusion's source, `Round4.Bounded`. -/
theorem not_fires_vstore_of_bounded (i : Nat) (hi : i ∈ [22, 23, 24, 25]) {c : Config H}
    {w : Value} (hb : Round4.Bounded c) :
    ¬ Fires (simEnv B) "Step" i (.tuple [configV hn c, w]) :=
  not_fires_vstore_of_bnd i hi hb.code

end Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd
