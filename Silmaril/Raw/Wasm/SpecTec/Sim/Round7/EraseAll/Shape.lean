module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Upd

/-!
# Round 7, the whole-evaluator erasure: the swap set `QC c` is shaped like module instances

`qShape_QC : QShape (QC c)`: a record of `QC c` is the image of a module instance, whose fields are
those of `moduleinst` and whose fields other than `EXPORTS` are lists of addresses (numbers) or of
`_DEF` cases. So `UpdSafe (QC c) env` (`updSafe_QC`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

theorem flat_tyV_def (d : Silmaril.Wasm.Validation.DefType) :
    Flat (Silmaril.SpecTec.Equiv.Validation.tyV d) := by
  cases d
  exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem flat_num (k : Nat) : Flat (.num (.natN k)) :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem flat_addrs (l : List Nat) : ∃ us, Value.list (l.map fun a => .num (.natN a)) = .list us ∧
    ∀ u ∈ us, Flat u :=
  ⟨_, rfl, fun u hu => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hu; exact flat_num a⟩

theorem qShape_moduleInst (m : ModuleInst) : ∃ gs, moduleInstToValue Sim.CT m = .struct gs ∧
    ∀ p ∈ gs, p.1 ∈ Roots.modAtoms ∧ (p.1 ≠ "EXPORTS" → ∃ us, p.2 = .list us ∧ ∀ u ∈ us, Flat u) := by
  refine ⟨_, rfl, fun p hp => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by simp [Roots.modAtoms, Roots.numAtoms], fun hne => ?_⟩
  · refine ⟨_, rfl, fun u hu => ?_⟩
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
    exact flat_tyV_def d
  all_goals first | exact flat_addrs _ | exact absurd rfl hne

theorem qShape_QC {H : Type} (c : Config H) : QShape (QC c) := by
  intro r hr
  rcases hr with ⟨m, -, rfl⟩ | ⟨m, -, rfl, -⟩ <;> exact qShape_moduleInst m

theorem updSafe_QC {H : Type} (c : Config H) (env : Env) : UpdSafe (QC c) env :=
  updSafe_of_shape (qShape_QC c)

/-- **`BIErase` in its natural form**: the primitives of `gd` names do not see erasure of their
arguments, and answer values without `EXPORTS` records. -/
theorem biErase_of {Q : Value → Prop} {gd : String → Bool} {env : Env}
    (hc : ∀ x ws, gd x = true → env.builtins.call x (ws.map eraseA) = env.builtins.call x ws)
    (hn : ∀ x ws u, gd x = true → env.builtins.call x ws = some u → nxB u = true) :
    BIErase Q gd env := by
  intro x ws hx _
  refine ⟨?_, fun u hu => allIn_of_nxB Q u (hn x ws u hx hu)⟩
  rw [hc x ws hx]
  cases h : env.builtins.call x ws with
  | none => rfl
  | some u => simp [eraseV_of_nxB u (hn x ws u hx h)]

/-- **The hypotheses at the swap set of a configuration**: `QInj` and `UpdSafe` are discharged;
what is left is the syntactic check of the `gd`/`gr` part of the script and the builtins. -/
theorem hyps_QC {H : Type} {c : Config H} (hinj : StripInj c) {gr gd : String → Bool} {env : Env}
    (hd : ∀ x d, gd x = true → env.findDef? x = some d → ∀ cl ∈ d.2.2, xClause gr gd cl = true)
    (hr : ∀ x d, gr x = true → env.findRel? x = some d → ∀ r ∈ d.2.2.2, xRule gr gd r = true)
    (hb : BIErase (QC c) gd env) : Hyps (QC c) gr gd env :=
  ⟨qInj_QC hinj, hd, hr, hb, updSafe_QC c env⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
