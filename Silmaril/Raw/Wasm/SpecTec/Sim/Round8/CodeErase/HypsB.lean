module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.Blocktype
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Script

/-!
# Round 8, function code erasure: the hypotheses at round 6's primitives (unrefined)

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

* `biErase_sim`: the builtins of `simEnv (Prims.builtins P hn host)` satisfy `BIErase Q gd` at
  every `gd` that does not name `$hostcall` (`$blocktype_` through `call_blocktype_erase`, `$sx`
  directly, every other primitive by strictness).
* `hyps_sim : Hyps (fun _ => True) grC gdC (simEnv (Prims.builtins P hn host))`: every hypothesis
  of `Round8.CodeErase.EraseAll.eraseAt` holds on the wasm-3.0 script, at every value.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

/-- **Round 6's primitives commute with erasure at every name but `$hostcall`**, in `simEnv`. -/
theorem biErase_sim {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {Q : Value → Prop} {gd : String → Bool}
    (hgd : ∀ x, gd x = true → x ≠ "hostcall") :
    BIErase Q gd (simEnv (Prims.builtins P hn host)) := by
  intro x ws hx _
  have hb : ∀ ws, (simEnv (Prims.builtins P hn host)).builtins.call x ws =
      Prims.call P hn host x ws := fun _ => rfl
  rw [hb, hb]
  by_cases hs : x = "sx"
  · subst hs
    rw [call_sx, call_sx, vvCall_sx_erase]
    refine ⟨?_, fun u hu => by rw [vvCall_sx_val hu]; trivial⟩
    cases h : FwdSimdAgg.vvCall "sx" ws with
    | none => rfl
    | some v => rw [vvCall_sx_val h]; rfl
  by_cases hbt : x = "blocktype_"
  · subst hbt
    rw [call_blocktype_erase, call_blocktype_eq]
    refine ⟨?_, fun u hu => allIn_of_ncB Q u (btSpec_nx hu)⟩
    cases h : btSpec ws with
    | none => rfl
    | some v => simp [eraseC_of_ncB v (btSpec_nx h)]
  exact erase_of_oks (oks_call P hn host (hgd x hx) hbt hs)

/-- `gdC` does not name `$hostcall`: it is `excludedC`. -/
theorem gdC_ne {x : String} (h : gdC x = true) : x ≠ "hostcall" := by
  unfold gdC stepReachC at h
  have hm := (List.mem_filter.1 (List.contains_iff_mem.1 h)).2
  rintro rfl
  revert hm
  decide

mutual
/-- Every value is in the swap set of every value. -/
theorem allIn_true : ∀ v : Value, AllIn (fun _ => True) v
  | .bool _ => trivial
  | .num _ => trivial
  | .text _ => trivial
  | .tuple vs => allIns_true vs
  | .case _ w => allIn_true w
  | .struct gs => ⟨fun _ => trivial, allInf_true gs⟩
  | .list vs => allIns_true vs
  | .opt none => trivial
  | .opt (some w) => allIn_true w

theorem allIns_true : ∀ vs : List Value, AllIns (fun _ => True) vs
  | [] => trivial
  | v :: vs => ⟨allIn_true v, allIns_true vs⟩

theorem allInf_true : ∀ gs : List (IL.AtomS × Value), AllInf (fun _ => True) gs
  | [] => trivial
  | (_, v) :: gs => ⟨allIn_true v, allInf_true gs⟩
end

/-- **The hypotheses of `eraseAt` on the wasm-3.0 script at round 6's primitives**, with every
value in the swap set. -/
theorem hyps_sim {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    Hyps (fun _ => True) grC gdC (simEnv (Prims.builtins P hn host)) :=
  ⟨qInj _, defs_simEnv _, rels_simEnv _, biErase_sim P hn host fun _ => gdC_ne,
    fun _ _ _ _ _ u _ _ _ _ _ => allIn_true u⟩

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll
