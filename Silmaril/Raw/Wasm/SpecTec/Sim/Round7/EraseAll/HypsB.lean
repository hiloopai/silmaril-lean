module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Blocktype
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Mono
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckB

/-!
# Round 7, the whole-evaluator erasure: the checked part with `$blocktype_` and `Step_read`

* `biErase_BI'`: the builtins of `utf8Env (Round4Int.BI P hn host)` satisfy `BIErase Q gd` at every
  `gd` that does not name `$hostcall` (`$blocktype_` through `call_blocktype_erase`).
* `hyps_B : StripInj c → Hyps (QC c) grB gdB (utf8Env (Round4Int.BI P hn host))`. So
  `Round7.EraseAll.eraseAt` covers `$blocktype_` and `Step_read` too; of the six excluded names
  only `$with_tableinst`, `$with_meminst`, `$hostcall` and `Step` are left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

/-- **Round 6's primitives commute with erasure at every name but `$hostcall`.** -/
theorem biErase_BI' {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {Q : Value → Prop} {gd : String → Bool}
    (hgd : ∀ x, gd x = true → x ≠ "hostcall") :
    BIErase Q gd (utf8Env (Round4Int.BI P hn host)) := by
  intro x ws hx _
  have hb : ∀ ws, (utf8Env (Round4Int.BI P hn host)).builtins.call x ws =
      if x = "utf8" then Round6.MemSimd.utf8Call ws else Prims.call P hn host x ws := fun _ => rfl
  rw [hb, hb]
  by_cases hu : x = "utf8"
  · rw [ite_eq_left hu, ite_eq_left hu]
    exact erase_of_oks oks_utf8Call
  rw [ite_eq_right hu, ite_eq_right hu]
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
    refine ⟨?_, fun u hu => allIn_of_nxB Q u (btSpec_nx hu)⟩
    cases h : btSpec ws with
    | none => rfl
    | some v => simp [eraseV_of_nxB v (btSpec_nx h)]
  exact erase_of_oks (oks_call P hn host (hgd x hx) hbt hs)

/-! ## The enlarged checked part -/

theorem mem_defsOfDefs {x : IL.Id} {v : DefDef} : ∀ {ds : List Def}, (x, v) ∈ defsOfDefs ds →
    ∃ d ∈ ds, (x, v) ∈ defsOfDef d
  | [], h => by simp [defsOfDefs, Map.empty] at h
  | d :: ds, h => by
    rw [defsOfDefs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨d', hd', h'⟩ := mem_defsOfDefs h
      exact ⟨d', List.mem_cons_of_mem _ hd', h'⟩
    · exact ⟨d, List.mem_cons_self .., h⟩

theorem mem_relsOfDefs {x : IL.Id} {v : RelDef} : ∀ {ds : List Def}, (x, v) ∈ relsOfDefs ds →
    ∃ d ∈ ds, (x, v) ∈ relsOfDef d
  | [], h => by simp [relsOfDefs, Map.empty] at h
  | d :: ds, h => by
    rw [relsOfDefs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨d', hd', h'⟩ := mem_relsOfDefs h
      exact ⟨d', List.mem_cons_of_mem _ hd', h'⟩
    · exact ⟨d, List.mem_cons_self .., h⟩

theorem grE_grB (x : String) (h : grE x = true) : grB x = true := by simp [grB, h]
theorem gdE_gdB (x : String) (h : gdE x = true) : gdB x = true := by simp [gdB, h]

/-- The definition `d` binding `$blocktype_` or `Step_read` passes the check at `grB`, `gdB`. -/
theorem xDefOk_B {d : Def} (hd : d ∈ Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) (hn : xBNamed d = true) :
    xDefOk grB gdB d = true := by
  have h := List.all_eq_true.1 xBNamedOk_fixed d hd
  simpa [hn] using h

/-- **`Hyps.defs` at `gdB`.** -/
theorem defs_B (B : Builtins) :
    ∀ x d, gdB x = true → (utf8Env B).findDef? x = some d → ∀ cl ∈ d.2.2, xClause grB gdB cl = true := by
  intro x d hx hd cl hcl
  by_cases hE : gdE x = true
  · exact xClause_mono grE_grB gdE_gdB cl (defs_utf8Env B x d hE hd cl hcl)
  · have hbt : x = "blocktype_" := by simpa [gdB, hE] using hx
    subst hbt
    rw [findDef?_utf8Env_of_ne B (by decide)] at hd
    obtain ⟨d', hd', hm⟩ := mem_defsOfDefs (mem_defs_of_findDef hd)
    have hn : xBNamed d' = true := by
      simp only [xBNamed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl ⟨_, hm, rfl⟩
    have h := xDefOk_B hd' hn
    simp only [xDefOk, xDefsOk, Bool.and_eq_true, List.all_eq_true] at h
    have h' := h.1.1 _ hm
    have hg : gdB "blocktype_" = true := by simp [gdB]
    simp only [hg, Bool.not_true, Bool.false_or, List.all_eq_true] at h'
    exact h' cl hcl

/-- **`Hyps.rels` at `grB`.** -/
theorem rels_B (B : Builtins) :
    ∀ x d, grB x = true → (utf8Env B).findRel? x = some d → ∀ r ∈ d.2.2.2, xRule grB gdB r = true := by
  intro x d hx hd r hr
  by_cases hE : grE x = true
  · exact xRule_mono grE_grB gdE_gdB r (rels_utf8Env B x d hE hd r hr)
  · have hsr : x = "Step_read" := by simpa [grB, hE] using hx
    subst hsr
    rw [findRel?_utf8Env] at hd
    obtain ⟨d', hd', hm⟩ := mem_relsOfDefs (mem_rels_of_findRel' hd)
    have hn : xBNamed d' = true := by
      simp only [xBNamed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inr ⟨_, hm, rfl⟩
    have h := xDefOk_B hd' hn
    simp only [xDefOk, xRelsOk, Bool.and_eq_true, List.all_eq_true] at h
    have h' := h.1.2 _ hm
    have hg : grB "Step_read" = true := by simp [grB]
    simp only [hg, Bool.not_true, Bool.false_or, List.all_eq_true] at h'
    exact h' r hr

theorem gdB_ne {x : String} (h : gdB x = true) : x ≠ "hostcall" := by
  simp only [gdB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | rfl
  · exact (gdE_ne h).1
  · decide

/-- **The hypotheses of `eraseAt` at round 6's primitives, on the enlarged checked part.** -/
theorem hyps_B {H : Type} {c : Silmaril.Wasm.Execution.Core.Config H} (hinj : StripInj c)
    (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    Hyps (QC c) grB gdB (utf8Env (Round4Int.BI P hn host)) :=
  hyps_QC hinj (defs_B _) (rels_B _) (biErase_BI' P hn host fun _ => gdB_ne)

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
