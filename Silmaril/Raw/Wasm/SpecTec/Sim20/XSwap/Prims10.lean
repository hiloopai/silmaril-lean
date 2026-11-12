module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Hyps20
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Check10
public import Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.Thms

/-!
# the evaluator-level re-encoding on the 1.0 script (unrefined)

* `biSwap_fwdB10`: the primitives of `utf8Env10T (fwdB10 nd r)` commute with `swapX` (round 3's
  strictness: `$bytes_`, `$ibytes_` and `$growmemory` answer at images of V1 encoders, the float,
  integer and `$utf8` primitives as for 2.0).
* `xScript10`, `defs_10T`, `rels_10T`: the two kernel halves (`Check10`) cover `Utf8Fix.fixedU10`,
  whose definitions and relations are those of `utf8Env10T B`.
* **`hyps10`**: `Hyps (fun _ => True) gr10 gd10 (utf8Env10T (fwdB10 nd r))`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (OKS ValsNx oks_dite oks_none valsNx_cons_val
  valsNx_nil)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (fixedU10 utf8Env10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (bytesCall10 ibytesCall10 growCall10 bytesB10 fwdB10)

theorem nxB_bytesV10 (b : ByteArray) : nxB (Sim10.bytesV b) = true := by
  simp [Sim10.bytesV]

theorem nxB_memInstV10 (m : Silmaril.Wasm.Execution.Runtime.MemInst) :
    nxB (Sim10.memInstV m) = true := by
  simp only [Sim10.memInstV, Sim10.limitsV, nxB, nxBf, nxBs]
  cases m.max <;> simp [nxB_bytesV10]

theorem oks_bytesCall10 (ws : List ArgV) : OKS ws (bytesCall10 ws) := by
  refine ⟨fun v hv => ?_⟩
  unfold bytesCall10 at hv
  split at hv
  · rename_i tv cv
    have hans : ∀ t, Sim10.Whole.bytesAns10 t cv = some v → nxB v = true ∧ nxB cv = true := by
      intro t h
      unfold Sim10.Whole.bytesAns10 at h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨nxB_bytesV10 _, Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.decNum_nx hb⟩
    repeat (first
      | (split at hv; rename_i htv; subst htv
         refine ⟨(hans _ hv).1, ?_⟩
         simp only [valsNx_cons_val, valsNx_nil, and_true]
         exact ⟨rfl, (hans _ hv).2⟩)
      | cases hv)
  · cases hv

theorem oks_ibytesCall10 (ws : List ArgV) : OKS ws (ibytesCall10 ws) := by
  refine ⟨fun v hv => ?_⟩
  unfold ibytesCall10 at hv
  split at hv
  · cases hv
    exact ⟨nxB_bytesV10 _, by simp⟩
  · cases hv

theorem oks_growCall10 (ws : List ArgV) : OKS ws (growCall10 ws) := by
  unfold growCall10
  refine oks_dite (fun h => ⟨fun v hv => ?_⟩) (fun _ => oks_none)
  obtain ⟨d, -, rfl⟩ := Option.map_eq_some_iff.1 hv
  refine ⟨nxB_memInstV10 _, ?_⟩
  rw [h.choose_spec]
  simp [nxB_memInstV10]

theorem oks_bytesB10 (P : Silmaril.Wasm.Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKS ws ((bytesB10 P).call x ws) := by
  show OKS ws (if x = "bytes_" then bytesCall10 ws else if x = "ibytes_" then ibytesCall10 ws
    else if x = "growmemory" then growCall10 ws else (Sim.Floats.floatIntB P).call x ws)
  split
  · exact oks_bytesCall10 ws
  split
  · exact oks_ibytesCall10 ws
  split
  · exact oks_growCall10 ws
  · exact oks_floatIntB P x ws

/-- **The primitives of `utf8Env10T (fwdB10 nd r)` commute with `swapX`.** -/
theorem biSwap_fwdB10 (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice) (gd : String → Bool) :
    Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.BIErase (fun _ => True) gd (utf8Env10T (fwdB10 nd r)) := by
  intro x ws _ _
  refine ⟨swap_of_oks (fun ws => ?_), fun u _ => allIn_true u⟩
  by_cases hx : x = "utf8"
  · subst hx
    rw [Sim10.Utf8Fix.call_utf8Env10T_utf8]
    exact Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.oks_utf8Call ws
  · rw [Sim10.Utf8Fix.call_utf8Env10T_of_ne _ hx]
    exact oks_bytesB10 _ x ws

theorem xScript10 : fixedU10.all (xDefOk gr10 gd10) = true := by
  refine Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.all_chunks _ 175 2 _ fixedU10_length
    fun i hi => ?_
  match i, hi with
  | 0, _ => exact xScript10_chunk00
  | 1, _ => exact xScript10_chunk01
  | _ + 2, h => exact absurd h (by omega)

theorem xDefsOk10 : xDefsOk gr10 gd10 (defsOfDefs fixedU10) = true := by
  rw [xDefsOk_defsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScript10 d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.1

theorem xRelsOk10 : xRelsOk gr10 gd10 (relsOfDefs fixedU10) = true := by
  rw [xRelsOk_relsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScript10 d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.2

theorem xAltsOk10 : xAltsOk gr10 gd10 (relsOfDefs fixedU10) = true := by
  rw [xAltsOk_relsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScript10 d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.2

theorem mem_defs_of_findDef10 {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (utf8Env10T B).findDef? x = some v) : (x, v) ∈ defsOfDefs fixedU10 := by
  unfold utf8Env10T at h
  rw [show ∀ (e : Env), (e.withBuiltins (Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.withUtf8 B)).findDef? x
    = e.findDef? x from fun _ => rfl] at h
  rw [envOfScript, envOfDefs_eq] at h
  have hm := Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.mem_of_find' h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

theorem mem_rels_of_findRel10 {B : Builtins} {x : IL.Id} {v : RelDef}
    (h : (utf8Env10T B).findRel? x = some v) : (x, v) ∈ relsOfDefs fixedU10 := by
  unfold utf8Env10T at h
  rw [show ∀ (e : Env), (e.withBuiltins (Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.withUtf8 B)).findRel? x
    = e.findRel? x from fun _ => rfl] at h
  rw [envOfScript, envOfDefs_eq] at h
  have hm := Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.mem_of_find' h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

theorem defs_10T (B : Builtins) :
    ∀ x d, gd10 x = true → (utf8Env10T B).findDef? x = some d →
      ∀ cl ∈ d.2.2, xClause gr10 gd10 cl = true := by
  intro x d hx hd cl hcl
  have h := List.all_eq_true.1 xDefsOk10 _ (mem_defs_of_findDef10 hd)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  exact h cl hcl

theorem rels_10T (B : Builtins) :
    ∀ x d, gr10 x = true → (utf8Env10T B).findRel? x = some d →
      ∀ r ∈ d.2.2.2, xRule gr10 gd10 r = true := by
  intro x d hx hd r hr
  have h := List.all_eq_true.1 xRelsOk10 _ (mem_rels_of_findRel10 hd)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  exact h r hr

/-- **`eraseAt`'s hypotheses on the 1.0 script, at `utf8Env10T (fwdB10 nd r)`.** -/
theorem hyps10 (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice) :
    Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Hyps (fun _ => True) gr10 gd10 (utf8Env10T (fwdB10 nd r)) :=
  ⟨qInj _, defs_10T _, rels_10T _, biSwap_fwdB10 nd r gd10,
    fun _ _ _ _ _ u _ _ _ _ _ => allIn_true u⟩

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
