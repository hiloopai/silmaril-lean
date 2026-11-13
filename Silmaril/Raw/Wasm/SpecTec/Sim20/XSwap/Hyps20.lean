module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Prims20
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Check0
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Check1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Check2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Check3
public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Thms

/-!
# the hypotheses of the evaluator-level re-encoding on the 2.0 script (unrefined)

* `xScript20`: the twenty kernel chunks (`Check0`–`Check3`) cover the corrected 2.0 script, so every
  definition of `gd20` and every relation of `gr20` passes the check, conclusion alternatives
  included (`xDefsOk20`, `xRelsOk20`, `xAltsOk20`).
* `defs_20T`, `rels_20T`: in `utf8Env20T B` the definitions are the script's but `$utf8`, which has
  no clauses, and the relations are the script's.
* **`hyps20`**: `Hyps (fun _ => True) gr20 gd20 (utf8Env20T (storeB P))`, so
  `EraseAll.eraseAt` holds there at every fuel.
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
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (fixedT20 simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T)

set_option maxRecDepth 100000 in
theorem fixedT20_length : fixedT20.length ≤ 25 * 20 := by
  decide +kernel

theorem xScript20 : fixedT20.all (xDefOk gr20 gd20) = true := by
  refine Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.all_chunks _ 25 20 _ fixedT20_length
    fun i hi => ?_
  match i, hi with
  | 0, _ => exact xScript20_chunk00
  | 1, _ => exact xScript20_chunk01
  | 2, _ => exact xScript20_chunk02
  | 3, _ => exact xScript20_chunk03
  | 4, _ => exact xScript20_chunk04
  | 5, _ => exact xScript20_chunk05
  | 6, _ => exact xScript20_chunk06
  | 7, _ => exact xScript20_chunk07
  | 8, _ => exact xScript20_chunk08
  | 9, _ => exact xScript20_chunk09
  | 10, _ => exact xScript20_chunk10
  | 11, _ => exact xScript20_chunk11
  | 12, _ => exact xScript20_chunk12
  | 13, _ => exact xScript20_chunk13
  | 14, _ => exact xScript20_chunk14
  | 15, _ => exact xScript20_chunk15
  | 16, _ => exact xScript20_chunk16
  | 17, _ => exact xScript20_chunk17
  | 18, _ => exact xScript20_chunk18
  | 19, _ => exact xScript20_chunk19
  | _ + 20, h => exact absurd h (by omega)

theorem xDefsOk_append (gr gd : String → Bool) (a b : Map DefDef) :
    xDefsOk gr gd (a ++ b) = (xDefsOk gr gd a && xDefsOk gr gd b) := by
  simp [xDefsOk, List.all_append]

theorem xRelsOk_append (gr gd : String → Bool) (a b : Map RelDef) :
    xRelsOk gr gd (a ++ b) = (xRelsOk gr gd a && xRelsOk gr gd b) := by
  simp [xRelsOk, List.all_append]

theorem xAltsOk_append (gr gd : String → Bool) (a b : Map RelDef) :
    xAltsOk gr gd (a ++ b) = (xAltsOk gr gd a && xAltsOk gr gd b) := by
  simp [xAltsOk, List.all_append]

theorem xDefsOk_defsOfDefs (gr gd : String → Bool) : ∀ ds : List Def,
    xDefsOk gr gd (defsOfDefs ds) = ds.all fun d => xDefsOk gr gd (defsOfDef d)
  | [] => rfl
  | d :: ds => by
    rw [defsOfDefs, xDefsOk_append, xDefsOk_defsOfDefs gr gd ds, List.all_cons, Bool.and_comm]

theorem xRelsOk_relsOfDefs (gr gd : String → Bool) : ∀ ds : List Def,
    xRelsOk gr gd (relsOfDefs ds) = ds.all fun d => xRelsOk gr gd (relsOfDef d)
  | [] => rfl
  | d :: ds => by
    rw [relsOfDefs, xRelsOk_append, xRelsOk_relsOfDefs gr gd ds, List.all_cons, Bool.and_comm]

theorem xAltsOk_relsOfDefs (gr gd : String → Bool) : ∀ ds : List Def,
    xAltsOk gr gd (relsOfDefs ds) = ds.all fun d => xAltsOk gr gd (relsOfDef d)
  | [] => rfl
  | d :: ds => by
    rw [relsOfDefs, xAltsOk_append, xAltsOk_relsOfDefs gr gd ds, List.all_cons, Bool.and_comm]

theorem xDefsOk20 : xDefsOk gr20 gd20 (defsOfDefs fixedT20) = true := by
  rw [xDefsOk_defsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScript20 d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.1

theorem xRelsOk20 : xRelsOk gr20 gd20 (relsOfDefs fixedT20) = true := by
  rw [xRelsOk_relsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScript20 d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.2

theorem xAltsOk20 : xAltsOk gr20 gd20 (relsOfDefs fixedT20) = true := by
  rw [xAltsOk_relsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScript20 d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.2

theorem mem_defs_of_findDef20 {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (simEnv20T B).findDef? x = some v) : (x, v) ∈ defsOfDefs fixedT20 := by
  unfold simEnv20T at h
  rw [Env.findDef?_withBuiltins, envOfScript, envOfDefs_eq] at h
  have hm := Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.mem_of_find' h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

theorem mem_rels_of_findRel20 {B : Builtins} {x : IL.Id} {v : RelDef}
    (h : (simEnv20T B).findRel? x = some v) : (x, v) ∈ relsOfDefs fixedT20 := by
  unfold simEnv20T at h
  rw [Env.findRel?_withBuiltins, envOfScript, envOfDefs_eq] at h
  have hm := Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.mem_of_find' h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

/-- **`Hyps.defs` at `utf8Env20T B`.** -/
theorem defs_20T (B : Builtins) :
    ∀ x d, gd20 x = true → (utf8Env20T B).findDef? x = some d →
      ∀ cl ∈ d.2.2, xClause gr20 gd20 cl = true := by
  intro x d hx hd cl hcl
  by_cases hu : x = "utf8"
  · subst hu
    rw [Utf8Mono.findDef?_utf8Env20T] at hd
    cases hd
    cases hcl
  · rw [Utf8Mono.findDef?_utf8Env20T_of_ne B hu] at hd
    have h := List.all_eq_true.1 xDefsOk20 _ (mem_defs_of_findDef20 hd)
    simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
    exact h cl hcl

/-- **`Hyps.rels` at `utf8Env20T B`.** -/
theorem rels_20T (B : Builtins) :
    ∀ x d, gr20 x = true → (utf8Env20T B).findRel? x = some d →
      ∀ r ∈ d.2.2.2, xRule gr20 gd20 r = true := by
  intro x d hx hd r hr
  rw [Utf8Mono.findRel?_utf8Env20T B x] at hd
  have h := List.all_eq_true.1 xRelsOk20 _ (mem_rels_of_findRel20 hd)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  exact h r hr

/-- **`eraseAt`'s hypotheses on the 2.0 script, at `utf8Env20T (storeB P)`.** -/
theorem hyps20 (P : Silmaril.Wasm.Numerics.Profile) :
    Hyps (fun _ => True) gr20 gd20 (utf8Env20T (Silmaril.Wasm.SpecTec.Sim20.Whole.storeB P)) :=
  ⟨qInj _, defs_20T _, rels_20T _, biSwap_storeB P gd20,
    fun _ _ _ _ _ u _ _ _ _ _ => allIn_true u⟩

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
