module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk1
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk3
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk4
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk5
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk6
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk7
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk8
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Chunk9

/-!
# Round 7: the `Step` closure facts on the whole fixed wasm-3.0 script

`scriptOk_fixed` puts the ten kernel-checked chunks together (`scriptOk_chunks`), and the
theorems after it unfold `scriptOk` into the separate facts: closure (`stepReach_closed`), no
`EXPORTS` atom (`stepReach_noExports`), `$utf8` called only by `$utf8` and `name`
(`stepReach_utf8`), record composition only in `Deftype_ok` (`stepReach_comp`), and every record
update rooted at `$sof`, `$fof` or `$lanes_` along a path without `MODULE`, `FUNCS` or `EXPORTS`
(`stepReach_upd`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

open Silmaril.SpecTec.IL hiding Id Prod

theorem defsItems_append (a b : List Def) : defsItems (a ++ b) = defsItems a ++ defsItems b := by
  induction a with
  | nil => simp [defsItems]
  | cons d a ih => simp [defsItems, ih, List.append_assoc]

theorem scriptOk_append (R : List (Nat × String)) (a b : Script) :
    scriptOk R (a ++ b) = (scriptOk R a && scriptOk R b) := by
  simp [scriptOk, items, defsItems_append, List.all_append]

theorem scriptOk_nil (R : List (Nat × String)) : scriptOk R [] = true := by
  simp [scriptOk, items, defsItems]

/-- **`scriptOk` from chunks of `k` definitions.** -/
theorem scriptOk_chunks (R : List (Nat × String)) (k : Nat) :
    ∀ (n : Nat) (s : Script), s.length ≤ k * n →
      (∀ i < n, scriptOk R ((s.drop (k * i)).take k) = true) → scriptOk R s = true
  | 0, s, h, _ => by
    have hs : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (by simpa using h))
    subst hs
    exact scriptOk_nil R
  | n + 1, s, h, hc => by
    rw [← List.take_append_drop k s, scriptOk_append]
    have h₀ : scriptOk R (s.take k) = true := by simpa using hc 0 (Nat.succ_pos n)
    have h₁ : scriptOk R (s.drop k) = true := by
      refine scriptOk_chunks R k n (s.drop k) ?_ fun i hi => ?_
      · simp only [List.length_drop]
        rw [Nat.mul_succ] at h
        omega
      · have := hc (i + 1) (Nat.succ_lt_succ hi)
        rwa [Nat.mul_succ, Nat.add_comm, ← List.drop_drop] at this
    simp [h₀, h₁]

theorem fixed_length_le : Scripts.Wasm30.fixed.length ≤ 100 * 10 := by decide +kernel

/-- **The `Step` closure facts hold on the whole fixed wasm-3.0 script.** -/
theorem scriptOk_fixed : scriptOk stepReach Scripts.Wasm30.fixed = true := by
  refine scriptOk_chunks stepReach 100 10 _ fixed_length_le fun i hi => ?_
  match i, hi with
  | 0, _ => simpa using scriptOk_chunk0
  | 1, _ => exact scriptOk_chunk1
  | 2, _ => exact scriptOk_chunk2
  | 3, _ => exact scriptOk_chunk3
  | 4, _ => exact scriptOk_chunk4
  | 5, _ => exact scriptOk_chunk5
  | 6, _ => exact scriptOk_chunk6
  | 7, _ => exact scriptOk_chunk7
  | 8, _ => exact scriptOk_chunk8
  | 9, _ => exact scriptOk_chunk9

/-- Every item of the fixed script named in `stepReach` is `itemOk`. -/
theorem itemOk_of_mem {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) : itemOk stepReach it = true := by
  have := List.all_eq_true.1 scriptOk_fixed it h
  simpa [List.elem_eq_mem, hR] using this

/-- **`stepReach` is closed**: every reference made by a definition of the fixed wasm-3.0 script
named in `stepReach` is in `stepReach`. -/
theorem stepReach_closed {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) : ∀ r ∈ evRefs it.2.2, r ∈ stepReach := by
  have := itemOk_of_mem h hR
  simp only [itemOk, Bool.and_eq_true, List.all_eq_true, List.elem_eq_mem,
    decide_eq_true_eq] at this
  exact this.1

/-- `evOk` holds of every event of a reachable item. -/
theorem evOk_of_mem {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) : ∀ e ∈ it.2.2, evOk (it.1, it.2.1) e = true := by
  have := itemOk_of_mem h hR
  simp only [itemOk, Bool.and_eq_true, List.all_eq_true] at this
  exact this.2

/-- **No reachable expression uses the atom `EXPORTS`**: not as a record field, a projection or
a path step. -/
theorem stepReach_noExports {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) : Ev.atom "EXPORTS" ∉ it.2.2 := fun he => by
  simpa [evOk] using evOk_of_mem h hR _ he

/-- **Only `$utf8` itself and the type `name` call `$utf8`** among the reachable definitions. -/
theorem stepReach_utf8 {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) (hu : Ev.ref 1 "utf8" ∈ it.2.2) :
    (it.1, it.2.1) ∈ utf8Allowed := by
  simpa [evOk] using evOk_of_mem h hR _ hu

/-- **Only `Deftype_ok` composes records or lists** among the reachable definitions. -/
theorem stepReach_comp {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) (hc : Ev.comp ∈ it.2.2) : (it.1, it.2.1) ∈ compAllowed := by
  simpa [evOk] using evOk_of_mem h hR _ hc

/-- **Every reachable record update starts at `$sof`, `$fof` or `$lanes_`, along a path without
`MODULE`, `FUNCS` or `EXPORTS`.** -/
theorem stepReach_upd {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hR : (it.1, it.2.1) ∈ stepReach) {r : Exp} {ats : List String} (hu : Ev.upd r ats ∈ it.2.2) :
    rootHead r ∈ rootsAllowed ∧ ∀ a ∈ ats, a ∉ atomsBanned := by
  simpa [evOk] using evOk_of_mem h hR _ hu

/-- `Step` is in the closure. -/
theorem step_mem_stepReach : (0, "Step") ∈ stepReach := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
