module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VBytes.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VBytes.Chunk0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VBytes.Chunk1
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VBytes.Chunk2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VBytes.Chunk3

/-!
# Round 7, memory SIMD: where `simEnv B` can call `$vbytes_`

The kernel facts of `Chunk0`–`Chunk3` and `Rules`, read in `simEnv B` for every `B`:

* `vbytesOnlyStep_fixed`: in the whole fixed script only `Step_read` and `Step` refer to
  `$vbytes_`;
* `def_noVBytes`, `typ_noVBytes`, `rel_noVBytes`: no definition, no type and no relation other
  than `Step_read` and `Step` that `simEnv B` finds refers to `$vbytes_`;
* `pure_noVBytes`, `read_noVBytes`, `step_noVBytes`: no rule of `Step_pure`, no rule of
  `Step_read` outside `msReadRules` and no rule of `Step` outside `stepMSRules` refers to
  `$vbytes_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VBytes

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script

theorem vbytesOnlyStep_append (a b : Script) :
    vbytesOnlyStep (a ++ b) = (vbytesOnlyStep a && vbytesOnlyStep b) := by
  simp [vbytesOnlyStep, items, defsItems_append, List.all_append]

/-- `vbytesOnlyStep` from chunks of `k` definitions. -/
theorem vbytesOnlyStep_chunks (k : Nat) :
    ∀ (n : Nat) (s : Script), s.length ≤ k * n →
      (∀ i < n, vbytesOnlyStep ((s.drop (k * i)).take k) = true) → vbytesOnlyStep s = true
  | 0, s, h, _ => by
    have hs : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (by simpa using h))
    rw [hs]
    rfl
  | n + 1, s, h, hc => by
    have h₀ : vbytesOnlyStep (s.take k) = true := by simpa using hc 0 (Nat.succ_pos n)
    have hlen : (s.drop k).length ≤ k * n := by
      simp only [List.length_drop]
      rw [Nat.mul_succ] at h
      omega
    have hc' : ∀ i < n, vbytesOnlyStep (((s.drop k).drop (k * i)).take k) = true := by
      intro i hi
      have hi' := hc (i + 1) (Nat.succ_lt_succ hi)
      rwa [Nat.mul_succ, Nat.add_comm, ← List.drop_drop] at hi'
    have h₁ : vbytesOnlyStep (s.drop k) = true := vbytesOnlyStep_chunks k n (s.drop k) hlen hc'
    rw [← List.take_append_drop k s, vbytesOnlyStep_append, h₀, h₁]
    rfl

/-- **In the fixed wasm-3.0 script only `Step_read` and `Step` refer to `$vbytes_`.** -/
theorem vbytesOnlyStep_fixed : vbytesOnlyStep Scripts.Wasm30.fixed = true := by
  refine vbytesOnlyStep_chunks 250 4 _ (by simpa using fixed_length_le) fun i hi => ?_
  match i, hi with
  | 0, _ => simpa using vbytesOnlyStep_chunk0
  | 1, _ => exact vbytesOnlyStep_chunk1
  | 2, _ => exact vbytesOnlyStep_chunk2
  | 3, _ => exact vbytesOnlyStep_chunk3

/-- An item of the fixed script refers to `$vbytes_` only if it is `Step_read` or `Step`. -/
theorem item_noVBytes {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hx : ¬ (it.1 = 0 ∧ (it.2.1 = "Step_read" ∨ it.2.1 = "Step"))) :
    (1, "vbytes_") ∉ evRefs it.2.2 := by
  have hok : vbytesItemOk it = true := List.all_eq_true.mp vbytesOnlyStep_fixed it h
  intro hmem
  simp only [vbytesItemOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at hok
  rcases hok with hk | hk
  · exact hx hk
  · exact hk hmem

/-- **No definition `simEnv B` finds refers to `$vbytes_`.** -/
theorem def_noVBytes {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (simEnv B).findDef? x = some v) : (1, "vbytes_") ∉ evRefs (defDefEv v) :=
  item_noVBytes (findDef?_simEnv_item h) (by simp)

/-- **No type `simEnv B` finds refers to `$vbytes_`.** -/
theorem typ_noVBytes {B : Builtins} {x : IL.Id} {v : TypDef}
    (h : (simEnv B).findTyp? x = some v) : (1, "vbytes_") ∉ evRefs (typDefEv v) :=
  item_noVBytes (findTyp?_simEnv_item h) (by simp)

/-- **No relation other than `Step_read` and `Step` refers to `$vbytes_`.** -/
theorem rel_noVBytes {B : Builtins} {x : IL.Id} {v : RelDef}
    (h : (simEnv B).findRel? x = some v) (hr : x ≠ "Step_read") (hs : x ≠ "Step") :
    (1, "vbytes_") ∉ evRefs (relDefEv v) :=
  item_noVBytes (findRel?_simEnv_item h) (by simp [hr, hs])

/-- A rule outside `ruleUsers y rules` does not refer to `y`. -/
theorem not_mem_ruleUsers {y : String} {rules : List Rule} {i : Nat} {r : Rule}
    (hr : rules[i]? = some r) (hi : i ∉ ruleUsers y rules) : (1, y) ∉ evRefs (evRule r) := by
  intro hmem
  have hlt : i < rules.length := (List.getElem?_eq_some_iff.mp hr).1
  have hin : i ∈ ruleUsers y rules := by
    simp only [ruleUsers, List.mem_filter, List.mem_range, hr, List.contains_eq_mem,
      decide_eq_true_eq]
    exact ⟨hlt, hmem⟩
  exact hi hin

/-- `simEnv B` finds the relations of the fixed script. -/
theorem findRel?_simEnv_eq (B : Builtins) (x : IL.Id) :
    (simEnv B).findRel? x = Scripts.Wasm30.envFixed.findRel? x := by
  unfold simEnv baseEnv
  exact Env.findRel?_withBuiltins _ B x

/-- `ruleUsers` of a relation `simEnv B` finds, from `relRulesUsers`. -/
theorem ruleUsers_of_rel {B : Builtins} {x : IL.Id} {v : RelDef} {l : List Nat}
    (h : (simEnv B).findRel? x = some v) (hl : relRulesUsers "vbytes_" x = some l) :
    ruleUsers "vbytes_" v.2.2.2 = l := by
  rw [findRel?_simEnv_eq] at h
  simpa [relRulesUsers, h] using hl

/-- **No rule of `Step_pure` refers to `$vbytes_`.** -/
theorem pure_noVBytes {B : Builtins} {v : RelDef}
    (h : (simEnv B).findRel? "Step_pure" = some v) {i : Nat} {r : Rule}
    (hr : v.2.2.2[i]? = some r) : (1, "vbytes_") ∉ evRefs (evRule r) :=
  not_mem_ruleUsers hr (by rw [ruleUsers_of_rel h relRulesUsers_pure]; simp)

/-- **No rule of `Step_read` outside `msReadRules` refers to `$vbytes_`.** -/
theorem read_noVBytes {B : Builtins} {v : RelDef}
    (h : (simEnv B).findRel? "Step_read" = some v) {i : Nat} {r : Rule}
    (hr : v.2.2.2[i]? = some r) (hi : i ∉ MemSimd.msReadRules) :
    (1, "vbytes_") ∉ evRefs (evRule r) := by
  refine not_mem_ruleUsers hr ?_
  rw [ruleUsers_of_rel h relRulesUsers_read]
  intro h43
  exact hi (by simp only [List.mem_singleton] at h43; subst h43; decide)

/-- **No rule of `Step` outside `stepMSRules` refers to `$vbytes_`.** -/
theorem step_noVBytes {B : Builtins} {v : RelDef}
    (h : (simEnv B).findRel? "Step" = some v) {i : Nat} {r : Rule}
    (hr : v.2.2.2[i]? = some r) (hi : i ∉ MemSimd.stepMSRules) :
    (1, "vbytes_") ∉ evRefs (evRule r) := by
  refine not_mem_ruleUsers hr ?_
  rw [ruleUsers_of_rel h relRulesUsers_step]
  intro h23
  exact hi (by simp only [List.mem_singleton] at h23; subst h23; decide)

end Silmaril.Wasm.SpecTec.Sim.Round7.VBytes
