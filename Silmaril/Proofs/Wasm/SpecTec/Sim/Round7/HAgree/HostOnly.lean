module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.HostRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.HostChunk0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.HostChunk1
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.HostChunk2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.HostChunk3

/-!
# Round 7, `BD`: where `simEnv B` can call `$hostcall`

The kernel facts of `HostChunk0`–`HostChunk3` and `HostRules`, read in `simEnv B` for every `B`
(`Round7.VBytes.Assemble` for `$hostcall`):

* `hostcallOnlyStep_fixed`: in the whole fixed script only `Step` refers to `$hostcall`;
* `item_noHostcall`, `def_noHostcall`, `typ_noHostcall`: no definition and no type that
  `simEnv B` finds refers to `$hostcall`;
* `pure_noHostcall`, `read_noHostcall`, `step_noHostcall`: no rule of `Step_pure`, no rule of
  `Step_read` and no rule of `Step` other than 8 and 9 refers to `$hostcall`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (Item items evRefs evRule defsItems_append fixed_length_le defDefEv typDefEv
  findDef?_simEnv_item findTyp?_simEnv_item)
open Round7.VBytes (not_mem_ruleUsers ruleUsers relRulesUsers findRel?_simEnv_eq)

theorem hostcallOnlyStep_append (a b : Script) :
    hostcallOnlyStep (a ++ b) = (hostcallOnlyStep a && hostcallOnlyStep b) := by
  simp [hostcallOnlyStep, items, defsItems_append, List.all_append]

/-- `hostcallOnlyStep` from chunks of `k` definitions. -/
theorem hostcallOnlyStep_chunks (k : Nat) :
    ∀ (n : Nat) (s : Script), s.length ≤ k * n →
      (∀ i < n, hostcallOnlyStep ((s.drop (k * i)).take k) = true) → hostcallOnlyStep s = true
  | 0, s, h, _ => by
    have hs : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (by simpa using h))
    rw [hs]
    rfl
  | n + 1, s, h, hc => by
    have h₀ : hostcallOnlyStep (s.take k) = true := by simpa using hc 0 (Nat.succ_pos n)
    have hlen : (s.drop k).length ≤ k * n := by
      simp only [List.length_drop]
      rw [Nat.mul_succ] at h
      omega
    have hc' : ∀ i < n, hostcallOnlyStep (((s.drop k).drop (k * i)).take k) = true := by
      intro i hi
      have hi' := hc (i + 1) (Nat.succ_lt_succ hi)
      rwa [Nat.mul_succ, Nat.add_comm, ← List.drop_drop] at hi'
    have h₁ : hostcallOnlyStep (s.drop k) = true := hostcallOnlyStep_chunks k n (s.drop k) hlen hc'
    rw [← List.take_append_drop k s, hostcallOnlyStep_append, h₀, h₁]
    rfl

/-- **In the fixed wasm-3.0 script only `Step` refers to `$hostcall`.** -/
theorem hostcallOnlyStep_fixed : hostcallOnlyStep Scripts.Wasm30.fixed = true := by
  refine hostcallOnlyStep_chunks 250 4 _ (by simpa using fixed_length_le) fun i hi => ?_
  match i, hi with
  | 0, _ => simpa using hostcallOnlyStep_chunk0
  | 1, _ => exact hostcallOnlyStep_chunk1
  | 2, _ => exact hostcallOnlyStep_chunk2
  | 3, _ => exact hostcallOnlyStep_chunk3

/-- An item of the fixed script refers to `$hostcall` only if it is `Step`. -/
theorem item_noHostcall {it : Item} (h : it ∈ items Scripts.Wasm30.fixed)
    (hx : ¬ (it.1 = 0 ∧ it.2.1 = "Step")) : (1, "hostcall") ∉ evRefs it.2.2 := by
  have hok : hostcallItemOk it = true := List.all_eq_true.mp hostcallOnlyStep_fixed it h
  intro hmem
  simp only [hostcallItemOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at hok
  rcases hok with hk | hk
  · exact hx hk
  · exact hk hmem

/-- **No definition `simEnv B` finds refers to `$hostcall`.** -/
theorem def_noHostcall {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (simEnv B).findDef? x = some v) : (1, "hostcall") ∉ evRefs (defDefEv v) :=
  item_noHostcall (findDef?_simEnv_item h) (by simp)

/-- **No type `simEnv B` finds refers to `$hostcall`.** -/
theorem typ_noHostcall {B : Builtins} {x : IL.Id} {v : TypDef}
    (h : (simEnv B).findTyp? x = some v) : (1, "hostcall") ∉ evRefs (typDefEv v) :=
  item_noHostcall (findTyp?_simEnv_item h) (by simp)

/-- `ruleUsers "hostcall"` of a relation `simEnv B` finds, from `relRulesUsers`. -/
theorem ruleUsers_of_relH {B : Builtins} {x : IL.Id} {v : RelDef} {l : List Nat}
    (h : (simEnv B).findRel? x = some v) (hl : relRulesUsers "hostcall" x = some l) :
    ruleUsers "hostcall" v.2.2.2 = l := by
  rw [findRel?_simEnv_eq] at h
  simpa [relRulesUsers, h] using hl

/-- **No rule of `Step_pure` refers to `$hostcall`.** -/
theorem pure_noHostcall {B : Builtins} {v : RelDef}
    (h : (simEnv B).findRel? "Step_pure" = some v) {i : Nat} {r : Rule}
    (hr : v.2.2.2[i]? = some r) : (1, "hostcall") ∉ evRefs (evRule r) :=
  not_mem_ruleUsers hr (by rw [ruleUsers_of_relH h relRulesUsers_pure]; simp)

/-- **No rule of `Step_read` refers to `$hostcall`.** -/
theorem read_noHostcall {B : Builtins} {v : RelDef}
    (h : (simEnv B).findRel? "Step_read" = some v) {i : Nat} {r : Rule}
    (hr : v.2.2.2[i]? = some r) : (1, "hostcall") ∉ evRefs (evRule r) :=
  not_mem_ruleUsers hr (by rw [ruleUsers_of_relH h relRulesUsers_read]; simp)

/-- **No rule of `Step` other than 8 and 9 refers to `$hostcall`.** -/
theorem step_noHostcall {B : Builtins} {v : RelDef}
    (h : (simEnv B).findRel? "Step" = some v) {i : Nat} {r : Rule}
    (hr : v.2.2.2[i]? = some r) (hi : i ≠ 8) (hi' : i ≠ 9) :
    (1, "hostcall") ∉ evRefs (evRule r) := by
  refine not_mem_ruleUsers hr ?_
  rw [ruleUsers_of_relH h relRulesUsers_step]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
