module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Script.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Thms
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Shape
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript10
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript11
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript12
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript13
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript14
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript15
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript16
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript17
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript18
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript19
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript20
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript21
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript22
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript23
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript24
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript25
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript26
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript27
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript28
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript29
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript30
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript31
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript32
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript33
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript34
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript35
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript36
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript37
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript38
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript39

/-!
# Round 7, the whole-evaluator erasure: the hypotheses on the wasm-3.0 script

`xDefsOk_fixed` and `xRelsOk_fixed` put the kernel-checked chunks together: 40 chunks of 25
top-level definitions of the script (`CheckScript00`–`CheckScript39`, split in round 3, pass 3, so
that each module stays well under 20 s in a loaded build), through `xDefsOk_defsOfDefs` and
`xRelsOk_relsOfDefs`. In `utf8Env B`, a definition of
`stepReachE` is `$utf8` without clauses or a definition of the script, and a relation is one of
the script's; so `Hyps.defs` and `Hyps.rels` hold at `grE`, `gdE` (`defs_utf8Env`, `rels_utf8Env`),
and `hyps_utf8Env` leaves only the builtins (`BIErase`) open at `QC c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (QC)

/-- **`List.all` from chunks of `k` entries.** -/
theorem all_chunks {α : Type} (f : α → Bool) (k : Nat) :
    ∀ (n : Nat) (m : List α), m.length ≤ k * n →
      (∀ i < n, ((m.drop (k * i)).take k).all f = true) → m.all f = true
  | 0, m, h, _ => by
    have hm : m = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (by simpa using h))
    subst hm
    rfl
  | n + 1, m, h, hc => by
    rw [← List.take_append_drop k m, List.all_append]
    have h₀ : (m.take k).all f = true := by simpa using hc 0 (Nat.succ_pos n)
    have h₁ : (m.drop k).all f = true := by
      refine all_chunks f k n (m.drop k) ?_ fun i hi => ?_
      · simp only [List.length_drop]
        rw [Nat.mul_succ] at h
        omega
      · have := hc (i + 1) (Nat.succ_lt_succ hi)
        rwa [Nat.mul_succ, Nat.add_comm, ← List.drop_drop] at this
    simp [h₀, h₁]

theorem xDefsOk_append (gr gd : String → Bool) (a b : Map DefDef) :
    xDefsOk gr gd (a ++ b) = (xDefsOk gr gd a && xDefsOk gr gd b) := by
  simp [xDefsOk, List.all_append]

theorem xRelsOk_append (gr gd : String → Bool) (a b : Map RelDef) :
    xRelsOk gr gd (a ++ b) = (xRelsOk gr gd a && xRelsOk gr gd b) := by
  simp [xRelsOk, List.all_append]

theorem xDefsOk_defsOfDefs (gr gd : String → Bool) : ∀ ds : List Def,
    xDefsOk gr gd (defsOfDefs ds) = ds.all fun d => xDefsOk gr gd (defsOfDef d)
  | [] => rfl
  | d :: ds => by
    rw [defsOfDefs, xDefsOk_append, xDefsOk_defsOfDefs gr gd ds, List.all_cons, Bool.and_comm]

theorem xAltsOk_append (gr gd : String → Bool) (a b : Map RelDef) :
    xAltsOk gr gd (a ++ b) = (xAltsOk gr gd a && xAltsOk gr gd b) := by
  simp [xAltsOk, List.all_append]

theorem xAltsOk_relsOfDefs (gr gd : String → Bool) : ∀ ds : List Def,
    xAltsOk gr gd (relsOfDefs ds) = ds.all fun d => xAltsOk gr gd (relsOfDef d)
  | [] => rfl
  | d :: ds => by
    rw [relsOfDefs, xAltsOk_append, xAltsOk_relsOfDefs gr gd ds, List.all_cons, Bool.and_comm]

theorem xRelsOk_relsOfDefs (gr gd : String → Bool) : ∀ ds : List Def,
    xRelsOk gr gd (relsOfDefs ds) = ds.all fun d => xRelsOk gr gd (relsOfDef d)
  | [] => rfl
  | d :: ds => by
    rw [relsOfDefs, xRelsOk_append, xRelsOk_relsOfDefs gr gd ds, List.all_cons, Bool.and_comm]

/-- Every top-level definition of the fixed script passes `xDefOk`. -/
theorem xScriptOk_fixed : Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.all (xDefOk grE gdE) = true := by
  refine all_chunks _ 25 40 _ fixed_length fun i hi => ?_
  match i, hi with
  | 0, _ => exact xScriptOk_chunk00
  | 1, _ => exact xScriptOk_chunk01
  | 2, _ => exact xScriptOk_chunk02
  | 3, _ => exact xScriptOk_chunk03
  | 4, _ => exact xScriptOk_chunk04
  | 5, _ => exact xScriptOk_chunk05
  | 6, _ => exact xScriptOk_chunk06
  | 7, _ => exact xScriptOk_chunk07
  | 8, _ => exact xScriptOk_chunk08
  | 9, _ => exact xScriptOk_chunk09
  | 10, _ => exact xScriptOk_chunk10
  | 11, _ => exact xScriptOk_chunk11
  | 12, _ => exact xScriptOk_chunk12
  | 13, _ => exact xScriptOk_chunk13
  | 14, _ => exact xScriptOk_chunk14
  | 15, _ => exact xScriptOk_chunk15
  | 16, _ => exact xScriptOk_chunk16
  | 17, _ => exact xScriptOk_chunk17
  | 18, _ => exact xScriptOk_chunk18
  | 19, _ => exact xScriptOk_chunk19
  | 20, _ => exact xScriptOk_chunk20
  | 21, _ => exact xScriptOk_chunk21
  | 22, _ => exact xScriptOk_chunk22
  | 23, _ => exact xScriptOk_chunk23
  | 24, _ => exact xScriptOk_chunk24
  | 25, _ => exact xScriptOk_chunk25
  | 26, _ => exact xScriptOk_chunk26
  | 27, _ => exact xScriptOk_chunk27
  | 28, _ => exact xScriptOk_chunk28
  | 29, _ => exact xScriptOk_chunk29
  | 30, _ => exact xScriptOk_chunk30
  | 31, _ => exact xScriptOk_chunk31
  | 32, _ => exact xScriptOk_chunk32
  | 33, _ => exact xScriptOk_chunk33
  | 34, _ => exact xScriptOk_chunk34
  | 35, _ => exact xScriptOk_chunk35
  | 36, _ => exact xScriptOk_chunk36
  | 37, _ => exact xScriptOk_chunk37
  | 38, _ => exact xScriptOk_chunk38
  | 39, _ => exact xScriptOk_chunk39
  | _ + 40, h => exact absurd h (by omega)

/-- **Every definition of `stepReachE` has clauses that pass the syntactic check.** -/
theorem xDefsOk_fixed : xDefsOk grE gdE (defsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  rw [xDefsOk_defsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScriptOk_fixed d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.1

/-- **Every relation of `stepReachE` has rules that pass the syntactic check.** -/
theorem xRelsOk_fixed : xRelsOk grE gdE (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  rw [xRelsOk_relsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScriptOk_fixed d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.2

/-- **Every conclusion alternative of every rule of every relation of `stepReachE` passes the
syntactic check.** -/
theorem xAltsOk_fixed : xAltsOk grE gdE (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  rw [xAltsOk_relsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScriptOk_fixed d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.2

theorem mem_of_find' {α : Type} : ∀ {m : Map α} {x : IL.Id} {v : α}, m.find? x = some v → (x, v) ∈ m
  | [], _, _, h => by simp [Map.find?] at h
  | (y, u) :: m, x, v, h => by
    simp only [Map.find?] at h
    split at h
    · cases h; rename_i hy; subst hy; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_find' h)

theorem mem_defs_of_findDef {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (simEnv B).findDef? x = some v) :
    (x, v) ∈ defsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed := by
  unfold simEnv baseEnv at h
  rw [Env.findDef?_withBuiltins, envOfScript, envOfDefs_eq] at h
  have hm := mem_of_find' h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

theorem mem_rels_of_findRel' {B : Builtins} {x : IL.Id} {v : RelDef}
    (h : (simEnv B).findRel? x = some v) :
    (x, v) ∈ relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed := by
  unfold simEnv baseEnv at h
  rw [Env.findRel?_withBuiltins, envOfScript, envOfDefs_eq] at h
  have hm := mem_of_find' h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

/-- **`Hyps.defs` at `utf8Env B`.** -/
theorem defs_utf8Env (B : Builtins) :
    ∀ x d, gdE x = true → (utf8Env B).findDef? x = some d → ∀ cl ∈ d.2.2, xClause grE gdE cl = true := by
  intro x d hx hd cl hcl
  by_cases hu : x = "utf8"
  · subst hu
    rw [findDef?_utf8Env] at hd
    cases hd
    cases hcl
  · rw [findDef?_utf8Env_of_ne B hu] at hd
    have h := List.all_eq_true.1 xDefsOk_fixed _ (mem_defs_of_findDef hd)
    simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
    exact h cl hcl

/-- **`Hyps.rels` at `utf8Env B`.** -/
theorem rels_utf8Env (B : Builtins) :
    ∀ x d, grE x = true → (utf8Env B).findRel? x = some d → ∀ r ∈ d.2.2.2, xRule grE gdE r = true := by
  intro x d hx hd r hr
  rw [findRel?_utf8Env] at hd
  have h := List.all_eq_true.1 xRelsOk_fixed _ (mem_rels_of_findRel' hd)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  exact h r hr

/-- **The hypotheses of `eraseAt` on the wasm-3.0 script**, at the swap set of a configuration with
`StripInj`, up to the builtins. -/
theorem hyps_utf8Env {H : Type} {c : Config H} (hinj : StripInj c) (B : Builtins)
    (hb : BIErase (QC c) gdE (utf8Env B)) : Hyps (QC c) grE gdE (utf8Env B) :=
  hyps_QC hinj (defs_utf8Env B) (rels_utf8Env B) hb

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
