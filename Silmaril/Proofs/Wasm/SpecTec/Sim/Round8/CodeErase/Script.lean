module

public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check10
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check11
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check12
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check13
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check14
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check15
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check16
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check17
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check18
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check19
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check20
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check21
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check22
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check23
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check24
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check25
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check26
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check27
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check28
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check29
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check30
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check31
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check32
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check33
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check34
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check35
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check36
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check37
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check38
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.CodeErase.Check39

/-!
# Round 8, function code erasure: the hypotheses on the wasm-3.0 script

`xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed` put the 40 kernel-checked chunks together
(`Check00`–`Check39`, 25 top-level definitions each; `fixed_length` says 40 chunks cover the
script). In `simEnv B`, every definition of `gdC` and every relation of `grC` is one of the
script's, so `Hyps.defs` and `Hyps.rels` hold at `grC`, `gdC` (`defs_simEnv`, `rels_simEnv`).

This is round 3's `Round7.EraseAll.Script` with `grC`, `gdC` and the `CODE` check: every
definition `Step` reaches but `$hostcall`, and every relation it reaches but `Step` itself, passes.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
theorem fixed_length : Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.length ≤ 25 * 40 := by
  decide +kernel

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
theorem xScriptOk_fixed : Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.all (xDefOk grC gdC) = true := by
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

/-- **Every definition of `stepReachC` has clauses that pass the syntactic check.** -/
theorem xDefsOk_fixed : xDefsOk grC gdC (defsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  rw [xDefsOk_defsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScriptOk_fixed d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.1

/-- **Every relation of `stepReachC` has rules that pass the syntactic check.** -/
theorem xRelsOk_fixed : xRelsOk grC gdC (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  rw [xRelsOk_relsOfDefs, List.all_eq_true]
  intro d hd
  have h := List.all_eq_true.1 xScriptOk_fixed d hd
  simp only [xDefOk, Bool.and_eq_true] at h
  exact h.1.2

/-- **Every conclusion alternative of every rule of every relation of `stepReachC` passes the
syntactic check.** -/
theorem xAltsOk_fixed : xAltsOk grC gdC (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
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

/-- **`Hyps.defs` at `simEnv B`.** -/
theorem defs_simEnv (B : Builtins) :
    ∀ x d, gdC x = true → (simEnv B).findDef? x = some d → ∀ cl ∈ d.2.2, xClause grC gdC cl = true := by
  intro x d hx hd cl hcl
  have h := List.all_eq_true.1 xDefsOk_fixed _ (mem_defs_of_findDef hd)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  exact h cl hcl

/-- **`Hyps.rels` at `simEnv B`.** -/
theorem rels_simEnv (B : Builtins) :
    ∀ x d, grC x = true → (simEnv B).findRel? x = some d → ∀ r ∈ d.2.2.2, xRule grC gdC r = true := by
  intro x d hx hd r hr
  have h := List.all_eq_true.1 xRelsOk_fixed _ (mem_rels_of_findRel' hd)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  exact h r hr

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll
