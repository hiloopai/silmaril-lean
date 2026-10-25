module

public import Silmaril.Wasm.Link.AdminRelation

/-! # Inverting paired administrative control

Runtime values are identical. Non-value source instructions, labels and frames
retain their outer shape, with the actual rewrite and nested relation exposed.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.AdminRelation

open Silmaril.Wasm.Execution.Core

theorem Control.nil_left {mode source target ys}
    (h : Control mode source target [] ys) : ys = [] := by cases h; rfl

theorem Control.values_prefix {mode source target vs xs ys}
    (h : Control mode source target (vals vs ++ xs) ys) :
    ∃ rest, ys = vals vs ++ rest ∧ Control mode source target xs rest := by
  obtain ⟨pre, rest, rfl, hp, hr⟩ := h.split
  exact ⟨rest, by rw [hp.values_left], hr⟩

theorem Control.plain_cons {mode source target i xs ys}
    (h : Control mode source target (.plain i :: xs) ys)
    (nonvalue : (Admin.plain i).val? = none)
    (nonthrow : i ≠ .throwRef := by intro h; cases h) :
    ∃ j rest, ys = .plain j :: rest ∧ Instruction mode i j ∧
      Control mode source target xs rest := by
  generalize ha : Admin.plain i = a at h
  cases h
  case plain rewrite tail => cases ha; exact ⟨_, _, rfl, rewrite, tail⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha, nonvalue] at hv
    cases hv
  case throwRef rest => cases ha; exact False.elim (nonthrow rfl)
  all_goals cases ha

theorem Control.values_instruction {mode source target vs i ys}
    (h : Control mode source target (vals vs ++ [.plain i]) ys)
    (nonvalue : (Admin.plain i).val? = none)
    (nonthrow : i ≠ .throwRef := by intro h; cases h) :
    ∃ j, ys = vals vs ++ [.plain j] ∧ Instruction mode i j := by
  obtain ⟨rest, rfl, hr⟩ := h.values_prefix
  obtain ⟨j, tail, rfl, rewrite, empty⟩ := hr.plain_cons nonvalue nonthrow
  rw [empty.nil_left]
  exact ⟨j, rfl, rewrite⟩

theorem Control.ref_cons {mode source target r xs ys}
    (h : Control mode source target (.ref r :: xs) ys) :
    ∃ rest, ys = .ref r :: rest ∧ Control mode source target xs rest := by
  cases ys with
  | nil => have := h.length_eq; simp only [List.length_cons, List.length_nil] at this; omega
  | cons a ys =>
    have hv := h.head_value (v := .ref r) rfl
    exact ⟨ys, by rw [hv]; rfl, h.tail⟩

theorem Control.label_cons {mode source target n cont body xs ys}
    (h : Control mode source target (.label n cont body :: xs) ys) :
    ∃ cont' body' rest, ys = .label n cont' body' :: rest ∧
      Instructions mode cont cont' ∧ Control mode source target body body' ∧
      Control mode source target xs rest := by
  generalize ha : Admin.label n cont body = a at h
  cases h
  case label continuation inner rest => cases ha; exact ⟨_, _, _, rfl, continuation, inner, rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?, reduceCtorEq] at hv
  all_goals cases ha

theorem Control.frame_cons {mode source target n f body xs ys}
    (h : Control mode source target (.frame n f body :: xs) ys) :
    ∃ innerMode f' body' rest, ys = .frame n f' body' :: rest ∧
      Frames innerMode f f' ∧ Control innerMode f.module f'.module body body' ∧
      Control mode source target xs rest := by
  generalize ha : Admin.frame n f body = a at h
  cases h
  case frame frames inner rest => cases ha; exact ⟨_, _, _, _, rfl, frames, inner, rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?, reduceCtorEq] at hv
  all_goals cases ha

theorem Control.handler_cons {mode source target n catches body xs ys}
    (h : Control mode source target (.handler n catches body :: xs) ys) :
    mode = .same ∧ source = target ∧ ∃ body' rest,
      ys = .handler n catches body' :: rest ∧
      Control .same source source body body' ∧ Control .same source source xs rest := by
  generalize ha : Admin.handler n catches body = a at h
  cases h
  case handler inner rest => cases ha; exact ⟨rfl, rfl, _, _, rfl, inner, rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?, reduceCtorEq] at hv
  all_goals cases ha

theorem Control.trap_cons {mode source target xs ys}
    (h : Control mode source target (.trap :: xs) ys) :
    ∃ rest, ys = .trap :: rest ∧ Control mode source target xs rest := by
  generalize ha : Admin.trap = a at h
  cases h
  case trap rest => cases ha; exact ⟨_, rfl, rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?, reduceCtorEq] at hv
  all_goals cases ha

theorem Control.label_singleton {mode source target n cont body ys}
    (h : Control mode source target [.label n cont body] ys) :
    ∃ cont' body', ys = [.label n cont' body'] ∧ Instructions mode cont cont' ∧
      Control mode source target body body' := by
  obtain ⟨cont', body', rest, rfl, hc, hb, hr⟩ := h.label_cons
  rw [hr.nil_left]
  exact ⟨cont', body', rfl, hc, hb⟩

theorem Control.frame_singleton {mode source target n f body ys}
    (h : Control mode source target [.frame n f body] ys) :
    ∃ innerMode f' body', ys = [.frame n f' body'] ∧ Frames innerMode f f' ∧
      Control innerMode f.module f'.module body body' := by
  obtain ⟨innerMode, f', body', rest, rfl, hf, hb, hr⟩ := h.frame_cons
  rw [hr.nil_left]
  exact ⟨innerMode, f', body', rfl, hf, hb⟩

theorem Control.trap_singleton {mode source target ys}
    (h : Control mode source target [.trap] ys) : ys = [.trap] := by
  obtain ⟨rest, rfl, hr⟩ := h.trap_cons
  rw [hr.nil_left]

theorem Control.throwRef_cons {mode source target xs ys}
    (h : Control mode source target (.plain .throwRef :: xs) ys) :
    ∃ rest, ys = .plain .throwRef :: rest ∧ Control mode source target xs rest := by
  generalize ha : Admin.plain .throwRef = a at h
  cases h
  case plain rewrite rest =>
    cases ha
    cases mode with
    | same => change _ = _ at rewrite; subst rewrite; exact ⟨_, rfl, rest⟩
    | relocated r => simp only [Instruction, instruction?, reduceCtorEq] at rewrite
  case throwRef rest => cases ha; exact ⟨_, rfl, rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?, reduceCtorEq] at hv
  all_goals cases ha

theorem Control.throwing_left {mode source target address ys}
    (h : Control mode source target (throwing address) ys) : ys = throwing address := by
  obtain ⟨rest, rfl, tail⟩ := h.ref_cons
  obtain ⟨rest, rfl, empty⟩ := tail.throwRef_cons
  rw [empty.nil_left]

end Silmaril.Wasm.Link.GC.AdminRelation
