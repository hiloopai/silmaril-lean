module

public import Silmaril.Wasm.SingleThreaded.Determinism.Head

@[expose] public section

/-! # Determinism toolkit: codes that do not step

Values, a bare `TRAP`, a bare `(REF.EXN_ADDR a) THROW_REF`, and codes whose first
non-value is a branch, a `RETURN` or a `RETURN_CALL_REF` do not step.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

@[simp] theorem fnv_ref_cons (r : Ref) (l : List Admin) :
    fnv (.ref r :: l) = (.ref r :: (fnv l).1, (fnv l).2) :=
  fnv_toAdmin_cons (.ref r) l

@[simp] theorem fnv_trap_cons (l : List Admin) : fnv (.trap :: l) = ([], .trap :: l) :=
  fnv_cons_of_none rfl l

theorem fnv_headDec {P : Profile} {s : Store H} {f : Frame} {code : List Admin} {c' : Config H}
    (h : HeadDec P s f code c') :
    ∃ vs args e rest c₀, fnv code = (vs ++ args, e :: rest) ∧
      code = vals vs ++ (vals args ++ e :: rest) ∧ Head P s f args e c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  obtain ⟨vs, args, e, rest, c₀, rfl, hh, rfl⟩ := h
  refine ⟨vs, args, e, rest, c₀, ?_, rfl, hh, rfl⟩
  simp [fnv_cons_of_none hh.good.val_none]

theorem fnv_bubble {s : Store H} {f : Frame} {code : List Admin} {c' : Config H}
    (h : Bubble s f code c') :
    ∃ p q u r, (q ≠ [] ∨ u ≠ []) ∧
      ((fnv code = (p ++ q, .trap :: (u ++ r)) ∧ code = vals (p ++ q) ++ .trap :: (u ++ r) ∧
          c' = ⟨s, f, vals p ++ [.trap] ++ r⟩) ∨
       (∃ a, fnv code = (p ++ q ++ [.ref (.exn a)], .plain .throwRef :: (u ++ r)) ∧
          code = vals (p ++ q ++ [.ref (.exn a)]) ++ .plain .throwRef :: (u ++ r) ∧
          c' = ⟨s, f, vals p ++ [.ref (.exn a), .plain .throwRef] ++ r⟩)) := by
  obtain ⟨p, q, X, u, r, rfl, hX, hqu, rfl⟩ := h
  refine ⟨p, q, u, r, hqu, ?_⟩
  rcases hX with rfl | ⟨a, rfl⟩
  · left; simp
  · right
    refine ⟨a, ?_, ?_, rfl⟩
    · simp [fnv_cons_of_none (a := .plain .throwRef) rfl]
    · (simp; rfl)

theorem not_step_vals {P : Profile} {s : Store H} {f : Frame} {W : List Val} {c : Config H}
    (h : Step P noHost ⟨s, f, vals W⟩ c) : False := by
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hf, -, -, -⟩ := fnv_headDec hd
    simp at hf
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb <;> simp at hf

/-- The first non-value of a stepping code is not blocked. -/
theorem not_step_blocked {P : Profile} {s : Store H} {f : Frame} {code : List Admin}
    {c : Config H} (h : Step P noHost ⟨s, f, code⟩ c) {W : List Val} {e : Admin}
    {rest : List Admin} (hf : fnv code = (W, e :: rest)) : ¬ Blocked e := by
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e', rest', c₀, hf', -, hh, -⟩ := fnv_headDec hd
    simp only at hf'
    rw [hf] at hf'
    simp only [Prod.mk.injEq, List.cons.injEq] at hf'
    rw [hf'.2.1]
    exact hh.good.not_blocked
  · obtain ⟨p, q, u, r, -, ⟨hf', -⟩ | ⟨a, hf', -⟩⟩ := fnv_bubble hb <;> simp only at hf' <;>
      rw [hf] at hf' <;> simp only [Prod.mk.injEq, List.cons.injEq] at hf' <;> rw [hf'.2.1] <;>
      rintro (⟨l, h⟩ | h | h) <;> cases h

theorem not_step_trap {P : Profile} {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.trap]⟩ c) : False := by
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hf, -, hh, -⟩ := fnv_headDec hd
    simp only [fnv_trap_cons, Prod.mk.injEq, List.cons.injEq] at hf
    exact hh.good.ne_trap hf.2.1.symm
  · obtain ⟨p, q, u, r, hqu, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb
    · simp only [fnv_trap_cons, Prod.mk.injEq, List.cons.injEq, true_and] at hf
      simp only [List.nil_eq_append_iff] at hf
      exact hqu.elim (fun hq => hq hf.1.2) (fun hu => hu hf.2.1)
    · simp at hf

theorem not_step_throwing {P : Profile} {s : Store H} {f : Frame} {a : Nat} {c : Config H}
    (h : Step P noHost ⟨s, f, [.ref (.exn a), .plain .throwRef]⟩ c) : False := by
  have hf0 : fnv [.ref (.exn a), .plain .throwRef] = ([.ref (.exn a)], [.plain .throwRef]) := by
    simp [fnv_cons_of_none (a := .plain .throwRef) rfl]
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hf, -, hh, -⟩ := fnv_headDec hd
    simp only at hf
    rw [hf0] at hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hf
    obtain ⟨h1, rfl, -⟩ := hf
    have := hh.good.throwRef rfl
    subst this
    have := congrArg List.getLast? h1
    simp at this
  · obtain ⟨p, q, u, r, hqu, ⟨hf, -⟩ | ⟨a', hf, -⟩⟩ := fnv_bubble hb
    · simp only at hf; rw [hf0] at hf; simp at hf
    · simp only at hf
      rw [hf0] at hf
      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hf
      obtain ⟨h1, h2⟩ := hf
      have h1' := congrArg List.length h1
      simp only [List.length_append, List.length_cons, List.length_nil] at h1'
      rcases hqu with hq | hu
      · exact hq (List.eq_nil_of_length_eq_zero (by omega))
      · exact hu (by simp_all)

end Silmaril.Wasm.SingleThreaded.Det
