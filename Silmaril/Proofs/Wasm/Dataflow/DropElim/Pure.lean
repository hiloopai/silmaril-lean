module

public import Silmaril.Proofs.Wasm.Dataflow.DropElim.Match

/-!
# an earlier step of the two-pass DCE: dropped producers

`erase_pure_match`: a removable producer followed by `drop` is matched by dropping its
operands (one target step or more), or by a stutter for values and `local.get`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf noHost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Dropped producers -/

/-- A parametric step of `drop` consumes one value. -/
theorem parametric_drop_inv {args : List Val} {is' : List Admin}
    (h : ParametricStep (vals args ++ [.plain .drop]) is') : ∃ v, args = [v] ∧ is' = [] := by
  generalize he : vals args ++ [Admin.plain .drop] = code at h
  cases h with
  | drop v =>
    have he' : vals args = vals [v] := List.append_cancel_right (by simpa [vals] using he)
    exact ⟨v, SingleThreaded.Det.vals_inj.mp he', rfl⟩
  | _ =>
    have hlast := congrArg List.getLast? he
    simp at hlast

/-- A head `drop` removes the last value, for every profile and host. -/
theorem erase_drop_inv {s : Store H} {f : Frame} {vs : List Val} {c : Config H}
    (h : Step P host ⟨s, f, vals vs ++ [.plain .drop]⟩ c) :
    ∃ ws v, vs = ws ++ [v] ∧ c = ⟨s, f, vals ws⟩ := by
  have hn : Step P noHost ⟨s, f, vals vs ++ .plain .drop :: []⟩ c :=
    Step.noHost_of_frag h (by simp [fragInstr])
  obtain ⟨ws, args, c₀, rfl, hh, rfl⟩ := Step.head_inv hn rfl (by simp) (by simp)
  obtain ⟨is', hp, rfl⟩ : ∃ is', ParametricStep (vals args ++ [.plain .drop]) is' ∧
      c₀ = ⟨s, f, is'⟩ := by
    simpa [famOf, SingleThreaded.Det.FamRel] using hh.fam_inv (by simp [famOf])
  obtain ⟨v, rfl, rfl⟩ := parametric_drop_inv hp
  exact ⟨ws, v, rfl, by simp⟩

theorem pure_zero_size {a : Admin} (hp : adminPureArity? a = some 0) (hv : a.val? = none) :
    1 < adminSize a := by
  cases a with
  | plain i => cases i <;> simp_all [adminPureArity?, pureArity?, Admin.val?, adminSize]
  | _ => simp_all [adminPureArity?, Admin.val?]

/-- A value followed by `drop`: the source drops it, the target already has. -/
theorem erase_val_drop_match {s s' : Store H} {f f' : Frame} {vs : List Val} {v : Val}
    {rest rest' es' : List Admin} (hr : Erase rest rest')
    (h : Step P host ⟨s, f, vals vs ++ [v.toAdmin, .plain .drop] ++ rest⟩ ⟨s', f', es'⟩) :
    EraseMatched P host ⟨s, f, vals vs ++ [v.toAdmin, .plain .drop] ++ rest⟩ ⟨s', f', es'⟩
      ⟨s, f, vals vs ++ List.replicate 0 (.plain .drop) ++ rest'⟩ := by
  have hs : Step P host ⟨s, f, vals (vs ++ [v]) ++ .plain .drop :: rest⟩ ⟨s', f', es'⟩ := by
    simpa [vals] using h
  rcases Sim.Step.split_head rfl hs with ⟨ws, us, is', hvs, hh, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · obtain ⟨pre, last, rfl, hc⟩ := erase_drop_inv hh
    obtain ⟨rfl, rfl, rfl⟩ : s' = s ∧ f' = f ∧ is' = vals pre := by simpa using hc
    have hi : vs ++ [v] = (ws ++ pre) ++ [last] := by rw [hvs]; simp
    obtain ⟨rfl, -⟩ := List.append_inj' hi rfl
    refine ⟨⟨_, _, vals (ws ++ pre) ++ rest'⟩, ⟨rfl, rfl, ?_⟩, .inr ⟨by simp, ?_⟩⟩
    · simpa using (Erase.refl (vals (ws ++ pre))).append hr
    · simp only [codeSize_append, codeSize_vals, codeSize_cons, adminSize, List.length_append,
        adminSize_toAdmin]
      omega
  · cases he
  · cases he

/-- A removable instruction followed by `drop`: the source computes a value and the target
drops the operands. -/
theorem erase_instr_drop_match {s s' : Store H} {f f' : Frame} {vs : List Val} {i : Instr}
    {n : Nat} {rest rest' es' : List Admin} (hi : pureArity? i = some n)
    (hv : (Admin.plain i).val? = none) (hr : Erase rest rest')
    (h : Step P host ⟨s, f, vals vs ++ [.plain i, .plain .drop] ++ rest⟩ ⟨s', f', es'⟩) :
    EraseMatched P host ⟨s, f, vals vs ++ [.plain i, .plain .drop] ++ rest⟩ ⟨s', f', es'⟩
      ⟨s, f, vals vs ++ List.replicate n (.plain .drop) ++ rest'⟩ := by
  have hs : Step P host ⟨s, f, vals vs ++ .plain i :: (.plain .drop :: rest)⟩ ⟨s', f', es'⟩ := by
    simpa using h
  rcases Sim.Step.split_head hv hs with ⟨ws, us, is', rfl, hh, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · obtain ⟨pre, args, v, rfl, hn, hc⟩ := pureArity_step_vals hi hh
    obtain ⟨rfl, rfl, rfl⟩ : s' = s ∧ f' = f ∧ is' = vals pre ++ [v.toAdmin] := by simpa using hc
    refine ⟨⟨_, _, vals (ws ++ pre) ++ rest'⟩, ⟨rfl, rfl, ?_⟩, ?_⟩
    · simpa using ((Erase.refl (vals (ws ++ pre))).append (Erase.val_drop v)).append hr
    · by_cases hargs : args = []
      · subst hargs
        have hn0 : n = 0 := by simpa using hn.symm
        subst hn0
        have hsize := pure_zero_size (a := .plain i) hi hv
        exact .inr ⟨by simp, by simp [codeSize_cons]; omega⟩
      · have ht := transGen_drops (P := P) (host := host) (s := s') (f := f') (ws ++ pre) args
          rest' hargs
        exact .inl (by simpa [hn] using ht)
  · cases he
  · cases he
    simp [pureArity?] at hi

/-- A dropped pure producer is matched by dropping its operands, or by a strictly
decreasing stutter for values and `local.get`. -/
theorem erase_pure_match {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin} {n : Nat}
    {rest rest' es' : List Admin} (hp : adminPureArity? a = some n) (hr : Erase rest rest')
    (h : Step P host ⟨s, f, vals vs ++ [a, .plain .drop] ++ rest⟩ ⟨s', f', es'⟩) :
    EraseMatched P host ⟨s, f, vals vs ++ [a, .plain .drop] ++ rest⟩ ⟨s', f', es'⟩
      ⟨s, f, vals vs ++ List.replicate n (.plain .drop) ++ rest'⟩ := by
  cases hv : a.val? with
  | some v =>
    obtain rfl := Admin.eq_of_val? hv
    obtain rfl : n = 0 := by simpa using hp.symm
    exact erase_val_drop_match hr h
  | none =>
    obtain ⟨i, rfl⟩ : ∃ i, a = .plain i := by
      cases a <;> first | exact ⟨_, rfl⟩ | simp [adminPureArity?, Admin.val?] at hp hv
    exact erase_instr_drop_match hp hv hr h


end Silmaril.Wasm.Dataflow
