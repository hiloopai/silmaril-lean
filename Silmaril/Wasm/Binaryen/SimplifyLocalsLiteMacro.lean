module

public import Silmaril.Wasm.Behaviour.Semantics.CorePrefix
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteSim
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim
public import Silmaril.Wasm.SingleThreaded.InertHead

@[expose] public section

/-! # Tee/drop macro equivalence for every numerical profile

An active `v; local.tee x; drop` and `v; local.set x`, for an in-bounds local
index, have exactly the same Core behaviour set for every numerical profile and host, with an arbitrary
value-stack prefix and continuation. The three administrative steps of the
former and the one of the latter reach the very same configuration. Their
successors are unique even when the continuation's numerics or host calls are
nondeterministic.

This is a local macro certificate. The full recursive `teeDrop` module pass is
separately proved exactly equivalent at every numerical profile in
`SimplifyLocalsLiteAny.lean`, using an explicit reverse simulation and rank.
-/

namespace Silmaril.Wasm.Binaryen.SimplifyLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Inert instruction heads cannot select a host call, so their closed-host head
inversion also works with an arbitrary host. -/
theorem inert_head_inv {s : Store H} {f : Frame} {W : List Val}
    {i : Instr} {rest : List Admin} {c' : Config H}
    (he : (Admin.plain i).val? = none) (ht : i ≠ .throwRef)
    (hi : (Admin.plain i).isCallRef = false)
    (h : Step P host ⟨s, f, vals W ++ .plain i :: rest⟩ c') :
    ∃ vs args c₀, W = vs ++ args ∧ Det.Head P s f args (.plain i) c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ :=
  SingleThreaded.inert_head_inv he ht hi h

/-- The operand and result of the raw tee expansion do not depend on the profile. -/
theorem head_localTee {s : Store H} {f : Frame} {args : List Val}
    {x : LocalIdx} {c : Config H}
    (h : Det.Head P s f args (.plain (.localTee x)) c) :
    ∃ v, args = [v] ∧ c = ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩ := by
  have hv := h.fam_inv (by simp [Det.famOf])
  simp only [Det.famOf, Det.FamRel] at hv
  generalize he : (⟨s, f, vals args ++ [.plain (.localTee x)]⟩ : Config H) = cfg at hv
  cases hv with
  | @localTee s' f' y v =>
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, he⟩ := he
    obtain ⟨hargs, hx⟩ := (Det.append_singleton_inj (l₂ := [v.toAdmin])).mp he
    simp only [Admin.plain.injEq, Instr.localTee.injEq] at hx
    subst hx
    exact ⟨_, Det.vals_inj.mp hargs, rfl⟩
  | _ =>
    simp only [Config.mk.injEq] at he
    have := congrArg List.getLast? he.2.2
    simp at this

/-- The operand and result of a local store do not depend on the profile. -/
theorem head_localSet {s : Store H} {f : Frame} {args : List Val}
    {x : LocalIdx} {c : Config H}
    (h : Det.Head P s f args (.plain (.localSet x)) c) :
    ∃ v, args = [v] ∧ x.toNat < f.locals.length ∧ c = ⟨s, f.setLocal x v, []⟩ := by
  have hv := h.fam_inv (by simp [Det.famOf])
  simp only [Det.famOf, Det.FamRel] at hv
  generalize he : (⟨s, f, vals args ++ [.plain (.localSet x)]⟩ : Config H) = cfg at hv
  cases hv with
  | @localSet s' f' y v hx =>
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, he⟩ := he
    obtain ⟨hargs, hx'⟩ := (Det.append_singleton_inj (l₂ := [v.toAdmin])).mp he
    simp only [Admin.plain.injEq, Instr.localSet.injEq] at hx'
    subst hx'
    exact ⟨_, Det.vals_inj.mp hargs, hx, rfl⟩
  | _ =>
    simp only [Config.mk.injEq] at he
    have := congrArg List.getLast? he.2.2
    simp at this

/-- An active tee has a unique administrative successor, even with an arbitrary host. -/
theorem localTee_step_unique {s : Store H} {f : Frame} {vs : List Val}
    {v : Val} {x : LocalIdx} {rest : List Admin} {c' : Config H}
    (h : Step P host
      ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localTee x)] ++ rest⟩ c') :
    c' = ⟨s, f, vals vs ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest⟩ := by
  have h' : Step P host
      ⟨s, f, vals (vs ++ [v]) ++ .plain (.localTee x) :: rest⟩ c' := by
    simpa [vals, List.append_assoc] using h
  obtain ⟨pre, args, cfg, hW, hh, hc⟩ := inert_head_inv rfl (by simp) rfl h'
  obtain ⟨w, rfl, rfl⟩ := head_localTee hh
  obtain ⟨rfl, rfl⟩ := Det.append_singleton_inj.mp hW
  exact hc

/-- An active in-bounds set has a unique successor, even with an arbitrary host. -/
theorem localSet_step_unique {s : Store H} {f : Frame} {vs : List Val}
    {v : Val} {x : LocalIdx} {rest : List Admin} {c' : Config H}
    (h : Step P host
      ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localSet x)] ++ rest⟩ c') :
    c' = ⟨s, f.setLocal x v, vals vs ++ rest⟩ := by
  have h' : Step P host
      ⟨s, f, vals (vs ++ [v]) ++ .plain (.localSet x) :: rest⟩ c' := by
    simpa [vals, List.append_assoc] using h
  obtain ⟨pre, args, cfg, hW, hh, hc⟩ := inert_head_inv rfl (by simp) rfl h'
  obtain ⟨w, rfl, _, rfl⟩ := head_localSet hh
  obtain ⟨rfl, rfl⟩ := Det.append_singleton_inj.mp hW
  simpa using hc

/-- An active drop has a unique successor, even with an arbitrary host. -/
theorem drop_step_unique {s : Store H} {f : Frame} {vs : List Val}
    {v : Val} {rest : List Admin} {c' : Config H}
    (h : Step P host ⟨s, f, vals vs ++ [v.toAdmin, .plain .drop] ++ rest⟩ c') :
    c' = ⟨s, f, vals vs ++ rest⟩ := by
  have h' : Step P host ⟨s, f, vals (vs ++ [v]) ++ .plain .drop :: rest⟩ c' := by
    simpa [vals, List.append_assoc] using h
  obtain ⟨pre, args, cfg, hW, hh, hc⟩ := inert_head_inv rfl (by simp) rfl h'
  obtain ⟨w, rfl, rfl⟩ := RedundantSetLine.head_drop hh
  obtain ⟨rfl, rfl⟩ := Det.append_singleton_inj.mp hW
  simpa using hc

/-- A local store prefix can be contracted without changing any continuation behaviour. -/
theorem localSet_behaviours {s : Store H} {f : Frame} {vs : List Val}
    {v : Val} {x : LocalIdx} {rest : List Admin} (hx : x.toNat < f.locals.length) :
    behavioursOf P host ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localSet x)] ++ rest⟩ =
      behavioursOf P host ⟨s, f.setLocal x v, vals vs ++ rest⟩ := by
  apply Execution.Core.behavioursOf_eq_of_step_unique
  · simpa using Step.append_right (Step.vals_left
      (Step.variable (P := P) (host := host) (VariableStep.localSet (v := v) hx)) vs) rest
  · exact fun _ h => localSet_step_unique h

/-- Exact in-bounds local tee/drop macro equivalence for arbitrary numerical profiles and hosts.
The continuation is unrestricted and both sides use exactly the same `P` and `host`. -/
theorem teeDrop_macro_behaviours {s : Store H} {f : Frame} {vs : List Val}
    {v : Val} {x : LocalIdx} {rest : List Admin} (hx : x.toNat < f.locals.length) :
    behavioursOf P host
      ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localTee x), .plain .drop] ++ rest⟩ =
    behavioursOf P host ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localSet x)] ++ rest⟩ := by
  have htee : behavioursOf P host
      ⟨s, f, vals vs ++ [v.toAdmin, .plain (.localTee x)] ++ (.plain .drop :: rest)⟩ =
      behavioursOf P host
      ⟨s, f, vals vs ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++
        (.plain .drop :: rest)⟩ := by
    apply Execution.Core.behavioursOf_eq_of_step_unique
    · exact Step.append_right (Step.vals_left
        (Step.variable VariableStep.localTee) vs) _
    · exact fun _ h => localTee_step_unique h
  have hset := localSet_behaviours (P := P) (host := host) (s := s)
    (vs := vs ++ [v]) (v := v) (rest := .plain .drop :: rest) hx
  have hdrop : behavioursOf P host
      ⟨s, f.setLocal x v, vals vs ++ [v.toAdmin, .plain .drop] ++ rest⟩ =
      behavioursOf P host ⟨s, f.setLocal x v, vals vs ++ rest⟩ := by
    apply Execution.Core.behavioursOf_eq_of_step_unique
    · simpa using Step.append_right (Step.vals_left
        (Step.parametric (P := P) (host := host) (ParametricStep.drop v)) vs) rest
    · exact fun _ h => drop_step_unique h
  calc
    _ = behavioursOf P host
        ⟨s, f, vals vs ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++
          (.plain .drop :: rest)⟩ := by simpa [List.append_assoc] using htee
    _ = behavioursOf P host
        ⟨s, f.setLocal x v, vals vs ++ [v.toAdmin, .plain .drop] ++ rest⟩ := by
      simpa [vals, List.append_assoc] using hset
    _ = behavioursOf P host ⟨s, f.setLocal x v, vals vs ++ rest⟩ := hdrop
    _ = _ := (localSet_behaviours hx).symm

end Silmaril.Wasm.Binaryen.SimplifyLocalsLite
