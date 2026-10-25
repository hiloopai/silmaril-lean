module

public import Silmaril.Wasm.Binaryen.ConstSelectSim
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro

@[expose] public section

/-! # Constant-select macros with explicit operand availability

An active select with two operand values has a unique administrative successor
for every numerical profile and host. This gives exact local select/drop
equivalence with an arbitrary continuation when both operands are present.

Operand availability is essential: with only one operand, folded drop steps
while the original select is stuck. The final theorem proves that witness.
These are local certificates. `ConstSelectAny.lean` lifts them through a typed
reverse closure to prove the full recursive pass at every numerical profile.
-/

namespace Silmaril.Wasm.Binaryen.ConstSelect

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Select has a unique successor once both operands and its i32 condition are available. -/
theorem select_step_unique {s : Store H} {f : Frame} {vs : List Val}
    {a b : Val} {c : BitVec 32} {ts : Option (List ValType)} {rest : List Admin} {c' : Config H}
    (h : Step P host
      ⟨s, f, vals vs ++ [a.toAdmin, b.toAdmin, constI32 c, .plain (.select ts)] ++ rest⟩ c') :
    c' = ⟨s, f, vals vs ++ [(if c = 0 then b else a).toAdmin] ++ rest⟩ := by
  have h' : Step P host
      ⟨s, f, vals (vs ++ [a, b, Val.i32 c]) ++ .plain (.select ts) :: rest⟩ c' := by
    simpa [vals, Val.i32, constI32, List.append_assoc] using h
  obtain ⟨pre, args, cfg, hW, hh, he⟩ :=
    SimplifyLocalsLite.inert_head_inv rfl (by simp) rfl h'
  obtain ⟨a', b', k, rfl, rfl⟩ := head_select hh
  have hW' : ((vs ++ [a]) ++ [b]) ++ [Val.i32 c] =
      ((pre ++ [a']) ++ [b']) ++ [Val.i32 k] := by simpa [Val.i32, List.append_assoc] using hW
  obtain ⟨hab, hk⟩ := Det.append_singleton_inj.mp hW'
  obtain ⟨ha, hb⟩ := Det.append_singleton_inj.mp hab
  obtain ⟨hpre, ha'⟩ := Det.append_singleton_inj.mp ha
  subst pre a' b'
  have hk' : c = k := by cases hk; rfl
  subst k
  exact he

/-- Contract an active select without constraining any later numerical or host choice. -/
theorem select_behaviours {s : Store H} {f : Frame} {vs : List Val}
    {a b : Val} {c : BitVec 32} {ts : Option (List ValType)} {rest : List Admin} :
    behavioursOf P host
      ⟨s, f, vals vs ++ [a.toAdmin, b.toAdmin, constI32 c, .plain (.select ts)] ++ rest⟩ =
    behavioursOf P host ⟨s, f, vals vs ++ [(if c = 0 then b else a).toAdmin] ++ rest⟩ := by
  apply behavioursOf_eq_of_step_unique
  · apply Step.append_right
    apply Step.vals_left
    by_cases hc : c = 0
    · subst c
      simpa only [↓reduceIte] using Step.parametric (P := P) (host := host)
        (s := s) (f := f) (ParametricStep.selectFalse a b ts)
    · simpa only [hc, ↓reduceIte] using Step.parametric (P := P) (host := host)
        (s := s) (f := f) (ParametricStep.selectTrue (v₁ := a) (v₂ := b) (ts := ts) hc)
  · exact fun _ h => select_step_unique h

/-- Nonzero constant select and folded drop have exactly the same local behaviour
set when both operand values are explicitly present, for every profile and host. -/
theorem selectTrue_macro_behaviours {s : Store H} {f : Frame} {vs : List Val}
    {a b : Val} {c : BitVec 32} {ts : Option (List ValType)} {rest : List Admin} (hc : c ≠ 0) :
    behavioursOf P host
      ⟨s, f, vals vs ++ [a.toAdmin, b.toAdmin, constI32 c, .plain (.select ts)] ++ rest⟩ =
    behavioursOf P host ⟨s, f, vals vs ++ [a.toAdmin, b.toAdmin, .plain .drop] ++ rest⟩ := by
  have hs := select_behaviours (P := P) (host := host) (s := s) (f := f)
    (vs := vs) (a := a) (b := b) (c := c) (ts := ts) (rest := rest)
  rw [ite_eq_right hc] at hs
  have hd : behavioursOf P host
      ⟨s, f, vals vs ++ [a.toAdmin, b.toAdmin, .plain .drop] ++ rest⟩ =
      behavioursOf P host ⟨s, f, vals vs ++ [a.toAdmin] ++ rest⟩ := by
    apply behavioursOf_eq_of_step_unique
    · simpa [vals, List.append_assoc] using Step.append_right
        (Step.vals_left (Step.parametric (P := P) (host := host) (s := s) (f := f)
          (ParametricStep.drop b)) (vs ++ [a])) rest
    · intro c' h
      have h' : Step P host
          ⟨s, f, vals (vs ++ [a]) ++ [b.toAdmin, .plain .drop] ++ rest⟩ c' := by
        simpa [vals, List.append_assoc] using h
      simpa [vals, List.append_assoc] using SimplifyLocalsLite.drop_step_unique h'
  exact hs.trans hd.symm

/-- A short-stack witness: drop can step with one operand, while the original
constant-select redex needs two. This excludes a stack-unrestricted converse. -/
theorem selectTrue_short_stack {s : Store H} {f : Frame} (v : Val)
    (ts : Option (List ValType)) :
    Step P host ⟨s, f, [v.toAdmin, .plain .drop]⟩ ⟨s, f, []⟩ ∧
      ¬ ∃ c', Step P host ⟨s, f, [v.toAdmin, constI32 1, .plain (.select ts)]⟩ c' := by
  refine ⟨Step.parametric (ParametricStep.drop v), ?_⟩
  rintro ⟨c', h⟩
  have h' : Step P host
      ⟨s, f, vals [v, Val.i32 1] ++ .plain (.select ts) :: []⟩ c' := by
    simpa [vals, Val.i32, constI32] using h
  obtain ⟨pre, args, cfg, hW, hh, he⟩ :=
    SimplifyLocalsLite.inert_head_inv rfl (by simp) rfl h'
  obtain ⟨a, b, c, rfl, rfl⟩ := head_select hh
  have hlen := congrArg List.length hW
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end Silmaril.Wasm.Binaryen.ConstSelect
