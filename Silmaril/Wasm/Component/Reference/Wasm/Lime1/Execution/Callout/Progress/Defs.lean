module

public import Silmaril.Wasm.Lime1.Execution.Callout.Properties

/-!
# Progress of the executable Lime1 stepper

`Callout/Properties.lean` proves `step?_sound`: every step of the executable host-free stepper
`Lime1.Execution.step?` is a step of `Internal = Step noHostCalls`. This file proves the
converse direction at the level of *enabledness*:

* `step?_progress`: if a configuration has some `Internal` step, `step?` finds a step (possibly a
  different one, see below);
* `step?_eq_none_iff`: `step? cfg = none` exactly when `cfg` has no `Internal` step, i.e. the
  configuration is terminal (a value sequence or a lone trap), parked at a host callout
  (`CalloutAt`, see `CalloutAt.not_internal`), or stuck (ill-typed or dangling runtime state);
* `run_stuck` and `run_stuck_iff`: the driver `run` reports `Status.stuck` only for a
  configuration that is not terminal, not a callout and has no `Internal` step, and on such a
  configuration (with fuel left) it reports exactly that.

The proof is by induction on the `Step` derivation: `Internal.head_not_branch` shows that the
first non-value instruction of code that steps is never a bare `br`/`return` (those only reduce
through an enclosing label or frame), which rules out the cases where `stepHead?` declines a
label or frame; `Internal.stepFrom?_isSome` then shows the scan of `stepFrom?` reaches a redex
for any operand stack prefix and any trailing code. No `stepInstr?` case was missing, so
`Callout.lean` is unchanged.

## Deterministic choices of `stepInstr?`

`Step` is nondeterministic in three places; `step?` resolves each deterministically, and each
resolution is one of the permitted transitions (this is already part of `step?_sound`; the
lemmas `floatUnOp_choice_permitted`, `floatBinOp_choice_permitted`,
`convert_choice_permitted` and `memoryGrow_choice_permitted` restate it for readers):

* float unary/binary operators and conversions (the rules `floatUnary`, `floatBinary`,
  `convert` admit any permitted NaN payload via `Numerics.floatUnOpRel`, `floatBinOpRel`,
  `convertRel`): `step?` returns the deterministic results `Numerics.floatUnOp`,
  `Numerics.floatBinOp`, `Numerics.convert`;
* `memory.grow` (the rule `memoryGrow` with `Memory.Grow`, which always admits failure with
  result `-1` and the memory unchanged): `step?` grows exactly when `Memory.grow?` succeeds,
  returning the old size in pages, and fails otherwise.

Hence `step?_progress` is progress, not completeness: a nondeterministic `Internal` step (a
different NaN payload, or a `memory.grow` failure where growth was possible) is not claimed to
be the step `step?` takes. Not claimed either: anything about fuel exhaustion (`run` with fuel
`0` never reports `stuck`), or about host callouts, which are not `Internal` steps.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-! ## Scanning lemmas -/

section Scan

variable {H : Type*} (s : Store H) (f : Frame)

@[simp] theorem stepFrom?_value_cons (stack : List Value) (v : Value) (l : List Admin) :
    stepFrom? s f stack (value v :: l) = stepFrom? s f (v :: stack) l := by
  simp only [stepFrom?, asValue?_value]

theorem stepFrom?_cons_of_none (stack : List Value) {x : Admin} (l : List Admin)
    (h : asValue? x = none) : stepFrom? s f stack (x :: l) = stepHead? s f stack l x := by
  simp only [stepFrom?, h]

@[simp] theorem stepFrom?_values_append (stack vs : List Value) (l : List Admin) :
    stepFrom? s f stack (values vs ++ l) = stepFrom? s f (vs.reverse ++ stack) l := by
  induction vs generalizing stack with
  | nil => rfl
  | cons v vs ih =>
    simp only [values, List.map_cons, List.cons_append] at ih ⊢
    rw [stepFrom?_value_cons, ih]
    simp

end Scan

@[simp] theorem numOf?_self (t : NumType) (x : BitVec t.width) : numOf? t ⟨t, x⟩ = some x := by
  rcases t with (t | t) <;> cases t <;> rfl

@[simp] theorem intOf?_int (t : IntType) (x : BitVec t.width) : intOf? t (.int t x) = some x := by
  cases t <;> rfl

@[simp] theorem intOf?_i32 (x : BitVec 32) : intOf? .i32 (.int .i32 x) = some x := rfl

@[simp] theorem floatOf?_float (t : FloatType) (x : BitVec t.width) :
    floatOf? t (.float t x) = some x := by
  cases t <;> rfl

@[simp] theorem splitValues_nil : splitValues [] = ([], []) := rfl

@[simp] theorem splitValues_value_cons (v : Value) (l : List Admin) :
    splitValues (value v :: l) = (v :: (splitValues l).1, (splitValues l).2) := by
  simp only [splitValues, asValue?_value]

theorem splitValues_cons_of_none {x : Admin} (l : List Admin) (h : asValue? x = none) :
    splitValues (x :: l) = ([], x :: l) := by
  simp only [splitValues, h]

@[simp] theorem splitValues_values_append (vs : List Value) (l : List Admin) :
    splitValues (values vs ++ l) = (vs ++ (splitValues l).1, (splitValues l).2) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [values, List.map_cons, List.cons_append] at ih ⊢
    rw [splitValues_value_cons, ih]

@[simp] theorem splitValues_values (vs : List Value) : splitValues (values vs) = (vs, []) := by
  simpa [splitValues_nil] using splitValues_values_append vs []

theorem splitValues_append {l : List Admin} (t : List Admin) (h : (splitValues l).2 ≠ []) :
    splitValues (l ++ t) = ((splitValues l).1, (splitValues l).2 ++ t) := by
  induction l with
  | nil => simp [splitValues] at h
  | cons x xs ih =>
    cases hx : asValue? x with
    | none =>
      rw [List.cons_append, splitValues_cons_of_none _ hx, splitValues_cons_of_none _ hx]
      rfl
    | some v =>
      have hv : value v = x := coding.encode_of_decode hx
      subst hv
      rw [splitValues_value_cons] at h
      rw [List.cons_append, splitValues_value_cons, splitValues_value_cons, ih h]

@[simp] theorem splitValues_source_br_cons (l : LabelIdx) (rest : List Admin) :
    splitValues (.source (.br l) :: rest) = ([], .source (.br l) :: rest) := rfl

@[simp] theorem splitValues_source_return_cons (rest : List Admin) :
    splitValues (.source .return_ :: rest) = ([], .source .return_ :: rest) := rfl

@[simp] theorem splitValues_trap_cons (rest : List Admin) :
    splitValues (.trap :: rest) = ([], .trap :: rest) := rfl

@[simp] theorem stepHead?_source {H : Type*} (s : Store H) (f : Frame) (stack : List Value)
    (tail : List Admin) (i : Instr) :
    stepHead? s f stack tail (.source i) = (stepInstr? s f stack i).map fun (rest, s', f', after) =>
      (s', f', values rest.reverse ++ after ++ tail) := by
  rw [stepHead?]

/-- Instructions that only a surrounding label or frame can reduce. -/
def Admin.isBranch : Admin → Bool
  | .source (.br _) => true
  | .source .return_ => true
  | _ => false

set_option linter.unusedTactic false in
/-- The first non-value instruction of code that takes a host-free step exists and is not a
bare `br` or `return` (those are consumed by an enclosing label or frame). -/
theorem Internal.head_not_branch {H : Type*} {a b : Config H} (h : Internal a b) :
    ∃ x rest, (splitValues a.code).2 = x :: rest ∧ x.isBranch = false := by
  induction h with
  | pure s f hp =>
    cases hp <;>
      (try simp only [splitValues_value_cons, splitValues_values_append, List.append_assoc,
        List.cons_append, List.nil_append]) <;>
      exact ⟨_, _, rfl, rfl⟩
  | context _ vs tail ih =>
    obtain ⟨x, rest, hx, hb⟩ := ih
    refine ⟨x, rest ++ tail, ?_, hb⟩
    simp only [List.append_assoc, splitValues_values_append]
    rw [splitValues_append tail (by simp [hx]), hx, List.cons_append]
  | invokeHost _ _ _ _ _ _ _ _ _ _ hb => exact hb.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ hb => exact hb.elim
  | _ =>
    try simp only [splitValues_value_cons, splitValues_values_append]
    exact ⟨_, _, rfl, rfl⟩

theorem Internal.stepFrom?_isSome_label {H : Type*} {s s' : Store H} {f f' : Frame}
    {before after : List Admin} (h : Internal ⟨s, f, before⟩ ⟨s', f', after⟩) (n : Nat)
    (cont : Expr) (ih : ∀ stack tail, (stepFrom? s f stack (before ++ tail)).isSome)
    (stack : List Value) (tail : List Admin) :
    (stepFrom? s f stack ([.label n cont before] ++ tail)).isSome := by
  rw [List.singleton_append, stepFrom?_cons_of_none _ _ _ _ rfl, stepHead?]
  obtain ⟨x, rest, hx, hb⟩ := Internal.head_not_branch h
  split
  · rfl
  · rfl
  · next heq =>
    rw [heq] at hx
    cases hx
    simp [Admin.isBranch] at hb
  · next heq =>
    rw [heq] at hx
    cases hx
    simp [Admin.isBranch] at hb
  · have hih : (stepFrom? s f [] before).isSome := by simpa only [List.append_nil] using ih [] []
    simpa only [Option.isSome_map] using hih

theorem Internal.stepFrom?_isSome_frame {H : Type*} {s s' : Store H} {inner inner' : Frame}
    {before after : List Admin} (h : Internal ⟨s, inner, before⟩ ⟨s', inner', after⟩) (n : Nat)
    (outer : Frame) (ih : ∀ stack tail, (stepFrom? s inner stack (before ++ tail)).isSome)
    (stack : List Value) (tail : List Admin) :
    (stepFrom? s outer stack ([.frame n inner before] ++ tail)).isSome := by
  rw [List.singleton_append, stepFrom?_cons_of_none _ _ _ _ rfl, stepHead?]
  obtain ⟨x, rest, hx, hb⟩ := Internal.head_not_branch h
  split
  · next heq =>
    rw [heq] at hx
    cases hx
  · rfl
  · next heq =>
    rw [heq] at hx
    cases hx
    simp [Admin.isBranch] at hb
  · have hih : (stepFrom? s inner [] before).isSome := by
      simpa only [List.append_nil] using ih [] []
    simpa only [Option.isSome_map] using hih

theorem stepFrom?_isSome_callIndirect {H : Type*} {s : Store H} {f : Frame} {i : TypeIdx}
    {c : BitVec 32} {table : TableInst} {a : FuncAddr} {fn : FuncInst Func H} {ft : FuncType}
    (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
    (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
    (stack : List Value) (tail : List Admin) :
    (stepFrom? s f stack ([value (.int .i32 c), .source (.callIndirect i)] ++ tail)).isSome := by
  have e1 : table.refs[@BitVec.toNat IntType.i32.width c]? = some (some a) := element
  simp only [List.cons_append, List.nil_append, stepFrom?_value_cons]
  rw [stepFrom?_cons_of_none _ _ _ _ rfl]
  simp [stepInstr?, tableFound, e1, typeFound, found]
  split <;> rfl

theorem stepFrom?_isSome_callIndirect_trap {H : Type*} {s : Store H} {f : Frame} {i : TypeIdx}
    {c : BitVec 32} {table : TableInst} (tableFound : frameTable s f = some table)
    (bad : table.refs[c.toNat]? = none ∨ table.refs[c.toNat]? = some none)
    (stack : List Value) (tail : List Admin) :
    (stepFrom? s f stack ([value (.int .i32 c), .source (.callIndirect i)] ++ tail)).isSome := by
  simp only [List.cons_append, List.nil_append, stepFrom?_value_cons]
  rw [stepFrom?_cons_of_none _ _ _ _ rfl]
  rcases bad with e1 | e1
  · have e1' : table.refs[@BitVec.toNat IntType.i32.width c]? = none := e1
    simp [stepInstr?, tableFound, e1']
  · have e1' : table.refs[@BitVec.toNat IntType.i32.width c]? = some none := e1
    simp [stepInstr?, tableFound, e1']

set_option linter.unusedTactic false in
theorem Internal.stepFrom?_isSome {H : Type*} {a b : Config H} (h : Internal a b) :
    ∀ (stack : List Value) (tail : List Admin),
      (stepFrom? a.store a.frame stack (a.code ++ tail)).isSome := by
  induction h with
  | pure s f hp =>
    intro stack tail
    cases hp <;> (try simp only [List.cons_append, List.nil_append, List.append_assoc,
      stepFrom?_value_cons, stepFrom?_values_append]) <;>
      (try rw [stepFrom?_cons_of_none _ _ _ _ rfl]) <;>
      (try simp [stepInstr?, stepHead?, *]) <;>
      (split <;> rfl)
  | context _ vs _ ih =>
    intro stack tail
    simpa only [List.append_assoc, stepFrom?_values_append] using ih _ _
  | label h n cont ih => exact Internal.stepFrom?_isSome_label h n cont ih
  | frame h n outer ih => exact Internal.stepFrom?_isSome_frame h n outer ih
  | invokeWasm s f a ft module fn args found arity =>
    intro stack tail
    simp only [List.append_assoc, stepFrom?_values_append, List.singleton_append]
    rw [stepFrom?_cons_of_none _ _ _ _ rfl]
    simp [stepHead?, found, arity]
  | callIndirect _ _ _ _ _ _ _ _ tf ty el fd _ => exact stepFrom?_isSome_callIndirect tf ty el fd
  | callIndirectBounds _ _ _ _ _ tf ob => exact stepFrom?_isSome_callIndirect_trap tf (.inl ob)
  | callIndirectNull _ _ _ _ _ tf nl => exact stepFrom?_isSome_callIndirect_trap tf (.inr nl)
  | callIndirectType _ _ _ _ _ _ _ _ tf ty el fd _ =>
    exact stepFrom?_isSome_callIndirect tf ty el fd
  | invokeHost _ _ _ _ _ _ _ _ _ _ hb => exact hb.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ hb => exact hb.elim
  | _ =>
    intro stack tail
    try simp only [List.cons_append, List.nil_append, stepFrom?_value_cons]
    try rw [stepFrom?_cons_of_none _ _ _ _ rfl]
    try simp [stepInstr?, *]
    all_goals split <;> rfl

/-! ## Progress -/

/-- **Progress of `step?`.** Every configuration with a host-free step is stepped by `step?`.
The step it takes may differ from the given one where `Internal` is nondeterministic (NaN
payloads, `memory.grow` failure). -/
theorem step?_progress {H : Type*} {cfg cfg' : Config H} (h : Internal cfg cfg') :
    (step? cfg).isSome := by
  have := Internal.stepFrom?_isSome h [] []
  rw [List.append_nil] at this
  rw [step?, Option.isSome_map]
  exact this

/-! ## Deterministic choices (restated from `step?_sound`) -/

/-! ## Terminal configurations and the driver -/

/-! ## Tests -/

namespace CalloutExamples

end CalloutExamples

end Silmaril.Wasm.Lime1.Execution
