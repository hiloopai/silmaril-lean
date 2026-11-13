module

public import Silmaril.Compiler.Native.Optimize.Validation.Intern.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Intern
open Silmaril.Machine
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem expr_beq (a b : Expr) : (a == b) = true ↔ a = b := by
  change instBEqExpr.beq a b = true ↔ a = b
  cases a <;> cases b <;> simp [instBEqExpr.beq]

private theorem run_eq (state : State) (raw : Expr) :
    (intern raw).run state =
      match state.nodes.findIdx? (· == normalize state.nodes raw) with
      | some index => (index, state)
      | none => (state.nodes.size, { state with nodes := state.nodes.push (normalize state.nodes raw) }) := by
  cases found : state.nodes.findIdx? (· == normalize state.nodes raw) <;>
    simp [intern, StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
      MonadState.get, getThe, MonadStateOf.get, MonadStateOf.set, Bind.bind, Pure.pure, found]

/-- The actual state monad either reuses an existing normalized node or appends
exactly that node. No state component other than nodes can change. -/
theorem cases_actual (state : State) (raw : Expr) :
    (∃ index, state.nodes.findIdx? (· == normalize state.nodes raw) = some index ∧
      (intern raw).run state = (index, state)) ∨
    (state.nodes.findIdx? (· == normalize state.nodes raw) = none ∧
      (intern raw).run state =
        (state.nodes.size, { state with nodes := state.nodes.push (normalize state.nodes raw) })) := by
  cases found : state.nodes.findIdx? (· == normalize state.nodes raw) with
  | none => exact .inr ⟨rfl, by rw [run_eq, found]⟩
  | some index => exact .inl ⟨index, rfl, by rw [run_eq, found]⟩

theorem nodes_prefix (state : State) (raw : Expr) :
    ∃ suffix : Array Expr, (intern raw).run state |>.2.nodes = state.nodes ++ suffix ∧ suffix.size ≤ 1 := by
  rcases cases_actual state raw with ⟨index, found, actual⟩ | ⟨missing, actual⟩
  · rw [actual]
    exact ⟨#[], by simp⟩
  · rw [actual]
    exact ⟨#[normalize state.nodes raw], by simp⟩

theorem old_node (state : State) (raw : Expr) {index : Nat} (bounded : index < state.nodes.size) :
    ((intern raw).run state).2.nodes[index]? = state.nodes[index]? := by
  obtain ⟨suffix, equal, length⟩ := nodes_prefix state raw
  rw [equal]
  exact Array.getElem?_append_left bounded

theorem returned_bound (state : State) (raw : Expr) :
    ((intern raw).run state).1 ≤ state.nodes.size := by
  rcases cases_actual state raw with ⟨index, found, actual⟩ | ⟨missing, actual⟩
  · have bounded : index < state.nodes.size := (Array.findIdx?_eq_some_iff_getElem.mp found).1
    rw [actual]
    exact Nat.le_of_lt bounded
  · rw [actual]

theorem frame (state : State) (raw : Expr) :
    ((intern raw).run state).2.regs = state.regs ∧
    ((intern raw).run state).2.slots = state.slots ∧
    ((intern raw).run state).2.effects = state.effects := by
  rcases cases_actual state raw with ⟨index, found, actual⟩ | ⟨missing, actual⟩
  · rw [actual]
    exact ⟨rfl, rfl, rfl⟩
  · rw [actual]
    exact ⟨rfl, rfl, rfl⟩

theorem returned_index (state : State) (raw : Expr) :
    ((intern raw).run state).1 < ((intern raw).run state).2.nodes.size ∧
    ((intern raw).run state).2.nodes[((intern raw).run state).1]? =
      some (normalize state.nodes raw) := by
  rcases cases_actual state raw with ⟨index, found, actual⟩ | ⟨missing, actual⟩
  · obtain ⟨bounded, selected, earlier⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have equal : state.nodes[index] = normalize state.nodes raw := (expr_beq _ _).mp selected
    rw [actual]
    exact ⟨bounded, Array.getElem?_eq_some_iff.mpr ⟨bounded, equal⟩⟩
  · rw [actual]
    exact ⟨by simp, by simp⟩

theorem normalize_scoped (nodes : Array Expr) (raw : Expr) (bound : Nat)
    (wellFormed : ReferencesBelow bound raw) : ReferencesBelow bound (normalize nodes raw) := by
  cases raw with
  | unary op source =>
    simp only [normalize]
    split
    · trivial
    · exact wellFormed
  | binary op left right =>
    simp only [normalize]
    split
    · split
      · trivial
      · exact wellFormed
    · exact wellFormed
  | _ => exact wellFormed

theorem constants_agree {nodes : Array Expr} {meaning : Interpretation}
    (coherent : Coherent nodes meaning) : ConstantsAgree nodes meaning := by
  intro index word atIndex
  exact coherent index (.const word) atIndex

/-- Bounded expression references do not inspect the newly assigned index. -/
theorem eval_extend (meaning : Interpretation) (index : Nat) (value : Option Lir.Word)
    (expression : Expr) (wellFormed : ReferencesBelow index expression) :
    expression.eval (extendValue meaning index value) = expression.eval meaning := by
  cases expression with
  | unary op source =>
    have bound : source < index := wellFormed
    simp [Expr.eval, extendValue, ne_of_lt bound]
  | binary op left right =>
    have bounds : left < index ∧ right < index := wellFormed
    simp [Expr.eval, extendValue, ne_of_lt bounds.1, ne_of_lt bounds.2]
  | float op left right =>
    have bounds : left < index ∧ right < index := wellFormed
    simp [Expr.eval, extendValue, ne_of_lt bounds.1, ne_of_lt bounds.2]
  | _ => rfl

theorem references_mono {expression : Expr} {small large : Nat}
    (wellFormed : ReferencesBelow small expression) (bound : small ≤ large) : ReferencesBelow large expression := by
  cases expression <;> simp_all [ReferencesBelow] <;> omega

/-- Appending a wellFormed expression extends a coherent partial DAG constructively;
the new value may be none and every old value/meaning remains unchanged. -/
theorem append_denotes (nodes : Array Expr) (meaning : Interpretation) (expression : Expr)
    (wellFormed : WellScoped nodes) (coherent : Coherent nodes meaning)
    (newScoped : ReferencesBelow nodes.size expression) :
    WellScoped (nodes.push expression) ∧
      Coherent (nodes.push expression) (extendValue meaning nodes.size (expression.eval meaning)) := by
  constructor
  · show WellScoped (nodes.push expression)
    intro index selected atIndex
    by_cases appended : index = nodes.size
    · subst index
      have selectedEqual : expression = selected := by simpa using atIndex
      rw [← selectedEqual]
      exact newScoped
    · have old : nodes[index]? = some selected := by simpa [Array.getElem?_push, appended] using atIndex
      exact wellFormed index selected old
  · show Coherent (nodes.push expression) (extendValue meaning nodes.size (expression.eval meaning))
    intro index selected atIndex
    by_cases appended : index = nodes.size
    · subst index
      have selectedEqual : expression = selected := by simpa using atIndex
      subst selected
      simp only [extendValue, ↓reduceIte]
      exact (eval_extend meaning nodes.size (expression.eval meaning) expression newScoped).symm
    · show (extendValue meaning nodes.size (expression.eval meaning)).value index =
        selected.eval (extendValue meaning nodes.size (expression.eval meaning))
      have old : nodes[index]? = some selected := by simpa [Array.getElem?_push, appended] using atIndex
      have bounded : index < nodes.size := (Array.getElem?_eq_some_iff.mp old).1
      have refs : ReferencesBelow nodes.size selected :=
        references_mono (wellFormed index selected old) (Nat.le_of_lt bounded)
      calc
        (extendValue meaning nodes.size (expression.eval meaning)).value index = meaning.value index := by
          simp [extendValue, appended]
        _ = selected.eval meaning := coherent index selected old
        _ = selected.eval (extendValue meaning nodes.size (expression.eval meaning)) :=
          (eval_extend meaning nodes.size (expression.eval meaning) selected refs).symm

/-- Actual interning denotes its raw proposal in a coherent partial DAG, with
both normalized reuse and normalized append handled by actual intern cases. -/
theorem sound (state : State) (raw : Expr) (meaning : Interpretation)
    (wellFormed : WellScoped state.nodes) (coherent : Coherent state.nodes meaning)
    (rawScoped : ReferencesBelow state.nodes.size raw) :
    ∃ nextMeaning, Denotes state.nodes ((intern raw).run state).2.nodes
      ((intern raw).run state).1 raw meaning nextMeaning := by
  have normalizedMeaning : (normalize state.nodes raw).eval meaning = raw.eval meaning :=
    normalize_eval state.nodes meaning (constants_agree coherent) raw
  have normalizedScoped : ReferencesBelow state.nodes.size (normalize state.nodes raw) :=
    normalize_scoped state.nodes raw state.nodes.size rawScoped
  rcases cases_actual state raw with ⟨index, found, actual⟩ | ⟨missing, actual⟩
  · obtain ⟨bounded, selected, earlier⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have equal : state.nodes[index] = normalize state.nodes raw := (expr_beq _ _).mp selected
    have selectedAt : state.nodes[index]? = some (normalize state.nodes raw) := Array.getElem?_eq_some_iff.mpr ⟨bounded, equal⟩
    rw [actual]
    exact ⟨meaning, wellFormed, coherent, bounded,
      (coherent index _ selectedAt).trans normalizedMeaning,
      fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show ∃ nextMeaning, Denotes state.nodes ((intern raw).run state).2.nodes
      ((intern raw).run state).1 raw meaning nextMeaning
    have appended : WellScoped (state.nodes.push (normalize state.nodes raw)) ∧
        Coherent (state.nodes.push (normalize state.nodes raw))
          (extendValue meaning state.nodes.size ((normalize state.nodes raw).eval meaning)) :=
      append_denotes state.nodes meaning (normalize state.nodes raw) wellFormed coherent normalizedScoped
    rw [actual]
    refine ⟨extendValue meaning state.nodes.size ((normalize state.nodes raw).eval meaning),
      appended.1, appended.2, by simp, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simpa [extendValue] using normalizedMeaning
    · intro other bounded
      simp [extendValue, ne_of_lt bounded]
    · intro other expression atIndex
      have bounded : other < state.nodes.size := (Array.getElem?_eq_some_iff.mp atIndex).1
      exact eval_extend meaning state.nodes.size _ expression
        (references_mono (wellFormed other expression atIndex) (Nat.le_of_lt bounded))

end Silmaril.Compiler.Native.Optimize.Validation.Intern
