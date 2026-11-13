module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Meaning.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects
open Silmaril.Machine
open Roots

set_option maxRecDepth 8192

theorem PrefixExtends.refl (meaning : Interpretation) (nodes events : Nat) :
    PrefixExtends nodes events meaning meaning :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩

theorem PrefixExtends.trans {smallNodes largeNodes smallEvents largeEvents : Nat}
    {first middle last : Interpretation}
    (earlier : PrefixExtends smallNodes smallEvents first middle)
    (later : PrefixExtends largeNodes largeEvents middle last)
    (nodes : smallNodes ≤ largeNodes) (events : smallEvents ≤ largeEvents) :
    PrefixExtends smallNodes smallEvents first last :=
  ⟨fun index bounded => (later.values index (by omega)).trans (earlier.values index bounded),
    later.input.trans earlier.input, later.slot.trans earlier.slot, later.address.trans earlier.address,
    fun event bounded => (later.load event (by omega)).trans (earlier.load event bounded),
    later.result.trans earlier.result⟩

/-- Existing frozen pure/slot extension proofs embed without changing them. -/
theorem prefix_of_extends {nodes : Nat} {oldMeaning newMeaning : Interpretation}
    (extension : Extends nodes oldMeaning newMeaning) (events : Nat) :
    PrefixExtends nodes events oldMeaning newMeaning :=
  ⟨extension.values, extension.input, extension.slot, extension.address,
    fun event _ => congrFun extension.load event, extension.result⟩

theorem expression_preserved {nodes events : Nat} {oldMeaning newMeaning : Interpretation}
    (extension : PrefixExtends nodes events oldMeaning newMeaning) (expression : Expr)
    (references : Intern.ReferencesBelow nodes expression)
    (loads : EventReferencesBelow events expression) :
    expression.eval newMeaning = expression.eval oldMeaning := by
  cases expression with
  | input reg => exact congrFun extension.input reg
  | slot index => exact congrFun extension.slot index
  | const word => rfl
  | unary op source => simp only [Expr.eval, extension.values source references]
  | binary op left right => simp only [Expr.eval, extension.values left references.1, extension.values right references.2]
  | float op left right => simp only [Expr.eval, extension.values left references.1, extension.values right references.2]
  | addr symbol offset => exact congrFun (congrFun extension.address symbol) offset
  | load event => exact extension.load event loads
  | result event index => exact congrFun (congrFun extension.result event) index

/-- The rooted partial frame/DAG survives a genuine extension of load results
because existing load nodes reference strictly earlier events. -/
theorem prefix_rooted (state : State) (frame : Lir.Frame Nat) (oldMeaning newMeaning : Interpretation)
    (rooted : Rooted state frame oldMeaning) (events : Nat) (loads : LoadsScoped state.nodes events)
    (extension : PrefixExtends state.nodes.size events oldMeaning newMeaning) :
    Rooted state frame newMeaning := by
  refine ⟨rooted.wellScoped, ?_, rooted.regsBounded, rooted.slotsBounded, ?_, ?_⟩
  · intro index expression found
    have bounded : index < state.nodes.size := (Array.getElem?_eq_some_iff.mp found).1
    have references : Intern.ReferencesBelow state.nodes.size expression := Intern.references_mono (rooted.wellScoped index expression found) (Nat.le_of_lt bounded)
    exact (extension.values index bounded).trans ((rooted.coherent index expression found).trans
      (expression_preserved extension expression references (loads index expression found)).symm)
  · intro reg
    simp only [regValue]
    cases found : state.regs.find? (·.1 == reg) with
    | none => simpa only [regValue, found, extension.input] using rooted.regs reg
    | some root =>
      have bounded : root.2 < state.nodes.size := rooted.regsBounded root (List.mem_of_find?_eq_some found)
      simpa only [regValue, found, extension.values root.2 bounded] using rooted.regs reg
  · intro slot
    simp only [slotValue]
    cases found : state.slots.find? (·.1 == slot) with
    | none => simpa only [slotValue, found, extension.slot] using rooted.slots slot
    | some root =>
      have bounded : root.2 < state.nodes.size := rooted.slotsBounded root (List.mem_of_find?_eq_some found)
      simpa only [slotValue, found, extension.values root.2 bounded] using rooted.slots slot

theorem prefix_total (nodes : Array Expr) (oldMeaning newMeaning : Interpretation) (events : Nat)
    (total : Total.TotalNodes nodes oldMeaning) (extension : PrefixExtends nodes.size events oldMeaning newMeaning) :
    Total.TotalNodes nodes newMeaning := by
  intro index bounded
  obtain ⟨word, value⟩ := total index bounded
  exact ⟨word, (extension.values index bounded).trans value⟩

theorem setLoad_prefix (meaning : Interpretation) (nodes event : Nat) (word : Lir.Word) :
    PrefixExtends nodes event meaning (setLoad meaning event word) := by
  refine ⟨fun _ _ => rfl, rfl, rfl, rfl, ?_, rfl⟩
  intro other bounded
  have different : other ≠ event := by omega
  simp only [setLoad, different, ↓reduceIte]

/-- A fresh actual load result does not retroactively change an earlier load
node, including its absence, or a prior partial register/slot observation. -/
theorem setLoad_rooted (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Rooted state frame meaning) (loads : LoadsScoped state.nodes state.effects.size)
    (word : Lir.Word) : Rooted state frame (setLoad meaning state.effects.size word) :=
  prefix_rooted state frame meaning _ rooted state.effects.size loads (setLoad_prefix meaning _ _ word)

theorem setLoad_current (meaning : Interpretation) (event : Nat) (word : Lir.Word) :
    (setLoad meaning event word).load event = some word := by simp [setLoad]

theorem loadsScoped_mono {nodes : Array Expr} {small large : Nat}
    (loads : LoadsScoped nodes small) (bound : small ≤ large) : LoadsScoped nodes large := by
  intro index expression found
  have boundedRefs := loads index expression found
  cases expression <;> simp_all [EventReferencesBelow]
  omega

private theorem normalized_loads (nodes : Array Expr) (raw : Expr) (events : Nat)
    (loads : EventReferencesBelow events raw) : EventReferencesBelow events (normalize nodes raw) := by
  cases raw with
  | unary op source =>
    simp only [normalize]
    split <;> trivial
  | binary op left right =>
    simp only [normalize]
    split
    · split <;> trivial
    · trivial
  | _ => exact loads

/-- Real intern reuse/append retains load-event scoping. -/
theorem intern_loadsScoped (state : State) (raw : Expr) (events : Nat)
    (loads : LoadsScoped state.nodes events) (rawLoads : EventReferencesBelow events raw) :
    LoadsScoped ((intern raw).run state).2.nodes events := by
  rcases Intern.cases_actual state raw with ⟨index, found, actual⟩ | ⟨missing, actual⟩
  · rw [actual]
    exact loads
  · rw [actual]
    intro index expression found
    by_cases appended : index = state.nodes.size
    · subst index
      have same : normalize state.nodes raw = expression := by simpa using found
      rw [← same]
      exact normalized_loads state.nodes raw events rawLoads
    · have old : state.nodes[index]? = some expression := by
        simpa [Array.getElem?_push, appended] using found
      exact loads index expression old

/-- Source partial reads append only input leaves, never future load nodes. -/
theorem readReg_loadsScoped (state : State) (reg events : Nat) (loads : LoadsScoped state.nodes events) :
    LoadsScoped ((readReg reg).run state).2.nodes events := by
  cases found : state.regs.find? (·.1 == reg) with
  | none =>
    have actual : (readReg reg).run state = (intern (.input reg)).run state := by
      simp [readReg, StateT.run, StateT.bind, StateT.get,
        MonadState.get, getThe, MonadStateOf.get, Bind.bind, Pure.pure, found]
    rw [actual]
    exact intern_loadsScoped state (.input reg) events loads trivial
  | some root =>
    have actual : (readReg reg).run state = (root.2, state) := by
      cases root
      simp [readReg, StateT.run, StateT.bind, StateT.get, StateT.pure,
        MonadState.get, getThe, MonadStateOf.get, Bind.bind, Pure.pure, found]
    rw [actual]
    exact loads

/-- Ordered symbolic effects inspect only their DAG operand roots; preserved
root values therefore preserve concrete events even when new loads are added. -/
theorem concreteEffect_preserved {nodes events : Nat} {oldMeaning newMeaning : Interpretation}
    (extension : PrefixExtends nodes events oldMeaning newMeaning) (effect : Effect)
    (boundedRefs : EffectReferencesBelow nodes effect) :
    concreteEffect newMeaning effect = concreteEffect oldMeaning effect := by
  cases effect with
  | load width ext base offset => simp only [concreteEffect, extension.values base boundedRefs]
  | store width base offset source =>
    simp only [concreteEffect, extension.values base boundedRefs.1, extension.values source boundedRefs.2]
  | faulting op left right =>
    simp only [concreteEffect, extension.values left boundedRefs.1, extension.values right boundedRefs.2]
  | call symbol args results => rfl
  | indirect target args results => rfl

theorem runEffects_preserved {nodes events : Nat} {oldMeaning newMeaning : Interpretation}
    (extension : PrefixExtends nodes events oldMeaning newMeaning) (effects : List Effect)
    (boundedRefs : ∀ effect ∈ effects, EffectReferencesBelow nodes effect) (memory : Lir.Memory) :
    runEffects newMeaning effects memory = runEffects oldMeaning effects memory := by
  have same : effects.mapM (concreteEffect newMeaning) = effects.mapM (concreteEffect oldMeaning) := by
    induction effects with
    | nil => rfl
    | cons effect rest ih =>
      simp only [List.mapM_cons, concreteEffect_preserved extension effect (boundedRefs effect (by simp)),
        ih (fun e member => boundedRefs e (by simp [member]))]
  simp only [runEffects, same]

end Silmaril.Compiler.Native.Optimize.Validation.Effects
