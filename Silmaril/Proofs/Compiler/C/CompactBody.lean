module

public import Silmaril.Compiler.C.Compact.Defs
import Silmaril.Proofs.Compiler.C.Compact
import Std.Data.HashMap.Lemmas

public section
namespace Silmaril.Proofs.Compiler.C.Compact

open Silmaril.Compiler.C.Compact Silmaril.Compile.C Silmaril.Compile.C.Sem
open Silmaril.Cerberus Silmaril.Cerberus.Ail

private theorem wrap_range (value : Int) : C0.inRange 4 true (C0.wrap 4 true value) = true := by
  change decide (-2147483648 ≤ C0.wrap 4 true value ∧ C0.wrap 4 true value < 2147483648) = true
  apply decide_eq_true
  unfold C0.wrap
  change -2147483648 ≤ (if (true && decide (2147483648 ≤ value % 4294967296)) = true then
      value % 4294967296 - 4294967296 else value % 4294967296) ∧ _
  simp only [Bool.true_and, decide_eq_true_eq]
  split <;> omega

private theorem wrap_id {value : Int} (valid : C0.inRange 4 true value = true) :
    C0.wrap 4 true value = value := by
  change decide (-2147483648 ≤ value ∧ value < 2147483648) = true at valid
  have bounds := of_decide_eq_true valid
  change (if (true && decide (2147483648 ≤ value % 4294967296)) = true then
      value % 4294967296 - 4294967296 else value % 4294967296) = value
  simp only [Bool.true_and, decide_eq_true_eq]
  split <;> omega

private theorem slot_read {scope : List Sym} {slots : Array Int} {env : C0.Env}
    (state : SlotState scope slots env) (fd : C0.FunDef) (index : Nat) (symbol : Sym)
    (lookup : scope[index]? = some symbol) :
    readSlot slots index = C0.readVar fd env symbol := by
  obtain ⟨value, slot, localValue, _⟩ := state.initialized index symbol lookup
  simp [readSlot, C0.readVar, slot, localValue]

private theorem slot_init {scope : List Sym} {slots : Array Int} {env : C0.Env}
    (state : SlotState scope slots env) (symbol : Sym) (value : Int)
    (fresh : ∀ previous ∈ scope, previous.number ≠ symbol.number)
    (valid : C0.inRange 4 true value = true) :
    SlotState (scope ++ [symbol]) (slots.push value) { env with locals := env.locals.insert symbol.number value } := by
  refine ⟨by simp [state.size], ?_⟩
  intro index object lookup
  by_cases within : index < scope.length
  · rw [List.getElem?_append_left within] at lookup
    obtain ⟨old, slot, localValue, range⟩ := state.initialized index object lookup
    have different := fresh object (List.mem_of_getElem? lookup)
    refine ⟨old, ?_, ?_, range⟩
    · rw [Array.getElem?_push, ite_eq_right (by rw [state.size]; omega)]
      exact slot
    · simp [Std.HashMap.getElem?_insert, Ne.symm different, localValue]
  · have indexEq : index = scope.length := by
      have bound := (List.getElem?_eq_some_iff.mp lookup).1
      simp at bound
      omega
    subst index
    rw [List.getElem?_append_right (Nat.le_refl _)] at lookup
    have same : object = symbol := by simpa using lookup.symm
    subst object
    refine ⟨value, ?_, ?_, valid⟩
    · rw [← state.size, Array.getElem?_push_size]
    · simp

private theorem slot_range {scope : List Sym} {slots : Array Int} {env : C0.Env}
    (state : SlotState scope slots env) (index : Nat) (within : index < slots.size) :
    IntOutcome (readSlot slots index) := by
  rw [state.size] at within
  obtain ⟨value, loaded, _, valid⟩ := state.initialized index scope[index] (List.getElem?_eq_getElem within)
  simpa [IntOutcome, readSlot, loaded] using valid

private theorem op_outcome (op : Op) (left right : Int) : IntOutcome (op.eval left right) := by
  cases op
  · simp only [Op.eval]
    split
    · assumption
    · rfl
  · simp only [Op.eval, IntOutcome]
    split <;> decide

private theorem expr_outcome {scope : List Sym} {slots : Array Int} {env : C0.Env}
    (state : SlotState scope slots env) (expr : Expr) (valid : expr.scoped slots.size = true) :
    IntOutcome (expr.eval (readSlot slots)) := by
  induction expr with
  | literal value => exact wrap_range value
  | slot index => exact slot_range state index (by simpa [Expr.scoped] using valid)
  | bin op left right ihLeft ihRight =>
    have bounds : left.scoped slots.size = true ∧ right.scoped slots.size = true := by
      simpa only [Expr.scoped, Bool.and_eq_true] using valid
    have leftOutcome := ihLeft bounds.1
    have rightOutcome := ihRight bounds.2
    simp only [Expr.eval, bind, Except.bind]
    cases evaluation : left.eval (readSlot slots) with
    | error stop => simpa [evaluation] using leftOutcome
    | ok lhs =>
      cases evaluationRight : right.eval (readSlot slots) with
      | error stop => simpa [evaluationRight] using rightOutcome
      | ok rhs => exact op_outcome op lhs rhs

private theorem terminal_run {scope : List Sym} {body : Body} {ail : TypedStatement}
    (matched : TerminalProjects scope body ail) (program : C0.Prog) (fd : C0.FunDef)
    (returnType : fd.ret = .int 4 true) (caller : C0.Env) (kont : C0.Kont)
    (slots : Array Int) (env : C0.Env) (state : SlotState scope slots env)
    (valid : body.scoped slots.size = true) (fuel : Nat) (enough : body.fuel ≤ fuel) :
    IntOutcome (body.run slots) ∧
      observeActivation caller (C0.loop program fuel fd (some ail) kont env) =
        (body.run slots).map (fun value => (some value, { env with locals := caller.locals })) := by
  induction matched generalizing fuel with
  | @ret value ail loc desug attrs matched =>
    change value.depth + 2 ≤ fuel at enough
    obtain ⟨steps, rfl⟩ : ∃ steps, fuel = steps + 2 := ⟨fuel - 2, by omega⟩
    have evaluate := eval_eq matched program fd env (readSlot slots) (slot_read state fd) steps (by omega)
    have outcome := expr_outcome state value valid
    refine ⟨outcome, ?_⟩
    rw [C0.loop.eq_2, C0.step]
    simp only [Statement.node, evaluate]
    cases evaluation : value.eval (readSlot slots) with
    | error stop => simp [observeActivation, Body.run, evaluation, Except.map, bind, Except.bind]
    | ok returned =>
      have inRange : C0.inRange 4 true returned = true := by simpa [evaluation, IntOutcome] using outcome
      simp [observeActivation, Body.run, evaluation, Except.map, bind, Except.bind, pure, Except.pure, C0.convTo,
        returnType, wrap_id inRange]
  | @branch test yes no ailTest ailYes ailNo loc desug attrs testMatch yesMatch noMatch ihYes ihNo =>
    simp only [Body.fuel, max_le_iff] at enough
    obtain ⟨steps, rfl⟩ : ∃ steps, fuel = steps + 2 := ⟨fuel - 2, by omega⟩
    simp only [Body.scoped, Bool.and_eq_true] at valid
    have evaluate := eval_eq testMatch program fd env (readSlot slots) (slot_read state fd) steps (by omega)
    have outcome := expr_outcome state test valid.1.1
    have yesResult := ihYes valid.1.2 (steps + 1) (by omega)
    have noResult := ihNo valid.2 (steps + 1) (by omega)
    rw [C0.loop.eq_2, C0.step]
    simp only [Statement.node, evaluate, Body.run, bind, Except.bind]
    cases evaluation : test.eval (readSlot slots) with
    | error stop => exact ⟨by simpa [evaluation, IntOutcome] using outcome, rfl⟩
    | ok condition =>
      simp only [Except.map]
      split <;> assumption

private theorem block_run {scope bindings : List Sym} {body : Body} {ail : List TypedStatement}
    (matched : BlockProjects scope bindings body ail) (program : C0.Prog) (fd : C0.FunDef)
    (returnType : fd.ret = .int 4 true) (caller : C0.Env) (kont : C0.Kont)
    (localTypes : ∀ symbol ∈ bindings, fd.locals[symbol.number]? = some (.int 4 true))
    (slots : Array Int) (env : C0.Env) (state : SlotState scope slots env)
    (valid : body.scoped slots.size = true) (fuel : Nat) (enough : body.fuel + 1 ≤ fuel) :
    IntOutcome (body.run slots) ∧
      observeActivation caller (C0.loop program fuel fd none (.seq ail kont) env) =
        (body.run slots).map (fun value => (some value, { env with locals := caller.locals })) := by
  induction matched generalizing slots env fuel with
  | terminal matched =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel with
      | zero => cases matched <;> simp [Body.fuel] at enough
      | succ steps =>
        rw [C0.loop.eq_2, C0.step.eq_4]
        exact terminal_run matched program fd returnType caller (.seq [] kont) slots env state valid
          (steps + 1) (by omega)
  | @bind scope symbol rest init next ailInit ailNext loc desug attrs fresh valueMatch nextMatch ih =>
    simp only [Body.fuel] at enough
    have initFuel : init.depth + 3 ≤ fuel := by omega
    have nextFuel : next.fuel + 3 ≤ fuel := by omega
    obtain ⟨steps, rfl⟩ : ∃ steps, fuel = steps + 3 := ⟨fuel - 3, by omega⟩
    simp only [Body.scoped, Bool.and_eq_true] at valid
    have evaluate := eval_eq valueMatch program fd env (readSlot slots) (slot_read state fd) steps (by omega)
    have outcome := expr_outcome state init valid.1
    have localType := localTypes symbol (by simp)
    rw [C0.loop.eq_2, C0.step.eq_4]
    change _ ∧ observeActivation caller (C0.loop program (steps + 2) fd (some _) _ env) = _
    rw [C0.loop.eq_2, C0.step, Statement.node]
    simp only [List.forIn_cons, List.forIn_nil, evaluate, Except.map, Body.run, bind, Except.bind]
    cases evaluation : init.eval (readSlot slots) with
    | error stop => exact ⟨by simpa [evaluation, IntOutcome] using outcome, rfl⟩
    | ok value =>
      have inRange : C0.inRange 4 true value = true := by simpa [evaluation, IntOutcome] using outcome
      have nextState := slot_init state symbol value fresh inRange
      have nextScoped : next.scoped (slots.push value).size = true := by simpa using valid.2
      have result := ih (fun other mem => localTypes other (by simp [mem])) _ _ nextState nextScoped
        (steps + 1) (by omega)
      simpa [localType, C0.convTo, wrap_id inRange, Except.map, pure, Except.pure] using result

theorem extraction {ail : TypedProgram} {result : Projection} (success : project ail = .ok result) :
    FunctionProjects ail result.fn := by
  cases checked : projectChecked ail with
  | error reason => simp [project, checked, Except.map] at success
  | ok witness =>
    have equal : witness.value = result := by simpa [project, checked, Except.map] using success
    exact equal ▸ witness.projects

theorem activation {scope bindings : List Sym} {fn : Function} {loc : Loc}
    {ailBindings : Bindings} {ail : List TypedStatement}
    (matched : BlockProjects scope bindings fn.body ail)
    (arity : fn.arity = scope.length) (valid : fn.body.scoped fn.arity = true)
    (program : C0.Prog) (fd : C0.FunDef) (caller env : C0.Env) (slots : Array Int)
    (entry : SlotState scope slots env) (returnType : fd.ret = .int 4 true)
    (localTypes : ∀ symbol ∈ bindings, fd.locals[symbol.number]? = some (.int 4 true))
    (fuel : Nat) (enough : fn.body.fuel + 2 ≤ fuel) :
    IntOutcome (fn.run slots) ∧
      observeActivation caller (C0.loop program fuel fd
        (some (.mk loc ⟨false, none⟩ (.mk []) (.block ailBindings ail))) .stop env) =
      (fn.run slots).map (fun value => (some value, { env with locals := caller.locals })) := by
  have size : slots.size = fn.arity := entry.size.trans arity.symm
  have ranges : slots.toList.all (C0.inRange 4 true) = true := by
    rw [List.all_eq_true]
    intro value mem
    obtain ⟨index, atSlot⟩ := List.mem_iff_getElem?.mp mem
    have within := (List.getElem?_eq_some_iff.mp atSlot).1
    simp only [Array.length_toList] at within
    rw [Array.getElem?_toList] at atSlot
    simpa [readSlot, IntOutcome, atSlot] using slot_range entry index within
  have runEq : fn.run slots = fn.body.run slots := by simp [Function.run, size, ranges, valid]
  obtain ⟨steps, rfl⟩ : ∃ steps, fuel = steps + 2 := ⟨fuel - 2, by omega⟩
  rw [runEq, C0.loop.eq_2, C0.step, Statement.node]
  exact block_run matched program fd returnType caller .stop localTypes slots env entry
    (by simpa [size] using valid) (steps + 1) (by omega)

theorem accepted_activation {ail : TypedProgram} {fn : Function} (projection : FunctionProjects ail fn)
    {symbol : Sym} {source : FunctionDefinition GenTypeCategory}
    (sole : ail.2.functionDefinitions = [(symbol, source)])
    (program : C0.Prog) (fd : C0.FunDef) (caller env : C0.Env) (slots : Array Int)
    (entry : SlotState source.params slots env) (bodyEq : fd.body = source.body)
    (returnType : fd.ret = .int 4 true)
    (localTypes : ∀ bindings statements, source.body.node = .block bindings statements →
      ∀ binding ∈ bindings, fd.locals[binding.1.number]? = some (.int 4 true))
    (fuel : Nat) (enough : fn.body.fuel + 2 ≤ fuel) :
    IntOutcome (fn.run slots) ∧
      observeActivation caller (C0.loop program fuel fd (some fd.body) .stop env) =
        (fn.run slots).map (fun value => (some value, { env with locals := caller.locals })) := by
  obtain ⟨original, definition, loc, bindings, statements, locals, unique, outer, arity, names, matched⟩ :=
    projection.shape
  rw [unique] at sole
  simp only [List.cons.injEq, and_true, Prod.mk.injEq] at sole
  obtain ⟨rfl, rfl⟩ := sole
  subst locals
  rw [bodyEq, outer]
  exact activation matched arity projection.wellScoped program fd caller env slots entry returnType
    (fun localSymbol mem => by
      obtain ⟨binding, inBlock, rfl⟩ := List.mem_map.mp mem
      exact localTypes _ _ (congrArg Statement.node outer) binding inBlock) fuel enough

end Silmaril.Proofs.Compiler.C.Compact
