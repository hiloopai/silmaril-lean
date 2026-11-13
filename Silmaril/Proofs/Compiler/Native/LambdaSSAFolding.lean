module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Thms
/-! Actual source and folded evaluations for the existing typed arithmetic
fragment, sound lexical abstract information, and both-direction preservation
of every finite observation. The unchanged-memory total executions are derived
from the syntax independently of a successful-evaluation premise. -/
@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Machine.RTL (Opcode CallOracle packValues)
open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.Lir (Word)

theorem models_unknown (value : Value Word) : Models .unknown value := trivial

theorem models_packed (word : Word) : Models (packed word) (packValues [word]) :=
  ⟨.atom word, .unit, rfl, rfl, rfl⟩

theorem environment_cons {known : List Abstract} {env : Semantics.Env Word}
    (models : EnvironmentModels known env) {abstract : Abstract} {value : Value Word}
    (head : Models abstract value) : EnvironmentModels (abstract :: known) (Semantics.extend env value) := by
  intro index
  cases index with
  | zero => exact head
  | succ index => exact models index

theorem shape_environment_cons {context : List Shape} {env : Semantics.Env Word}
    (shapes : ShapeEnvironment context env) {shape : Shape} {value : Value Word}
    {words : List Word} (head : shape.Holds value words) :
    ShapeEnvironment (shape :: context) (Semantics.extend env value) := by
  intro index expected lookup
  cases index with
  | zero =>
    have same : shape = expected := Option.some.inj lookup
    exact ⟨words, same ▸ head⟩
  | succ index => exact shapes index expected lookup

theorem models_components {known : Abstract} {left right : Value Word}
    (models : Models known (.pair left right)) :
    let components := match known with
      | .pair a b => (a, b)
      | _ => (.unknown, .unknown)
    Models components.1 left ∧ Models components.2 right := by
  cases known with
  | unknown => exact ⟨trivial, trivial⟩
  | word word => cases models
  | unit => cases models
  | pair a b =>
    obtain ⟨x, y, same, hx, hy⟩ := models
    obtain ⟨rfl, rfl⟩ := Value.pair.inj same
    exact ⟨hx, hy⟩

theorem models_words {known : Abstract} {value : Value Word} {words : List Word}
    (models : Models known value) (packed : abstractWords known = some words) :
    value = packValues words := by
  induction known generalizing words value with
  | unknown => cases packed
  | word word => cases packed
  | unit =>
    simp only [abstractWords, Option.some.injEq] at packed
    cases packed
    exact models
  | pair a b ihA ihB =>
    cases a with
    | unknown | unit | pair => cases packed
    | word word =>
      obtain ⟨x, y, same, hx, hy⟩ := models
      simp only [Models] at hx
      subst x
      simp only [abstractWords, Option.map_eq_some_iff] at packed
      obtain ⟨rest, hrest, rfl⟩ := packed
      rw [same, ihB hy hrest]
      rfl

theorem constantOp_models (oracle : CallOracle) (memory : Memory)
    {opcode : Old.Opcode} {known : Abstract} {value : Value Word} {word : Word}
    (models : Models known value) (folded : constantOp opcode known = some word) :
    Opcode.step oracle opcode value memory (packValues [word]) memory := by
  have words : ∃ words, abstractWords known = some words := by
    unfold constantOp at folded
    split at folded
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · cases folded
  obtain ⟨words, packed⟩ := words
  rw [models_words models packed]
  exact constantOp_sound oracle memory folded words packed

theorem arithmetic_binary_total (op : Silmaril.Machine.Lir.Binop)
    (admitted : (newBinary op).isSome = true) (left right : Word) :
    ∃ result, op.eval left right = some result := by
  cases op <;> simp only [newBinary, Option.isSome_none, Bool.false_eq_true] at admitted
  all_goals exact ⟨_, rfl⟩

theorem shape_tuple_zero {value : Value Word} {words : List Word}
    (shape : (Shape.tuple 0).Holds value words) : value = .unit := by
  obtain ⟨rfl, length⟩ := shape
  have empty : words = [] := by simpa only [List.length_eq_zero_iff] using length
  subst words
  rfl

theorem shape_tuple_one {value : Value Word} {words : List Word}
    (shape : (Shape.tuple 1).Holds value words) :
    ∃ word, value = packValues [word] := by
  obtain ⟨rfl, length⟩ := shape
  cases words with
  | nil => cases length
  | cons word rest =>
    have empty : rest = [] := by simpa only [List.length_eq_zero_iff] using (Nat.succ.inj length)
    subst rest
    exact ⟨word, rfl⟩

theorem shape_tuple_two {value : Value Word} {words : List Word}
    (shape : (Shape.tuple 2).Holds value words) :
    ∃ left right, value = packValues [left, right] := by
  obtain ⟨rfl, length⟩ := shape
  cases words with
  | nil => cases length
  | cons left rest =>
    cases rest with
    | nil => cases length
    | cons right tail =>
      have empty : tail = [] := by simpa only [List.length_eq_zero_iff] using (Nat.succ.inj (Nat.succ.inj length))
      subst tail
      exact ⟨left, right, rfl⟩

theorem arithmetic_results {opcode : Old.Opcode} (admitted : ArithmeticOpcode opcode) :
    opcode.results = 1 := by
  cases opcode <;> first | rfl | cases admitted

theorem arithmetic_total (oracle : CallOracle) (memory : Memory)
    {opcode : Old.Opcode} {value : Value Word} {words : List Word}
    (admitted : ArithmeticOpcode opcode) (shape : (Shape.tuple opcode.arity).Holds value words) :
    ∃ word, Opcode.step oracle opcode value memory (packValues [word]) memory := by
  cases opcode with
  | const word =>
    obtain rfl := shape_tuple_zero shape
    exact ⟨word, .const⟩
  | move =>
    obtain ⟨word, rfl⟩ := shape_tuple_one shape
    exact ⟨word, .move⟩
  | unary op =>
    obtain ⟨word, rfl⟩ := shape_tuple_one shape
    exact ⟨op.eval word, .unary⟩
  | binary op =>
    obtain ⟨left, right, rfl⟩ := shape_tuple_two shape
    obtain ⟨word, step⟩ := arithmetic_binary_total op admitted left right
    exact ⟨word, .binary step⟩
  | load | store | call | test => cases admitted

theorem shape_packed (word : Word) : (Shape.tuple 1).Holds (packValues [word]) [word] :=
  ⟨rfl, rfl⟩

/-- The nonconstant branch of the actual implementation, stated once. -/
theorem foldTm_op_eq (known : List Abstract) (opcode : Old.Opcode) (argument : Old.Tm)
    (nonconstant : ∀ word, opcode ≠ .const word) :
    foldTm known (.op opcode argument) =
      let folded := foldTm known argument
      match constantOp opcode folded.2.1 with
      | some word => (.op (.const word) .unit, packed word, folded.2.2 + 1)
      | none => (.op opcode folded.1, .unknown, folded.2.2) := by
  cases opcode with
  | const word => exact False.elim (nonconstant word rfl)
  | move | unary | binary | load | store | call | test => rfl

/-- The shared semantic argument for a nonconstant arithmetic instruction. -/
theorem foldTm_op_total (oracle : CallOracle) (memory : Memory)
    {known : List Abstract} {env : Semantics.Env Word} {opcode : Old.Opcode} {argument : Old.Tm}
    (nonconstant : ∀ word, opcode ≠ .const word) (admitted : ArithmeticOpcode opcode)
    {arg : Value Word} {words : List Word}
    (sourceArg : Semantics.Tm.Eval (Opcode.step oracle) env argument memory arg memory)
    (foldedArg : Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known argument).1 memory arg memory)
    (modelsArg : Models (foldTm known argument).2.1 arg)
    (shapeArg : (Shape.tuple opcode.arity).Holds arg words) :
    ∃ word,
      Semantics.Tm.Eval (Opcode.step oracle) env (.op opcode argument)
        memory (packValues [word]) memory ∧
      Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known (.op opcode argument)).1
        memory (packValues [word]) memory ∧
      Models (foldTm known (.op opcode argument)).2.1 (packValues [word]) := by
  have equation := foldTm_op_eq known opcode argument nonconstant
  cases fold : constantOp opcode (foldTm known argument).2.1 with
  | none =>
    obtain ⟨word, step⟩ := arithmetic_total oracle memory admitted shapeArg
    refine ⟨word, .op sourceArg step, ?_, ?_⟩
    · simpa only [equation, fold] using (Semantics.Tm.Eval.op foldedArg step)
    · simp only [equation, fold, Models]
  | some word =>
    have step : Opcode.step oracle opcode arg memory (packValues [word]) memory :=
      constantOp_models oracle memory modelsArg fold
    refine ⟨word, .op sourceArg step, ?_, ?_⟩
    · simpa only [equation, fold] using
        (Semantics.Tm.Eval.op .unit (Opcode.step.const (value := word)))
    · simpa only [equation, fold] using models_packed word

/-- Actual traversal soundness for the existing typed pure total RTL fragment.
Both executions are constructed from syntax, independently of successful source
evaluation, and both leave the original memory unchanged. -/
theorem foldTm_total (oracle : CallOracle) (memory : Memory)
    {context : List Shape} {term : Old.Tm} {shape : Shape}
    (typed : TmFits [] context term shape)
    (pure : term.ForallInstr ArithmeticOpcode)
    {known : List Abstract} {env : Semantics.Env Word}
    (models : EnvironmentModels known env) (shapes : ShapeEnvironment context env) :
    ∃ value words,
      Semantics.Tm.Eval (Opcode.step oracle) env term memory value memory ∧
      Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known term).1 memory value memory ∧
      Models (foldTm known term).2.1 value ∧ shape.Holds value words := by
  induction typed generalizing known env with
  | var lookup =>
    obtain ⟨words, holds⟩ := shapes _ _ lookup
    exact ⟨_, words, .var, .var, models _, holds⟩
  | unit => exact ⟨.unit, [], .unit, .unit, rfl, rfl, rfl⟩
  | @pair context first rest n typedA typedB ihA ihB =>
    show ∃ value words,
      Semantics.Tm.Eval (Opcode.step oracle) env _ memory value memory ∧
      Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known _).1 memory value memory ∧
      Models (foldTm known _).2.1 value ∧ (Shape.tuple _).Holds value words
    obtain ⟨a, aw, sourceA, foldedA, modelsA, shapeA⟩ :
        ∃ value words,
          Semantics.Tm.Eval (Opcode.step oracle) env first memory value memory ∧
          Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known first).1 memory value memory ∧
          Models (foldTm known first).2.1 value ∧ Shape.word.Holds value words :=
      ihA pure.1 models shapes
    obtain ⟨b, bw, sourceB, foldedB, modelsB, shapeB⟩ :
        ∃ value words,
          Semantics.Tm.Eval (Opcode.step oracle) env rest memory value memory ∧
          Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known rest).1 memory value memory ∧
          Models (foldTm known rest).2.1 value ∧ (Shape.tuple n).Holds value words :=
      ihB pure.2 models shapes
    obtain ⟨word, rfl, rfl⟩ := shapeA
    obtain ⟨rfl, length⟩ := shapeB
    refine ⟨.pair (.atom word) (packValues bw), word :: bw,
      .pair sourceA sourceB, ?_, ?_, rfl, ?_⟩
    · exact .pair foldedA foldedB
    · exact ⟨_, _, rfl, modelsA, modelsB⟩
    · exact congrArg Nat.succ length
  | @op context opcode argument notTest typedArg ih =>
    show ∃ value words,
      Semantics.Tm.Eval (Opcode.step oracle) env (.op opcode argument) memory value memory ∧
      Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known (.op opcode argument)).1 memory value memory ∧
      Models (foldTm known (.op opcode argument)).2.1 value ∧
      (Shape.tuple opcode.results).Holds value words
    obtain ⟨arg, words, sourceArg, foldedArg, modelsArg, shapeArg⟩ :
        ∃ value words,
          Semantics.Tm.Eval (Opcode.step oracle) env argument memory value memory ∧
          Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known argument).1 memory value memory ∧
          Models (foldTm known argument).2.1 value ∧ (Shape.tuple opcode.arity).Holds value words :=
      ih pure.2 models shapes
    cases opcode with
    | const word =>
      obtain rfl := shape_tuple_zero shapeArg
      exact ⟨packValues [word], [word], .op sourceArg .const, .op sourceArg .const,
        models_packed word, shape_packed word⟩
    | move | unary op | binary op =>
      obtain ⟨word, source, folded, modelsResult⟩ := foldTm_op_total oracle memory
        (by intro word impossible; cases impossible) pure.1 sourceArg foldedArg modelsArg shapeArg
      exact ⟨packValues [word], [word], source, folded, modelsResult, shape_packed word⟩
    | load | store | call | test => cases pure.1
  | let₁ typedValue typedBody ihValue ihBody =>
    obtain ⟨value, vw, sourceValue, foldedValue, modelsValue, shapeValue⟩ := ihValue pure.1 models shapes
    obtain ⟨result, rw, sourceBody, foldedBody, modelsBody, shapeBody⟩ :=
      ihBody pure.2 (environment_cons models modelsValue) (shape_environment_cons shapes shapeValue)
    exact ⟨result, rw, .let₁ sourceValue sourceBody, .let₁ foldedValue foldedBody, modelsBody, shapeBody⟩
  | @let₂ context argument body n resultShape typedValue typedBody ihValue ihBody =>
    show ∃ value words,
      Semantics.Tm.Eval (Opcode.step oracle) env _ memory value memory ∧
      Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known _).1 memory value memory ∧
      Models (foldTm known _).2.1 value ∧ Shape.Holds _ value words
    obtain ⟨value, vw, sourceValue, foldedValue, modelsValue, shapeValue⟩ :
        ∃ value words,
          Semantics.Tm.Eval (Opcode.step oracle) env argument memory value memory ∧
          Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known argument).1 memory value memory ∧
          Models (foldTm known argument).2.1 value ∧ (Shape.tuple (n + 1)).Holds value words :=
      ihValue pure.1 models shapes
    obtain ⟨rfl, length⟩ := shapeValue
    cases vw with
    | nil => cases length
    | cons word rest =>
      show ∃ value words,
        Semantics.Tm.Eval (Opcode.step oracle) env (.let₂ argument body) memory value memory ∧
        Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known (.let₂ argument body)).1 memory value memory ∧
        Models (foldTm known (.let₂ argument body)).2.1 value ∧ resultShape.Holds value words
      have shapes' : ShapeEnvironment (.tuple n :: .word :: context)
          (Semantics.extend (Semantics.extend env (.atom word)) (packValues rest)) :=
        shape_environment_cons (shape_environment_cons shapes
        (shape := Shape.word) (words := [word]) ⟨word, rfl, rfl⟩)
        (shape := Shape.tuple _) (words := rest) ⟨rfl, Nat.succ.inj length⟩
      have components :
          let components := match (foldTm known _).2.1 with
            | .pair a b => (a, b)
            | _ => (.unknown, .unknown)
          Models components.1 (.atom word) ∧ Models components.2 (packValues rest) :=
        models_components modelsValue
      obtain ⟨result, rw, sourceBody, foldedBody, modelsBody, shapeBody⟩ :=
        ihBody pure.2 (environment_cons (environment_cons models components.1) components.2) shapes'
      exact ⟨result, rw, .let₂ sourceValue sourceBody, .let₂ foldedValue foldedBody, modelsBody, shapeBody⟩

/-- Arithmetic steps cannot consult the call oracle. -/
theorem arithmetic_oracle {oracle other : CallOracle}
    {opcode : Old.Opcode} {argument result : Value Word} {before after : Memory}
    (admitted : ArithmeticOpcode opcode)
    (step : Opcode.step oracle opcode argument before result after) :
    Opcode.step other opcode argument before result after := by
  cases step with
  | const => exact .const
  | move => exact .move
  | unary => exact .unary
  | binary equation => exact .binary equation
  | load | store | call | test_nonzero | test_zero => cases admitted

/-- Changing the oracle preserves each actual evaluation of a pure term. -/
theorem eval_oracle {oracle other : CallOracle}
    {env : Semantics.Env Word} {term : Old.Tm} {before after : Memory} {value : Value Word}
    (evaluation : Semantics.Tm.Eval (Opcode.step oracle) env term before value after)
    (pure : term.ForallInstr ArithmeticOpcode) :
    Semantics.Tm.Eval (Opcode.step other) env term before value after := by
  induction evaluation with
  | var => exact .var
  | unit => exact .unit
  | op _ step ih => exact .op (ih pure.2) (arithmetic_oracle pure.1 step)
  | pair _ _ ihA ihB => exact .pair (ihA pure.1) (ihB pure.2)
  | let₁ _ _ ihA ihB => exact .let₁ (ihA pure.1) (ihB pure.2)
  | let₂ _ _ ihA ihB => exact .let₂ (ihA pure.1) (ihB pure.2)
  | inl _ ih => exact .inl (ih pure)
  | inr _ ih => exact .inr (ih pure)
  | case_inl _ _ ihA ihB => exact .case_inl (ihA pure.1) (ihB pure.2.1)
  | case_inr _ _ ihA ihB => exact .case_inr (ihA pure.1) (ihB pure.2.2)

theorem eval_deterministic {oracle : CallOracle}
    {env : Semantics.Env Word} {term : Old.Tm} {before after₁ after₂ : Memory}
    {value₁ value₂ : Value Word} (pure : term.ForallInstr ArithmeticOpcode)
    (first : Semantics.Tm.Eval (Opcode.step oracle) env term before value₁ after₁)
    (second : Semantics.Tm.Eval (Opcode.step oracle) env term before value₂ after₂) :
    value₁ = value₂ ∧ after₁ = after₂ := by
  have deterministic : Silmaril.Machine.RTL.CallOracle.Deterministic noCalls := by
    intro _ _ _ _ _ _ _ impossible
    cases impossible
  exact (eval_oracle (other := noCalls) first pure).deterministic
    (Opcode.step_deterministic deterministic) (eval_oracle second pure)

/-- Folding only retains admitted instructions or introduces a constant. -/
theorem foldTm_pure {term : Old.Tm} (pure : term.ForallInstr ArithmeticOpcode)
    (known : List Abstract) : (foldTm known term).1.ForallInstr ArithmeticOpcode := by
  induction term generalizing known with
  | var | unit => trivial
  | op opcode argument ih =>
    cases opcode with
    | const => exact pure
    | move | unary | binary =>
      simp only [foldTm]
      split
      · exact ⟨trivial, trivial⟩
      · exact ⟨pure.1, ih pure.2 known⟩
    | load | store | call | test => cases pure.1
  | pair a b ihA ihB => exact ⟨ihA pure.1 known, ihB pure.2 known⟩
  | let₁ a b ihA ihB => exact ⟨ihA pure.1 known, ihB pure.2 _⟩
  | let₂ a b ihA ihB => exact ⟨ihA pure.1 known, ihB pure.2 _⟩
  | inl a ih | inr a ih | abort a ih => exact ih pure known
  | case a left right ihA ihLeft ihRight =>
    exact ⟨ihA pure.1 known, ihLeft pure.2.1 _, ihRight pure.2.2 _⟩

/-- Every actual finite observation is preserved in both directions. Totality
above also ensures this equivalence is never vacuous on the stated fragment. -/
theorem foldTm_eval_iff (oracle : CallOracle) (memory : Memory)
    {context : List Shape} {term : Old.Tm} {shape : Shape}
    (typed : TmFits [] context term shape) (pure : term.ForallInstr ArithmeticOpcode)
    {known : List Abstract} {env : Semantics.Env Word}
    (models : EnvironmentModels known env) (shapes : ShapeEnvironment context env)
    (value : Value Word) (after : Memory) :
    Semantics.Tm.Eval (Opcode.step oracle) env (foldTm known term).1 memory value after ↔
      Semantics.Tm.Eval (Opcode.step oracle) env term memory value after := by
  obtain ⟨result, _, source, folded, _, _⟩ := foldTm_total oracle memory typed pure models shapes
  constructor
  · intro evaluation
    obtain ⟨rfl, rfl⟩ := eval_deterministic (foldTm_pure pure known) folded evaluation
    exact source
  · intro evaluation
    obtain ⟨rfl, rfl⟩ := eval_deterministic pure source evaluation
    exact folded

end Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding
