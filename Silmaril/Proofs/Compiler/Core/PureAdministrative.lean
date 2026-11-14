module

public import Silmaril.Compiler.Core.Source.PureAdministrative.Defs
@[expose] public section
namespace Silmaril.Compiler.Core.Source.PureAdministrative
open Silmaril.Cerberus.Core
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval

theorem FramesPlain.nil : FramesPlain [] := by
  constructor <;> simp [controlHasCCall, activeCall]

theorem FramesPlain.arguments {frames : List Frame} (plain : FramesPlain frames)
    (operator : Prim) (allowed : NoProcedure operator) (acc : List Val) (rest : List PE) (environment : Env) :
    FramesPlain (.arguments operator acc rest environment :: frames) := by
  rcases plain with ⟨callfree, inactive⟩
  cases operator <;> simp_all [NoProcedure, FramesPlain, controlHasCCall, activeCall]

theorem FramesPlain.pureIf {frames : List Frame} (plain : FramesPlain frames) (yes no : PE) (environment : Env) :
    FramesPlain (.pureIf yes no environment :: frames) := by
  rcases plain with ⟨callfree, inactive⟩
  constructor <;> simp_all [controlHasCCall, activeCall]

theorem FramesPlain.pureCase {frames : List Frame} (plain : FramesPlain frames)
    (branches : List (Pattern Sym × PE)) (environment : Env) :
    FramesPlain (.pureCase branches environment :: frames) := by
  rcases plain with ⟨callfree, inactive⟩
  constructor <;> simp_all [controlHasCCall, activeCall]

theorem FramesPlain.diagnosticLocation {frames : List Frame} (plain : FramesPlain frames) (location : Loc) :
    FramesPlain (.diagnosticLocation location :: frames) := by
  rcases plain with ⟨callfree, inactive⟩
  constructor <;> simp_all [controlHasCCall, activeCall]

theorem FramesPlain.annotations {frames : List Frame} (plain : FramesPlain frames) (accesses : List Access) :
    FramesPlain (.annotations accesses :: frames) := by
  rcases plain with ⟨callfree, inactive⟩
  constructor <;> simp_all [controlHasCCall, activeCall]

theorem FramesPlain.value {frames : List Frame} (plain : FramesPlain frames) (value : Val)
    (memory : Mem.Concrete.State) : Administrative.Plain ⟨.value value, frames, memory⟩ := by
  rcases plain with ⟨callfree, inactive⟩
  constructor
  · rfl
  · simpa only [controlHasCCall] using callfree
  · simpa only [activeCall] using inactive

theorem FramesPlain.expression {frames : List Frame} (plain : FramesPlain frames) (expression : PE)
    (environment : Env) (memory : Mem.Concrete.State) :
    Administrative.Plain ⟨.pureExpr expression environment, frames, memory⟩ := by
  rcases plain with ⟨callfree, inactive⟩
  constructor
  · rfl
  · simpa only [controlHasCCall] using callfree
  · simpa only [activeCall] using inactive

theorem FramesPlain.apply {frames : List Frame} (plain : FramesPlain frames) (operator : Prim)
    (allowed : NoProcedure operator) (values : List Val) (memory : Mem.Concrete.State) :
    Administrative.Plain ⟨.apply operator values, frames, memory⟩ := by
  rcases plain with ⟨callfree, inactive⟩
  constructor
  · rfl
  · cases operator <;> simp_all [NoProcedure, controlHasCCall]
  · simpa only [activeCall] using inactive

private theorem pure_running (expression : PE) (environment : Env) (frames : List Frame)
    (memory : Mem.Concrete.State) : Administrative.NotDone ⟨.pureExpr expression environment, frames, memory⟩ := by
  intro value accesses impossible
  cases impossible

private theorem value_running (value : Val) (frame : Frame) (frames : List Frame)
    (memory : Mem.Concrete.State) (notAnnotation : ∀ accesses, frame ≠ .annotations accesses) :
    Administrative.NotDone ⟨.value value, frame :: frames, memory⟩ := by
  intro value accesses valueEq annotationsEq
  cases frame <;> simp_all [annotationsOnly]

private theorem apply_path (file : Program) {labels : Labels} {operator : Prim} (allowed : PureEval.Plain operator)
    {values : List Val} {value : Val} {frames : List Frame} {memory : Mem.Concrete.State}
    (plain : FramesPlain frames) (evaluated : primitive operator values (tagsOf file memory) = .ok value) :
    Administrative.Path file labels ⟨.apply operator values, frames, memory⟩ ⟨.value value, frames, memory⟩ := by
  have notProcedure : NoProcedure operator := by cases operator <;> simp_all [PureEval.Plain, NoProcedure]
  refine .cons (.next (plain.apply operator notProcedure values memory)
    (by intro value accesses impossible; cases impossible) (plain.value value memory) ?_) (.refl (plain.value value memory))
  intro outer
  unfold tagsOf at evaluated
  cases operator <;> simp only [PureEval.Plain] at allowed <;>
    simp [requestAux, awaitsScheduling, evaluated]

private theorem arguments_path (file : Program) {labels : Labels} (operator : Prim) (allowed : NoProcedure operator)
    (expressions : List PE) (environment : Env) (frames : List Frame) (memory : Mem.Concrete.State)
    (plain : FramesPlain frames) (expression : PE)
    (requested : ∀ outer, requestAux file labels memory (.pureExpr expression environment) (frames ++ outer) false =
      arguments operator expressions environment (frames ++ outer)) :
    Administrative.Path file labels ⟨.pureExpr expression environment, frames, memory⟩
      (argState operator [] expressions environment frames memory) := by
  cases expressions with
  | nil =>
    refine .cons (.next (plain.expression expression environment memory) (pure_running _ _ _ _)
      (plain.apply operator allowed [] memory) ?_) (.refl (plain.apply operator allowed [] memory))
    simpa [arguments] using requested
  | cons first rest =>
    have targetPlain := (plain.arguments operator allowed [] rest environment).expression first environment memory
    refine .cons (.next (plain.expression expression environment memory) (pure_running _ _ _ _) targetPlain ?_)
      (.refl targetPlain)
    simpa [arguments] using requested

private theorem form_path (file : Program) (tags : Mem.Concrete.Tags) {operator : Prim}
    (allowed : PureEval.Plain operator) {expression : PE} {expressions : List PE} {values : List Val} {value : Val}
    {environment : Env}
    (first : ∀ labels frames memory, requestAux file labels memory (.pureExpr expression environment) frames false =
      arguments operator expressions environment frames)
    (args : Sound file tags environment (.inr expressions) (.inr values))
    (evaluated : primitive operator values tags = .ok value) :
    Sound file tags environment (.inl expression) (.inl value) := by
  have notProcedure : NoProcedure operator := by cases operator <;> simp_all [PureEval.Plain, NoProcedure]
  intro labels frames memory plain tagsEq
  exact (arguments_path file operator notProcedure expressions environment frames memory plain expression
    (fun outer => first labels (frames ++ outer) memory)).trans
    ((args labels operator [] frames memory notProcedure plain tagsEq).trans
      (apply_path file allowed plain (by rw [tagsEq]; exact evaluated)))

/-- The existing inductive big-step evaluation yields real uniform raw requests
and hence a compositional administrative path. No successful machine trace is
assumed. In particular pure function calls unfold the actual functionBody. -/
theorem pureEvaluation_path (file : Program) (tags : Mem.Concrete.Tags) {environment : Env}
    {source : PE ⊕ List PE} {target : Val ⊕ List Val}
    (evaluated : Eval file tags environment source target) : Sound file tags environment source target := by
  induction evaluated with
  | nil =>
    intro labels operator acc frames memory allowed plain _
    simpa [argState] using Administrative.Path.refl (plain.apply operator allowed acc memory)
  | @cons environment expression expressions value values _ _ firstIH restIH =>
    show Sound file tags environment (.inr (expression :: expressions)) (.inr (value :: values))
    intro labels operator acc frames memory allowed plain tagsEq
    have argPlain : FramesPlain (.arguments operator acc expressions environment :: frames) :=
      plain.arguments operator allowed acc expressions environment
    refine (firstIH labels _ memory argPlain tagsEq).trans ?_
    cases expressions with
    | nil =>
      have nextPlain : Administrative.Plain ⟨.apply operator (acc ++ [value]), frames, memory⟩ :=
        plain.apply operator allowed (acc ++ [value]) memory
      refine (Administrative.Path.cons (Administrative.Edge.next (argPlain.value value memory)
        (value_running _ _ _ _ (by intro accesses impossible; cases impossible)) nextPlain ?_) (.refl nextPlain)).trans ?_
      · intro outer
        simp [requestAux, awaitsScheduling]
      · simpa [argState] using restIH labels operator (acc ++ [value]) frames memory allowed plain tagsEq
    | cons next rest =>
      show Administrative.Path file labels
        ⟨.value value, .arguments operator acc (next :: rest) environment :: frames, memory⟩
        ⟨.apply operator (acc ++ (value :: values)), frames, memory⟩
      have nextPlain : Administrative.Plain
          ⟨.pureExpr next environment, .arguments operator (acc ++ [value]) rest environment :: frames, memory⟩ :=
        (plain.arguments operator allowed (acc ++ [value]) rest environment).expression next environment memory
      refine (Administrative.Path.cons (Administrative.Edge.next (argPlain.value value memory)
        (value_running _ _ _ _ (by intro accesses impossible; cases impossible)) nextPlain ?_) (.refl nextPlain)).trans ?_
      · intro outer
        simp [requestAux, awaitsScheduling]
      · simpa [argState] using restIH labels operator (acc ++ [value]) frames memory allowed plain tagsEq
  | val =>
    intro labels frames memory plain _
    refine .cons (.next (plain.expression _ _ _) (pure_running _ _ _ _) (plain.value _ _) ?_) (.refl (plain.value _ _))
    intro outer
    simp [requestAux, awaitsScheduling]
  | sym found =>
    intro labels frames memory plain _
    refine .cons (.next (plain.expression _ _ _) (pure_running _ _ _ _) (plain.value _ _) ?_) (.refl (plain.value _ _))
    intro outer
    simp [requestAux, awaitsScheduling, found]
  | ctor _ primitiveEq ih =>
    exact form_path file tags (operator := .ctor _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih primitiveEq
  | op _ primitiveEq ih =>
    exact form_path file tags (operator := .bin _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih primitiveEq
  | convInt _ primitiveEq ih =>
    exact form_path file tags (operator := .conv _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih primitiveEq
  | catchInt _ primitiveEq ih =>
    exact form_path file tags (operator := .catchInt _ _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih primitiveEq
  | wrapInt _ primitiveEq ih =>
    exact form_path file tags (operator := .wrapInt _ _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih primitiveEq
  | not _ primitiveEq ih =>
    exact form_path file tags (operator := .notBool) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih primitiveEq
  | @ifTrue environment ann condition yes no value _ _ conditionIH yesIH =>
    show Sound file tags environment (.inl (.mk ann () (.if_ condition yes no))) (.inl value)
    intro labels frames memory plain tagsEq
    have conditionPlain : FramesPlain (.pureIf yes no environment :: frames) := plain.pureIf yes no environment
    refine (Administrative.Path.cons (Administrative.Edge.next (plain.expression _ _ _) (pure_running _ _ _ _)
      (conditionPlain.expression condition environment memory) ?_) (.refl (conditionPlain.expression condition environment memory))).trans ?_
    · intro outer
      simp [requestAux, awaitsScheduling]
    · refine (conditionIH labels _ memory conditionPlain tagsEq).trans ?_
      refine (Administrative.Path.cons (Administrative.Edge.next (conditionPlain.value .true memory)
        (value_running _ _ _ _ (by intro accesses impossible; cases impossible)) (plain.expression yes environment memory) ?_)
        (.refl (plain.expression yes environment memory))).trans (yesIH labels frames memory plain tagsEq)
      intro outer
      simp [requestAux, awaitsScheduling]
  | @ifFalse environment ann condition yes no value _ _ conditionIH noIH =>
    show Sound file tags environment (.inl (.mk ann () (.if_ condition yes no))) (.inl value)
    intro labels frames memory plain tagsEq
    have conditionPlain : FramesPlain (.pureIf yes no environment :: frames) := plain.pureIf yes no environment
    refine (Administrative.Path.cons (Administrative.Edge.next (plain.expression _ _ _) (pure_running _ _ _ _)
      (conditionPlain.expression condition environment memory) ?_) (.refl (conditionPlain.expression condition environment memory))).trans ?_
    · intro outer
      simp [requestAux, awaitsScheduling]
    · refine (conditionIH labels _ memory conditionPlain tagsEq).trans ?_
      refine (Administrative.Path.cons (Administrative.Edge.next (conditionPlain.value .false memory)
        (value_running _ _ _ _ (by intro accesses impossible; cases impossible)) (plain.expression no environment memory) ?_)
        (.refl (plain.expression no environment memory))).trans (noIH labels frames memory plain tagsEq)
      intro outer
      simp [requestAux, awaitsScheduling]
  | @case_ environment ann expression branches matched bindings body value _ selected _ expressionIH bodyIH =>
    show Sound file tags environment (.inl (.mk ann () (.case_ expression branches))) (.inl value)
    intro labels frames memory plain tagsEq
    have casePlain : FramesPlain (.pureCase branches environment :: frames) := plain.pureCase branches environment
    refine (Administrative.Path.cons (Administrative.Edge.next (plain.expression _ _ _) (pure_running _ _ _ _)
      (casePlain.expression expression environment memory) ?_) (.refl (casePlain.expression expression environment memory))).trans ?_
    · intro outer
      simp [requestAux, awaitsScheduling]
    · refine (expressionIH labels _ memory casePlain tagsEq).trans ?_
      refine (Administrative.Path.cons (Administrative.Edge.next (casePlain.value matched memory)
        (value_running _ _ _ _ (by intro accesses impossible; cases impossible)) (plain.expression body (extendEnv bindings environment) memory) ?_)
        (.refl (plain.expression body (extendEnv bindings environment) memory))).trans (bodyIH labels frames memory plain tagsEq)
      intro outer
      simp [requestAux, awaitsScheduling, selected]
  | @call environment ann name expressions values body environment' value _ bodyEq _ argsIH bodyIH =>
    show Sound file tags environment (.inl (.mk ann () (.call name expressions))) (.inl value)
    intro labels frames memory plain tagsEq
    refine (arguments_path file (.call name) trivial expressions environment frames memory plain _
      (by intro outer; simp [requestAux, awaitsScheduling])).trans ?_
    refine (argsIH labels (.call name) [] frames memory trivial plain tagsEq).trans ?_
    refine (Administrative.Path.cons (Administrative.Edge.next (plain.apply (.call name) trivial values memory)
      (by intro value accesses impossible; cases impossible) (plain.expression body environment' memory) ?_)
      (.refl (plain.expression body environment' memory))).trans (bodyIH labels frames memory plain tagsEq)
    intro outer
    simp [requestAux, awaitsScheduling, bodyEq]

end Silmaril.Compiler.Core.Source.PureAdministrative
