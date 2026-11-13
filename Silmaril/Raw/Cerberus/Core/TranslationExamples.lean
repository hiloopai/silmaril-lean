module

public import Silmaril.Cerberus.Core.SeqReach.Defs
public import Silmaril.Compile.Category.Language

/-! # Actual Core behaviours for translation examples

The expressions here execute in the canonical Core dynamics with concrete memory.
They start as expressions, rather than going through C parsing or whole-file startup.
The language instance observes successful integer termination only: it does not
identify errors, undefined behaviour, divergence or output with integer results.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.TranslationExamples

open Dynamics SeqReach

/-- An empty context for closed Core expressions. -/
def emptyFile : Program where
  main := none
  callingConvention := .normal
  tagDefs := ∅
  stdlib := ∅
  impl := ∅
  globs := []
  funs := ∅
  extern := ∅
  funInfo := ∅
  loopAttributes := ∅
  visibleObjects := ∅

def integer (n : Int) : EE :=
  .mk [] (.pure (.mk [] () (.val (.object (.integer n)))))

/-- A genuine Core choice, retaining both defined results. -/
def nondet : EE := .mk [] (.nd [integer 0, integer 1])

/-- One legal resolution of the choice. -/
def ordered : EE := integer 0

def start (e : EE) : State := ⟨.effectExpr e ∅, [], {}⟩

def finish (n : Int) (m : Mem.Concrete.State := {}) : State :=
  ⟨.halt (.defined (.object (.integer n))), [], m⟩

/-- Successful integer observations, using unbounded relational reachability. -/
def returns (e : EE) (n : Int) : Prop :=
  ∃ m, Reaches emptyFile ∅ (start e) (finish n m)

/-- Actual expression semantics, restricted to successful integer observations.
Final memory and output are projected away. An expression with no successful
integer termination has empty behaviour here; this instance alone therefore does
not express safety or termination. Use the outcome theorems below for this fragment. -/
def language : Silmaril.Compile.Category.Language where
  Iface := Unit
  Prog := EE
  iface := fun _ => ()
  Obs := Int
  beh e := {n | returns e n}

theorem integer_reaches (n : Int) :
    Reaches emptyFile ∅ (start (integer n)) (finish n) := by
  refine (show Reaches emptyFile ∅ (start (integer n))
      ⟨.value (.object (.integer n)), [], {}⟩ from ?_).trans ?_
  · simpa [start, integer, focusMemory, runtimeValue, runtimeObject] using
      (effect_pure_reaches (file := emptyFile) (labels := ∅) []
        (pure_value [] (.object (.integer n)) ∅) [] {})
  · exact .single ⟨.terminal (.defined (.object (.integer n))),
      Step.respond (by intro o; simp) (by
        simpa [finish, request, requestAux, awaitsScheduling] using
          (Respond.end_ (mem := ({} : Mem.Concrete.State))
            (o := .defined (.object (.integer n)))))⟩

theorem nondet_select {n : Int} (hn : n = 0 ∨ n = 1) :
    Reaches emptyFile ∅ (start nondet) (start (integer n)) := by
  apply Relation.ReflTransGen.single
  refine ⟨.tau, Step.respond (by intro o; simp [start]) ?_⟩
  change Respond ({} : Mem.Concrete.State)
    (request emptyFile ∅ (start nondet)) .tau (start (integer n))
  have member : (Control.effectExpr (integer n) (∅ : Env), ([] : List Frame)) ∈
      [(Control.effectExpr (integer 0) ∅, []), (Control.effectExpr (integer 1) ∅, [])] := by
    rcases hn with rfl | rfl <;> simp
  simpa [start, nondet, request, requestAux, awaitsScheduling] using Respond.choose member

theorem nondet_returns_zero : returns nondet 0 :=
  ⟨{}, (nondet_select (Or.inl rfl)).trans (integer_reaches 0)⟩

theorem nondet_returns_one : returns nondet 1 :=
  ⟨{}, (nondet_select (Or.inr rfl)).trans (integer_reaches 1)⟩

theorem ordered_returns_zero : returns ordered 0 :=
  ⟨{}, integer_reaches 0⟩

/-- The five possible states of a literal computation. This is a finite invariant
of the existing dynamics, rather than a second execution semantics. -/
private inductive IntegerStage (n : Int) : State → Prop where
  | effect : IntegerStage n (start (integer n))
  | pure : IntegerStage n
      ⟨.pureExpr (.mk [] () (.val (.object (.integer n)))) ∅,
        [.diagnosticLocation ({} : Mem.Concrete.State).currentLocation], {}⟩
  | diagnostic : IntegerStage n
      ⟨.value (.object (.integer n)),
        [.diagnosticLocation ({} : Mem.Concrete.State).currentLocation], {}⟩
  | value : IntegerStage n ⟨.value (.object (.integer n)), [], {}⟩
  | halt : IntegerStage n (finish n)

private theorem integerStage_step {n : Int} {s t : State} {a : Label}
    (hs : IntegerStage n s) (step : Step emptyFile ∅ s a t) : IntegerStage n t := by
  cases hs <;> cases step with
  | respond live response =>
    first
    | exact (live _ rfl).elim
    | simp only [start, integer, request, requestAux, awaitsScheduling,
        runtimeValue, runtimeObject] at response
      cases response
      first | exact .pure | exact .diagnostic | exact .value | exact .halt

private theorem integerStage_reaches {n : Int} {s t : State}
    (hs : IntegerStage n s) (reach : Reaches emptyFile ∅ s t) : IntegerStage n t := by
  induction reach with
  | refl => exact hs
  | tail reach step ih =>
    rcases step with ⟨a, step⟩
    exact integerStage_step ih step

private theorem integerStage_finish {n z : Int} {m : Mem.Concrete.State}
    (hs : IntegerStage n (finish z m)) : z = n := by
  cases hs
  rfl

private theorem integerStage_halt {n : Int} {o : Outcome} {k : List Frame}
    {m : Mem.Concrete.State} (hs : IntegerStage n ⟨.halt o, k, m⟩) :
    o = .defined (.object (.integer n)) := by
  cases hs
  rfl

theorem integer_returns_iff (n z : Int) : returns (integer n) z ↔ z = n := by
  constructor
  · rintro ⟨m, reach⟩
    exact integerStage_finish (integerStage_reaches .effect reach)
  · intro equal
    subst z
    exact ⟨{}, integer_reaches n⟩

private def ChoiceStage (s : State) : Prop :=
  s = start nondet ∨ ∃ n, (n = 0 ∨ n = 1) ∧ IntegerStage n s

private theorem choiceStage_step {s t : State} {a : Label}
    (hs : ChoiceStage s) (step : Step emptyFile ∅ s a t) : ChoiceStage t := by
  rcases hs with rfl | ⟨n, hn, hs⟩
  · cases step with
    | respond live response =>
      simp only [start, nondet, request, requestAux, awaitsScheduling] at response
      cases response with
      | choose member =>
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨0, Or.inl rfl, .effect⟩
        · exact Or.inr ⟨1, Or.inr rfl, .effect⟩
  · exact Or.inr ⟨n, hn, integerStage_step hs step⟩

private theorem choiceStage_reaches {s t : State}
    (hs : ChoiceStage s) (reach : Reaches emptyFile ∅ s t) : ChoiceStage t := by
  induction reach with
  | refl => exact hs
  | tail reach step ih =>
    rcases step with ⟨a, step⟩
    exact choiceStage_step ih step

/-- Every reached terminal outcome is defined and is either 0 or 1. In particular
the fragment cannot reach UB, an error or an unsupported ending. -/
theorem nondet_terminal_defined {o : Outcome} {k : List Frame} {m : Mem.Concrete.State}
    (reach : Reaches emptyFile ∅ (start nondet) ⟨.halt o, k, m⟩) :
    o = .defined (.object (.integer 0)) ∨ o = .defined (.object (.integer 1)) := by
  rcases choiceStage_reaches (Or.inl rfl) reach with impossible | ⟨n, hn, stage⟩
  · cases impossible
  · rcases hn with rfl | rfl
    · exact Or.inl (integerStage_halt stage)
    · exact Or.inr (integerStage_halt stage)

theorem ordered_terminal_defined {o : Outcome} {k : List Frame} {m : Mem.Concrete.State}
    (reach : Reaches emptyFile ∅ (start ordered) ⟨.halt o, k, m⟩) :
    o = .defined (.object (.integer 0)) :=
  integerStage_halt (integerStage_reaches .effect reach)

theorem nondet_returns_iff (n : Int) : returns nondet n ↔ n = 0 ∨ n = 1 := by
  constructor
  · rintro ⟨m, reach⟩
    have invariant := choiceStage_reaches (Or.inl rfl) reach
    rcases invariant with impossible | ⟨z, hz, stage⟩
    · cases impossible
    · rwa [integerStage_finish stage]
  · intro hn
    exact ⟨{}, (nondet_select hn).trans (integer_reaches n)⟩

theorem nondet_excludes_two : ¬ returns nondet 2 := by
  simp [nondet_returns_iff]

theorem ordered_excludes_one : ¬ returns ordered 1 := by
  simp [ordered, integer_returns_iff]

/-- Ordered choice removes a possible behaviour, so it is a refinement. -/
theorem ordered_refines_nondet : language.Refines nondet ordered := by
  refine ⟨rfl, ?_⟩
  intro n hn
  change returns ordered n at hn
  change returns nondet n
  have : n = (0 : Int) := (integer_returns_iff 0 n).mp hn
  exact nondet_returns_iff n |>.mpr (Or.inl this)

/-- Refinement here is strict: the ordered expression loses the actual result 1. -/
theorem ordered_not_equivalent : ¬ language.BehEquiv nondet ordered := by
  intro equiv
  exact ordered_excludes_one (equiv.2.2 nondet_returns_one)

end Silmaril.Cerberus.Core.TranslationExamples
