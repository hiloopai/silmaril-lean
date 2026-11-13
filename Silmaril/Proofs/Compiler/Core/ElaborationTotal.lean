module

public import Silmaril.Compiler.Core.ElaborationTotal.Defs
public import Silmaril.Compiler.Core.ElaborationProcess.Thms
public import Silmaril.Compiler.Category.Cerberus.Thms
public import Silmaril.Proofs.Compiler.Core.ElaborationTotal.Return

/-! A checked literal-main document has a forced finite execution. This proves
universal satisfaction over the actual Core institution, including all finite
prefixes and infinite executions. Source elaboration success is derived from
the real Functions elaborator, not supplied as a theorem premise. -/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationTotal
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Category.Cerberus

/-- The category-language assertion is the same universal predicate on the
same actual Core operational model. -/
theorem satisfies_category {model : Silmaril.Cerberus.Institution.Model} {number : Int}
    (correct : Silmaril.Cerberus.Institution.Satisfies model (returnsInteger number)) :
    Silmaril.Compiler.Category.Cerberus.language.Sat model {behavior | returnsInteger number behavior} :=
  (Silmaril.Compiler.Category.Cerberus.sat_iff model (returnsInteger number)).2 correct

/-- The terminal specification excludes UB from every finite reachable state. -/
theorem satisfies_noUndefinedBehaviour {model : Silmaril.Cerberus.Institution.Model} {number : Int}
    (correct : Silmaril.Cerberus.Institution.Satisfies model (returnsInteger number)) :
    Silmaril.Cerberus.Institution.Satisfies model Silmaril.Cerberus.Institution.noUndefinedBehaviour := by
  intro behavior realized
  cases behavior with
  | finite actions state =>
      intro location undefined halted
      have impossible := (correct (.finite actions state) realized (.ub location undefined) halted).1
      cases impossible
  | infinite => trivial

/-- No infinite execution satisfies the literal-return specification. -/
theorem satisfies_terminates {model : Silmaril.Cerberus.Institution.Model} {number : Int}
    (correct : Silmaril.Cerberus.Institution.Satisfies model (returnsInteger number)) :
    Silmaril.Cerberus.Institution.Satisfies model Silmaril.Cerberus.Institution.terminates := by
  intro behavior realized
  cases behavior with
  | finite => trivial
  | infinite => exact correct _ realized

/-- All terminal outcomes, including errors and unsupported outcomes, are
constrained by `returnsInteger`; stdout is empty at every such endpoint. -/
theorem satisfies_terminalOutput {model : Silmaril.Cerberus.Institution.Model} {number : Int}
    (correct : Silmaril.Cerberus.Institution.Satisfies model (returnsInteger number)) :
    Silmaril.Cerberus.Institution.Satisfies model
      (Silmaril.Cerberus.Institution.terminalOutput (· = "")) := by
  intro behavior realized
  cases behavior with
  | finite actions state =>
      intro outcome halted
      exact (correct (.finite actions state) realized outcome halted).2
  | infinite => trivial

/-- A syntactically recognized document satisfies the universal specification.
The recognizer is the existing checked actual-Core syntax predicate. -/
theorem recognized_satisfies (document : Codec.Document) (number : Int)
    (recognized : ReturnLit.recognize document = some number) (arguments : List String) :
    ∃ start labels, Process.Spec.coreStart document arguments = .ok (start, labels) ∧
      Silmaril.Cerberus.Institution.Satisfies (Process.model document start labels) (returnsInteger number) := by
  obtain ⟨start, labels, finish, started, forced, halted, stdout⟩ := recognized_forced document number recognized
    (Map.ofList (document.enumBindings.getD [])) arguments
  refine ⟨start, labels, started, ?_⟩
  intro behavior realized
  cases behavior with
  | finite actions state =>
      intro outcome stateHalted
      have reachable := (Process.finite_iff_reaches (Process.model document start labels) state).1
        ⟨actions, realized⟩
      have same := Forced.terminal_unique forced halted reachable stateHalted
      cases same
      exact ⟨Control.halt.inj (stateHalted.symm.trans halted), stdout⟩
  | infinite states actions =>
      exact Forced.no_infinite forced halted states actions realized.1 realized.2

/-- Exactly one completed process observation is possible. Existence is the
earlier actual reachability theorem; the converse uses universal satisfaction. -/
theorem recognized_coreBeh_iff (document : Codec.Document) (number : Int)
    (recognized : ReturnLit.recognize document = some number) (arguments : List String)
    (observation : Process.Spec.Obs) :
    Process.Spec.CoreBeh document arguments observation ↔
      observation = .exit (number % 256).toNat [] := by
  obtain ⟨start, labels, started, correct⟩ := recognized_satisfies document number recognized arguments
  constructor
  · show Process.Spec.CoreBeh document arguments observation →
      observation = .exit (number % 256).toNat []
    intro behavior
    obtain ⟨execution, realized, observed⟩ :=
      (Process.coreBeh_iff_realises_observes document arguments start labels started observation).1 behavior
    have terminal : returnsInteger number execution := correct execution realized
    cases execution with
    | finite actions state =>
        show observation = .exit (number % 256).toNat []
        cases observation with
        | exit status bytes =>
            show (.exit status bytes : Process.Spec.Obs) = .exit (number % 256).toNat []
            obtain ⟨value, halted, statusAllowed, output⟩ := observed
            obtain ⟨returned, stdout⟩ := terminal (.defined value) halted
            have valueEquality : value = .loaded (.specified (.integer number)) := Outcome.defined.inj returned
            have statusEquality : status = (number % 256).toNat := by
              simpa only [valueEquality, Process.Spec.exitStatuses] using statusAllowed
            have bytesEquality : bytes = [] := by
              simpa [Process.Spec.coreBytes, stdout] using output.symm
            exact congrArg₂ (fun status bytes => (.exit status bytes : Process.Spec.Obs))
              statusEquality bytesEquality
        | abort bytes =>
            have impossible : Outcome.aborted = .defined (.loaded (.specified (.integer number))) :=
              (terminal .aborted observed.1).1
            cases impossible
        | trap | fault | diverges | exhausted => exact observed.elim
    | infinite states actions => exact terminal.elim
  · intro same
    exact same.symm ▸ ReturnLit.recognize_sound document number recognized arguments

/-- Actual restricted typed-Ail elaboration, successful actual Core startup,
and a universal behavioral result for its generated program. The source has
the existing concrete signed-int annotation; no independent Ail semantics or
native/compiler-category refinement theorem is asserted. -/
theorem literal_total (config : Silmaril.Cerberus.Target.Config)
    (types : Silmaril.Cerberus.Target.Environment) (runtime : Functions.RuntimeInputs)
    (source : ElaborationProcess.LiteralMain) (freshness : Freshness.Context)
    (available : freshness.next + 2 ≤ freshness.maximum)
    (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Construction.Pure)
    (found : Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1)
      runtime.stdlib = some (conversion, .function resultType parameters body))
    (conversionRecognized : ConvInt.isConvLoadedInt
      (source.bindings runtime freshness conversion).toFile conversion = true)
    (bounds : ConvInt.IsInt source.number) (commit implementation : String)
    (enums : Option (List (Sym × IntegerType))) (arguments : List String) :
    let document := ElaborationProcess.document (source.bindings runtime freshness conversion)
      commit implementation enums
    ∃ start labels,
      Functions.elaborate config types runtime source.program freshness =
        (.ok document.bindings, ElaborationProcess.finalContext freshness) ∧
      Process.Spec.coreStart document arguments = .ok (start, labels) ∧
      Silmaril.Cerberus.Institution.Satisfies (Process.model document start labels) (returnsInteger source.number) ∧
      ∀ observation, Process.Spec.CoreBeh document arguments observation ↔
        observation = .exit (source.number % 256).toNat [] := by
  let document := ElaborationProcess.document (source.bindings runtime freshness conversion)
    commit implementation enums
  have recognized : ReturnLit.recognize document = some source.number :=
    ElaborationProcess.literal_recognize source runtime freshness conversion commit implementation enums
      conversionRecognized bounds
  obtain ⟨start, labels, started, correct⟩ := recognized_satisfies document source.number recognized arguments
  exact ⟨start, labels,
    ElaborationProcess.literal_elaborate config types runtime source freshness available conversion
      resultType parameters body found,
    started, correct, recognized_coreBeh_iff document source.number recognized arguments⟩

end Silmaril.Compiler.Core.ElaborationTotal
