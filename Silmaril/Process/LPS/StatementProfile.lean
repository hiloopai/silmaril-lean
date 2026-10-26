module

public import Silmaril.Process.LPS.Shapes
public import Silmaril.Process.LPS.NativeX86Budget

/-! # Agreement statements with an explicit process profile

An ISA alone does not select a syscall ABI, loader or budget diagnostic. This
additive profile keeps those choices together. Behaviors and budget exclusions
are derived from the actual LPS transitions at its chosen initialization.

The four agreement forms share one formula. The source profile chooses the
input domain; entry validity is checked independently for both artifacts, as
in the literal LPS statements. Reference profiles below preserve those literal
statements, including their original stack and abort input restrictions.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS

structure StatementProfile (Artifact : Type) where
  isa : UserIsa
  image : Artifact → Image
  initialConfig : Artifact → ExecEntry → Int → ProcInput → Config isa
  syscalls : Reading → Sys SyscallEffect
  refusals : Reading → RefusalFilter
  allocClassifier : AllocBudgetClassifier
  validEntry : Artifact → ExecEntry → ProcInput → Prop
  /-- False is the ordinary reading; true models abort as a terminal death. -/
  validInput : Bool → ProcInput → Prop

namespace StatementProfile

variable {Plain Sanitized : Type}

/-- The initialized profile's real process behavior, with no hidden fallback
to the reference syscall table or entry-stack builder. -/
def run (profile : StatementProfile Plain) (reading : Reading) (artifact : Plain)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Behavior :=
  let initial := profile.initialConfig artifact entry limit input
  { traces := ObsTrace (profile.image artifact).segments
      (profile.syscalls reading) (profile.refusals reading) initial
    errors := ReachesError (profile.image artifact).segments
      (profile.syscalls reading) (profile.refusals reading) initial
    allErrors := AllTracesError (profile.image artifact).segments
      (profile.syscalls reading) (profile.refusals reading) initial
    unmodeled := ReachesUnmodeled (profile.image artifact).segments
      (profile.syscalls reading) (profile.refusals reading) initial }

/-- Reachability and classification use the same initialization, transitions
and refusal interpretation as the behavior. -/
def budgetRefused (profile : StatementProfile Plain) (reading : Reading) (artifact : Plain)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Prop :=
  RunBudgetRefusedFromUsing profile.isa profile.allocClassifier
    (profile.image artifact).segments (profile.syscalls reading) (profile.refusals reading)
    (profile.initialConfig artifact entry limit input)

def GoodBehavior (abortModelled : Bool) (behavior : Behavior) : Prop :=
  if abortModelled then ErrorFreeUnkilled behavior else ErrorFree behavior

/-- One common shape for all four agreement forms. Entry draws are independent;
the source budget premise and the source's input domain match the LPS shapes. -/
def agreement (plain : StatementProfile Plain) (sanitized : StatementProfile Sanitized)
    (reading : Reading) (abortModelled : Bool) (plainLimit sanitizedLimit : Int)
    (plainArtifact : Plain) (sanitizedArtifact : Sanitized) : Prop :=
  ∀ (plainEntry sanitizedEntry : ExecEntry) (input : ProcInput),
    plain.validEntry plainArtifact plainEntry input →
    sanitized.validEntry sanitizedArtifact sanitizedEntry input →
    plain.validInput abortModelled input →
    ¬ plain.budgetRefused reading plainArtifact plainLimit plainEntry input →
    GoodBehavior abortModelled (plain.run reading plainArtifact plainLimit plainEntry input) ∧
      GoodBehavior abortModelled
        (sanitized.run reading sanitizedArtifact sanitizedLimit sanitizedEntry input) ∧
      TraceEquiv (plain.run reading plainArtifact plainLimit plainEntry input).traces
        (sanitized.run reading sanitizedArtifact sanitizedLimit sanitizedEntry input).traces

def agrees (plain : StatementProfile Plain) (sanitized : StatementProfile Sanitized)
    (plainLimit sanitizedLimit : Int) (plainArtifact : Plain) (sanitizedArtifact : Sanitized) : Prop :=
  agreement plain sanitized none false plainLimit sanitizedLimit plainArtifact sanitizedArtifact

def agreesIn (plain : StatementProfile Plain) (sanitized : StatementProfile Sanitized)
    (environment : SpuriousCfg) (plainLimit sanitizedLimit : Int)
    (plainArtifact : Plain) (sanitizedArtifact : Sanitized) : Prop :=
  agreement plain sanitized (some environment) false
    plainLimit sanitizedLimit plainArtifact sanitizedArtifact

def agreesAbortModelled (plain : StatementProfile Plain) (sanitized : StatementProfile Sanitized)
    (plainLimit sanitizedLimit : Int) (plainArtifact : Plain) (sanitizedArtifact : Sanitized) : Prop :=
  agreement plain sanitized none true plainLimit sanitizedLimit plainArtifact sanitizedArtifact

def agreesInAbortModelled (plain : StatementProfile Plain) (sanitized : StatementProfile Sanitized)
    (environment : SpuriousCfg) (plainLimit sanitizedLimit : Int)
    (plainArtifact : Plain) (sanitizedArtifact : Sanitized) : Prop :=
  agreement plain sanitized (some environment) true
    plainLimit sanitizedLimit plainArtifact sanitizedArtifact

/-- The literal reference profile, not a native-ABI interpretation of an
arbitrary ISA. In particular, its initialization intentionally remains legacy. -/
def reference (isa : UserIsa) : StatementProfile Image where
  isa := isa
  image := id
  initialConfig := initConfig isa
  syscalls := fun _ => syscallSpec
  refusals := fun reading => match reading with
    | none => noFilter
    | some environment => spuriousRefusalCfg syscallSpec environment
  allocClassifier := allocBudgetRefusedB
  validEntry := ValidEntry
  validInput := fun abort => if abort then ValidInputAbort else ValidInput

theorem reference_run (isa : UserIsa) (reading : Reading) (image : Image)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) :
    (reference isa).run reading image limit entry input = runIn isa reading image limit entry input := by
  cases reading <;> rfl

theorem reference_budget (isa : UserIsa) (reading : Reading) (image : Image)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) :
    (reference isa).budgetRefused reading image limit entry input ↔
      BudgetRefusedIn isa reading image limit entry input := by
  cases reading <;> rfl

theorem reference_agrees (plainIsa sanitizedIsa : UserIsa) (plainLimit sanitizedLimit : Int)
    (plain sanitized : Image) :
    agrees (reference plainIsa) (reference sanitizedIsa) plainLimit sanitizedLimit plain sanitized =
      Shapes.agrees plainIsa sanitizedIsa plainLimit sanitizedLimit plain sanitized := rfl

theorem reference_agreesIn (plainIsa sanitizedIsa : UserIsa) (environment : SpuriousCfg)
    (plainLimit sanitizedLimit : Int) (plain sanitized : Image) :
    agreesIn (reference plainIsa) (reference sanitizedIsa) environment plainLimit sanitizedLimit plain sanitized =
      Shapes.agreesIn plainIsa sanitizedIsa environment plainLimit sanitizedLimit plain sanitized := rfl

theorem reference_agreesAbortModelled (plainIsa sanitizedIsa : UserIsa)
    (plainLimit sanitizedLimit : Int) (plain sanitized : Image) :
    agreesAbortModelled (reference plainIsa) (reference sanitizedIsa) plainLimit sanitizedLimit plain sanitized =
      Shapes.agreesAbortModelled plainIsa sanitizedIsa plainLimit sanitizedLimit plain sanitized := rfl

theorem reference_agreesInAbortModelled (plainIsa sanitizedIsa : UserIsa) (environment : SpuriousCfg)
    (plainLimit sanitizedLimit : Int) (plain sanitized : Image) :
    agreesInAbortModelled (reference plainIsa) (reference sanitizedIsa) environment plainLimit sanitizedLimit
        plain sanitized =
      Shapes.agreesInAbortModelled plainIsa sanitizedIsa environment plainLimit sanitizedLimit
        plain sanitized := rfl

/-- Safety of identical artifacts suffices for self-agreement, with the same
entry-independent behavior requirement as the original universal statement. -/
theorem agreement_self_of_safe (profile : StatementProfile Plain) (reading : Reading)
    (abortModelled : Bool) (limit : Int) (artifact : Plain)
    (safe : ∀ entry input, profile.validEntry artifact entry input →
      profile.validInput abortModelled input →
      ¬ profile.budgetRefused reading artifact limit entry input →
      GoodBehavior abortModelled (profile.run reading artifact limit entry input))
    (entryIndependent : ∀ first second input,
      profile.validEntry artifact first input → profile.validEntry artifact second input →
      profile.validInput abortModelled input →
      ¬ profile.budgetRefused reading artifact limit first input →
      TraceEquiv (profile.run reading artifact limit first input).traces
        (profile.run reading artifact limit second input).traces)
    (budgetIndependent : ∀ first second input,
      profile.validEntry artifact first input → profile.validEntry artifact second input →
      profile.validInput abortModelled input →
      profile.budgetRefused reading artifact limit second input →
      profile.budgetRefused reading artifact limit first input) :
    agreement profile profile reading abortModelled limit limit artifact artifact := by
  intro first second input firstValid secondValid inputValid firstBudget
  refine ⟨safe first input firstValid inputValid firstBudget, ?_,
    entryIndependent first second input firstValid secondValid inputValid firstBudget⟩
  exact safe second input secondValid inputValid
    (fun refused => firstBudget (budgetIndependent first second input firstValid secondValid inputValid refused))

/-- A concrete, valid, within-budget error refutes any agreement assertion.
This prevents one bad native execution from being hidden by trace equality. -/
theorem not_agreement_of_source_error (plain : StatementProfile Plain)
    (sanitized : StatementProfile Sanitized) (reading : Reading) (abortModelled : Bool)
    (plainLimit sanitizedLimit : Int) (plainArtifact : Plain) (sanitizedArtifact : Sanitized)
    (plainEntry sanitizedEntry : ExecEntry) (input : ProcInput)
    (plainValid : plain.validEntry plainArtifact plainEntry input)
    (sanitizedValid : sanitized.validEntry sanitizedArtifact sanitizedEntry input)
    (inputValid : plain.validInput abortModelled input)
    (budget : ¬ plain.budgetRefused reading plainArtifact plainLimit plainEntry input)
    (error : (plain.run reading plainArtifact plainLimit plainEntry input).errors) :
    ¬ agreement plain sanitized reading abortModelled plainLimit sanitizedLimit
      plainArtifact sanitizedArtifact := by
  intro agreed
  have good := (agreed plainEntry sanitizedEntry input plainValid sanitizedValid inputValid budget).1
  cases abortModelled with
  | false => exact good error
  | true => exact good.1 error

end StatementProfile
end Silmaril.Process.LPS
