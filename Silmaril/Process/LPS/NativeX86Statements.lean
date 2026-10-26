module

public import Silmaril.Process.LPS.StatementProfile
public import Silmaril.Process.LPS.X86NativeSystem

/-! # Native x86 agreement statements select a complete statement profile

Passing a native ISA to the literal reference Shapes does not select native
syscalls or an x86 entry stack. These additive statements instead take the
actual native System for each environment reading. A System's chosen filter
is used literally; callers explicitly decide how readings select Systems.

Snapshots, independent entry draws, native launch initialization and native
allocation classification are retained together. The ordinary and abort
input domains both retain ValidInputCore and the minimal x86 HWCAP policy;
they differ in the required abortTerminal value. There is no claim that the
native ABI is equivalent to the reference ABI.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.Statements

open Machines

abbrev Systems := Reading → System

def ValidInput (abortModelled : Bool) (input : ProcInput) : Prop :=
  X86Launch.ValidInput input ∧ input.abortTerminal = abortModelled

/-- Canonical, Wire and explicit flag-oracle ISAs can use this same native
launch and system policy. The caller must select an appropriate x86 ISA. -/
def profile (isa : UserIsa) (systems : Systems) : StatementProfile X86Launch.Snapshot where
  isa := isa
  image := X86Launch.Snapshot.image
  initialConfig := X86Launch.init isa
  syscalls := fun reading => (systems reading).spec
  refusals := fun reading => (systems reading).refused
  allocClassifier := NativeX86.allocBudgetRefusedB
  validEntry := X86Launch.ValidEntry isa
  validInput := ValidInput

theorem validInput_core (abortModelled : Bool) (input : ProcInput)
    (valid : ValidInput abortModelled input) : ValidInputCore input := valid.1.1

theorem validInput_hwcap (abortModelled : Bool) (input : ProcInput)
    (valid : ValidInput abortModelled input) : input.hwcap = 0 := valid.1.2

theorem validInput_abort (abortModelled : Bool) (input : ProcInput)
    (valid : ValidInput abortModelled input) : input.abortTerminal = abortModelled := valid.2

theorem profile_run (isa : UserIsa) (systems : Systems) (reading : Reading)
    (snapshot : X86Launch.Snapshot) (limit : Int) (entry : ExecEntry) (input : ProcInput) :
    (profile isa systems).run reading snapshot limit entry input =
      (systems reading).run isa snapshot limit entry input := rfl

theorem profile_budget (isa : UserIsa) (systems : Systems) (reading : Reading)
    (snapshot : X86Launch.Snapshot) (limit : Int) (entry : ExecEntry) (input : ProcInput) :
    (profile isa systems).budgetRefused reading snapshot limit entry input ↔
      (systems reading).RunBudgetRefused isa snapshot limit entry input := Iff.rfl

def agrees (plainIsa sanitizedIsa : UserIsa) (systems : Systems) (plainLimit sanitizedLimit : Int)
    (plain sanitized : X86Launch.Snapshot) : Prop :=
  StatementProfile.agrees (profile plainIsa systems) (profile sanitizedIsa systems)
    plainLimit sanitizedLimit plain sanitized

def agreesIn (plainIsa sanitizedIsa : UserIsa) (systems : Systems) (environment : SpuriousCfg)
    (plainLimit sanitizedLimit : Int) (plain sanitized : X86Launch.Snapshot) : Prop :=
  StatementProfile.agreesIn (profile plainIsa systems) (profile sanitizedIsa systems)
    environment plainLimit sanitizedLimit plain sanitized

def agreesAbortModelled (plainIsa sanitizedIsa : UserIsa) (systems : Systems)
    (plainLimit sanitizedLimit : Int) (plain sanitized : X86Launch.Snapshot) : Prop :=
  StatementProfile.agreesAbortModelled (profile plainIsa systems) (profile sanitizedIsa systems)
    plainLimit sanitizedLimit plain sanitized

def agreesInAbortModelled (plainIsa sanitizedIsa : UserIsa) (systems : Systems)
    (environment : SpuriousCfg) (plainLimit sanitizedLimit : Int)
    (plain sanitized : X86Launch.Snapshot) : Prop :=
  StatementProfile.agreesInAbortModelled (profile plainIsa systems) (profile sanitizedIsa systems)
    environment plainLimit sanitizedLimit plain sanitized

/-- Every native form is the same shared formula at its explicit reading. -/
theorem agrees_formula (plainIsa sanitizedIsa : UserIsa) (systems : Systems)
    (plainLimit sanitizedLimit : Int) (plain sanitized : X86Launch.Snapshot) :
    agrees plainIsa sanitizedIsa systems plainLimit sanitizedLimit plain sanitized =
      StatementProfile.agreement (profile plainIsa systems) (profile sanitizedIsa systems)
        none false plainLimit sanitizedLimit plain sanitized := rfl

theorem agreesIn_formula (plainIsa sanitizedIsa : UserIsa) (systems : Systems)
    (environment : SpuriousCfg) (plainLimit sanitizedLimit : Int)
    (plain sanitized : X86Launch.Snapshot) :
    agreesIn plainIsa sanitizedIsa systems environment plainLimit sanitizedLimit plain sanitized =
      StatementProfile.agreement (profile plainIsa systems) (profile sanitizedIsa systems)
        (some environment) false plainLimit sanitizedLimit plain sanitized := rfl

theorem agreesAbortModelled_formula (plainIsa sanitizedIsa : UserIsa) (systems : Systems)
    (plainLimit sanitizedLimit : Int) (plain sanitized : X86Launch.Snapshot) :
    agreesAbortModelled plainIsa sanitizedIsa systems plainLimit sanitizedLimit plain sanitized =
      StatementProfile.agreement (profile plainIsa systems) (profile sanitizedIsa systems)
        none true plainLimit sanitizedLimit plain sanitized := rfl

theorem agreesInAbortModelled_formula (plainIsa sanitizedIsa : UserIsa) (systems : Systems)
    (environment : SpuriousCfg) (plainLimit sanitizedLimit : Int)
    (plain sanitized : X86Launch.Snapshot) :
    agreesInAbortModelled plainIsa sanitizedIsa systems environment plainLimit sanitizedLimit plain sanitized =
      StatementProfile.agreement (profile plainIsa systems) (profile sanitizedIsa systems)
        (some environment) true plainLimit sanitizedLimit plain sanitized := rfl

end Silmaril.Process.LPS.NativeX86.Statements
