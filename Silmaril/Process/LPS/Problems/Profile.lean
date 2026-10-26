module

public import Silmaril.Process.LPS.Problems.Basic
public import Silmaril.Process.LPS.NativeX86AllStatements
public import Silmaril.Process.LPS.RunHelpers

/-!
# Problems over an explicit statement profile

`Problem.denote?` (`Problems.Basic`) states every shape through `Silmaril.Process.LPS.Shapes`,
which runs the reference (asm-generic numbered) syscall table and the reference launch. Passing a
native x86-64 ISA to it does not select the native table or the x86 entry stack
(`NativeX86Statements`). This file states the same shapes over a `StatementProfile` (ISA,
launch, syscall table, refusal reading, allocation classifier, entry and input domains):

* `StatementProfile.haltsWithinBudget` and `StatementProfile.haltsMayFail`: `Shapes.v:274` and
  `Shapes.v:291` over a profile. At the literal reference profile they are `rfl`-equal to the
  `Shapes` definitions (`reference_haltsWithinBudget`, `reference_haltsMayFail`); the four
  agreement forms already are (`StatementProfile.reference_agrees` and its siblings).
* `ProfileProblem`: a harness, a profile and the artifact of each build. `ProfileProblem.denote`
  states a `Statement` through the profile shapes only. A shape the profile has no reading of
  (the RV64GC input restriction, the distribution bound and the decidability shape) is `False`:
  unprovable, never vacuous. `Problem.toProfile` is a `Problem` at the reference profile, and
  `toProfile_denote_*` say that where its images exist its `denote?` is `some` of its profile statement.
* `nativeX86`: the hub's native x86-64 profile (`NativeX86.All.profile`): the canonical native
  machine `Machines.x86ExtNative`, the complete native table `NativeX86.All.nativeTable`, the x86
  launch and entry stack, the native refusal reading and the native allocation classifier, on
  the minimal `AT_HWCAP` profile (`NativeX86.All.minimal`, #3492's `Statements.ValidInput`).
* `PairProblem`: the agreement shapes applied to two programs that are not builds of one
  harness (a probe and its variant).
* Extended shapes (#3610): `StatementProfile.haltsMayFailWith` adds a property of every
  execution's trace to `haltsMayFail` (`TraceSpec`: what was written to stdout), over the same
  executions; `haltsMayFail_of_with` is the proved implication back to the published shape.

## Reading the refusal readings

Under `Env.mayFail` the native refusal filter refuses nothing (`nativeX86_refusals_mayFail`):
every injected failure is an outcome, as in the plain reading. So a `haltsMayFail` statement on
the native profile is a statement about every outcome of every call.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS

namespace StatementProfile

variable {Artifact : Type}

/-- LPS `must_exit_in` over a profile: every maximal execution of the profile's initialized
run under `reading` exits normally with a code in `allowed` (no error, kill or divergence). -/
def MustExitIn (profile : StatementProfile Artifact) (reading : Reading) (allowed : List Word)
    (artifact : Artifact) (limit : Int) (entry : ExecEntry) (input : ProcInput) : Prop :=
  MustExitInAt (profile.image artifact).segments (profile.syscalls reading)
    (profile.refusals reading) allowed (profile.initialConfig artifact entry limit input)

/-- `Shapes.v:274` `halts_within_budget` over a profile: in the forced-only reading, on every
valid launch on which the run is not refused for budget, every execution exits with an allowed
status. -/
def haltsWithinBudget (profile : StatementProfile Artifact) (limit : Int) (allowed : List Word)
    (artifact : Artifact) : Prop :=
  ∀ (entry : ExecEntry) (input : ProcInput), profile.validEntry artifact entry input →
    profile.validInput false input →
    ¬ profile.budgetRefused (some forcedOnlyCfg) artifact limit entry input →
    profile.MustExitIn (some forcedOnlyCfg) allowed artifact limit entry input

/-- `Shapes.v:291` `halts_may_fail` over a profile: in the may-fail reading, at the 16 GiB
source budget, every execution of every valid launch exits with an allowed status. -/
def haltsMayFail (profile : StatementProfile Artifact) (allowed : List Word)
    (artifact : Artifact) : Prop :=
  ∀ (entry : ExecEntry) (input : ProcInput), profile.validEntry artifact entry input →
    profile.validInput false input →
    profile.MustExitIn (some mayFailCfg) allowed artifact sourceAllocLimit entry input

theorem reference_haltsWithinBudget (isa : UserIsa) (limit : Int) (allowed : List Word)
    (img : Image) :
    (reference isa).haltsWithinBudget limit allowed img =
      Shapes.haltsWithinBudget isa limit allowed img := rfl

theorem reference_haltsMayFail (isa : UserIsa) (allowed : List Word) (img : Image) :
    (reference isa).haltsMayFail allowed img = Shapes.haltsMayFail isa allowed img := rfl

/-- `Shapes.v:310` `halts_may_fail_mono` over a profile. -/
theorem haltsMayFail_mono (profile : StatementProfile Artifact) {S₁ S₂ : List Word}
    {artifact : Artifact} (sub : S₁ ⊆ S₂) (h : profile.haltsMayFail S₁ artifact) :
    profile.haltsMayFail S₂ artifact :=
  fun entry input validEntry validInput =>
    Shapes.mustExitInAt_mono profile.isa sub (h entry input validEntry validInput)

/-- `Shapes.v:302` `halts_within_budget_mono` over a profile. -/
theorem haltsWithinBudget_mono (profile : StatementProfile Artifact) {limit : Int}
    {S₁ S₂ : List Word} {artifact : Artifact} (sub : S₁ ⊆ S₂)
    (h : profile.haltsWithinBudget limit S₁ artifact) :
    profile.haltsWithinBudget limit S₂ artifact :=
  fun entry input validEntry validInput budget =>
    Shapes.mustExitInAt_mono profile.isa sub (h entry input validEntry validInput budget)

/-! ## Extended shapes (#3610) -/

/-- The extended halting shape: as `haltsMayFail`, and the trace of every execution satisfies
`good`. Stated as one `Omni.Exec` judgment over the same executions. -/
def haltsMayFailWith (profile : StatementProfile Artifact) (allowed : List Word)
    (good : List Event → Prop) (artifact : Artifact) : Prop :=
  ∀ (entry : ExecEntry) (input : ProcInput), profile.validEntry artifact entry input →
    profile.validInput false input →
    Omni.Exec (profile.image artifact).segments (profile.syscalls (some mayFailCfg))
      (profile.refusals (some mayFailCfg))
      (profile.initialConfig artifact entry sourceAllocLimit input)
      (fun trace outcome => Omni.ExitsIn allowed trace outcome ∧ good trace)

/-- The extended shape implies the published one. -/
theorem haltsMayFail_of_with (profile : StatementProfile Artifact) {allowed : List Word}
    {good : List Event → Prop} {artifact : Artifact}
    (h : profile.haltsMayFailWith allowed good artifact) : profile.haltsMayFail allowed artifact :=
  fun entry input validEntry validInput =>
    (Omni.mustExitInAt_iff_exec allowed _).mpr
      ((h entry input validEntry validInput).consequence fun _ _ both => both.1)

end StatementProfile

namespace Problems

open Silmaril.Process.LPS.Machines

/-! ## The native x86-64 profile -/

/-- The hub's native x86-64 statement profile on the canonical native machine and the minimal
`AT_HWCAP` profile. -/
abbrev nativeX86 : StatementProfile X86Launch.Snapshot :=
  NativeX86.All.profile x86ExtNative (some NativeX86.All.minimal)

theorem nativeX86_syscalls (reading : Reading) :
    nativeX86.syscalls reading = dispatch NativeX86.All.nativeTable := rfl

theorem familyMayFail_mayFail (family : SpuriousFamily) : familyMayFail mayFailCfg family = true := by
  cases family <;> rfl

theorem injectedFamilyOff_mayFail (input : SyscallInput) : injectedFamilyOff mayFailCfg input = false := by
  unfold injectedFamilyOff
  split <;> simp [familyMayFail_mayFail]

theorem injectedFamilyOffX86Ext_mayFail (input : SyscallInput) :
    NativeX86.All.injectedFamilyOffX86Ext mayFailCfg input = false := by
  unfold NativeX86.All.injectedFamilyOffX86Ext
  split <;> simp [injectedFamilyOff_mayFail]

/-- `Env.mayFail` refuses nothing: every family may fail, so no injected refusal is filtered. -/
theorem nativeX86_refusals_mayFail : nativeX86.refusals (some mayFailCfg) = noFilter := by
  funext input model effect
  apply propext
  show NativeX86.All.spuriousRefusalCfgX86Ext (dispatch NativeX86.All.nativeTable) mayFailCfg
    input model effect ↔ False
  constructor
  · rintro ⟨off, _⟩
    rw [injectedFamilyOffX86Ext_mayFail] at off
    exact Bool.false_ne_true off
  · intro h
    exact h.elim

/-- The valid inputs of the native profile are the probe kit's launch inputs with `abort()` not
modelled. -/
theorem nativeX86_validInput (input : ProcInput) :
    nativeX86.validInput false input ↔
      X86Launch.ValidInput input ∧ input.abortTerminal = false := by
  simp only [NativeX86.All.profile, NativeX86.All.ValidInputFor, NativeX86.All.minimal,
    X86Launch.ValidInput]
  tauto

/-- The valid entries of the native profile are the probe kit's launch envelope
(`X86Launch.ValidEntry`: the stack pointer in its window and 16-aligned, the mmap base in its
bounds, the image below the whole stack reservation). That envelope is an inhabited profile,
not every Linux ASLR/execve choice, so a statement over `nativeX86` quantifies over it. -/
theorem nativeX86_validEntry (snapshot : X86Launch.Snapshot) (entry : ExecEntry) (input : ProcInput) :
    nativeX86.validEntry snapshot entry input ↔ X86Launch.ValidEntry x86ExtNative snapshot entry input :=
  Iff.rfl

/-! ## Problems over a profile -/

/-- The meaning of an agreement shape over two profiles. The RV64GC shapes restrict the input
domain to an `AT_HWCAP` value the profile has no reading of: `False`. -/
def AgreeShape.denoteProfile {Plain Sanitized : Type} (plainProfile : StatementProfile Plain)
    (sanitizedProfile : StatementProfile Sanitized) (limP limS : Int) (plain : Plain)
    (san : Sanitized) : AgreeShape → Prop
  | .agrees => StatementProfile.agrees plainProfile sanitizedProfile limP limS plain san
  | .agreesIn env =>
    StatementProfile.agreesIn plainProfile sanitizedProfile env.cfg limP limS plain san
  | .abortModelled =>
    StatementProfile.agreesAbortModelled plainProfile sanitizedProfile limP limS plain san
  | .inAbortModelled env =>
    StatementProfile.agreesInAbortModelled plainProfile sanitizedProfile env.cfg limP limS plain
      san
  | .rv64gc | .abortModelledRv64gc | .inRv64gc _ => False

/-- A harness over an explicit statement profile, with the artifact of each build. -/
structure ProfileProblem (Artifact : Type) where
  harness : Harness
  profile : StatementProfile Artifact
  images : Build → Option Artifact

namespace ProfileProblem

variable {Artifact : Type} (p : ProfileProblem Artifact)

/-- `False` unless the build has an artifact. -/
def withImage {α : Sort _} (none' : α) (b : Build) (k : Artifact → α) : α :=
  match p.images b with
  | some a => k a
  | none => none'

/-- The meaning of a statement about this problem, through the profile shapes only. The
distribution bound and the decidability shape have no profile form yet: `False`. -/
def denote : (s : Statement) → s.Sort
  | .agrees san budgets shape =>
    p.withImage False .plain fun plain => p.withImage False san fun sanImg =>
      shape.denoteProfile p.profile p.profile budgets.budgets.limSource
        budgets.budgets.limTarget plain sanImg
  | .haltsWithinBudget b budgets exits =>
    p.withImage False b fun a => p.profile.haltsWithinBudget budgets.budgets.limSource exits.codes a
  | .haltsMayFail b exits =>
    p.withImage False b fun a => p.profile.haltsMayFail exits.codes a
  | .disagreesAtMost .. => fun _ => False
  | .agreementDecidable .. => False

end ProfileProblem

/-- A `Problem` (its machine with the reference table and launch) as a profile problem. -/
def Problem.toProfile (p : Problem) : ProfileProblem Image :=
  ⟨p.harness, StatementProfile.reference p.isa, p.images⟩

theorem Problem.toProfile_denote_haltsMayFail (p : Problem) {b : Build} {img : Image}
    (h : p.images b = some img) (exits : ExitChoice) :
    p.denote? (.haltsMayFail b exits) = some (p.toProfile.denote (.haltsMayFail b exits)) := by
  rw [Problem.denote?_haltsMayFail h]
  simp only [ProfileProblem.denote, ProfileProblem.withImage, Problem.toProfile, h]
  rfl

theorem Problem.toProfile_denote_haltsWithinBudget (p : Problem) {b : Build} {img : Image}
    (h : p.images b = some img) (budgets : BudgetChoice) (exits : ExitChoice) :
    p.denote? (.haltsWithinBudget b budgets exits) =
      some (p.toProfile.denote (.haltsWithinBudget b budgets exits)) := by
  rw [Problem.denote?_haltsWithinBudget h]
  simp only [ProfileProblem.denote, ProfileProblem.withImage, Problem.toProfile, h]
  rfl

/-- On the four agreement shapes without the RV64GC restriction, the profile statement of a
`Problem` is its `Shapes` statement. -/
theorem Problem.toProfile_denote_agrees (p : Problem) {san : Build} {plain sanImg : Image}
    (hp : p.images .plain = some plain) (hs : p.images san = some sanImg)
    (budgets : BudgetChoice) (shape : AgreeShape)
    (notRv : ∀ env, shape ≠ .rv64gc ∧ shape ≠ .abortModelledRv64gc ∧ shape ≠ .inRv64gc env) :
    p.denote? (.agrees san budgets shape) = some (p.toProfile.denote (.agrees san budgets shape)) := by
  rw [Problem.denote?_agrees hp hs]
  simp only [ProfileProblem.denote, ProfileProblem.withImage, Problem.toProfile, hp, hs]
  cases shape with
  | rv64gc => exact absurd rfl (notRv .mayFail).1
  | abortModelledRv64gc => exact absurd rfl (notRv .mayFail).2.1
  | inRv64gc env => exact absurd rfl (notRv env).2.2
  | _ => rfl

/-- The native x86-64 problem of a harness: `nativeX86` and the snapshot of each build. -/
def nativeProblem (harness : Harness) (images : Build → Option X86Launch.Snapshot) :
    ProfileProblem X86Launch.Snapshot :=
  ⟨harness, nativeX86, images⟩

/-- Only the plain build. -/
def plainOnly {α : Type} (a : α) : Build → Option α
  | .plain => some a
  | _ => none

/-! ## Two programs compared by an agreement shape -/

/-- Two programs that are not builds of one harness (a probe and its variant), compared by one
of the published agreement shapes at a budget pair. -/
structure PairProblem (Artifact : Type) where
  name : String
  profile : StatementProfile Artifact
  first : Artifact
  second : Artifact
  budgets : BudgetChoice
  shape : AgreeShape

/-- The agreement shape on the two programs, `first` in the plain position. -/
def PairProblem.denote {Artifact : Type} (p : PairProblem Artifact) : Prop :=
  p.shape.denoteProfile p.profile p.profile p.budgets.budgets.limSource p.budgets.budgets.limTarget
    p.first p.second

/-! ## Extended problems (#3610) -/

/-- What an execution's trace must show, beyond its exit status. -/
inductive TraceSpec where
  /-- The bytes written to descriptor 1 form a prefix of `bytes` (a short write is allowed),
  and nothing is written to any other descriptor. -/
  | stdoutPrefix (bytes : List Byte)
  /-- The bytes written to descriptor 1 form a nonempty prefix of `bytes` (a short write is
  allowed, writing nothing is not), and nothing is written to any other descriptor. -/
  | stdoutNonemptyPrefix (bytes : List Byte)
  /-- Nothing is written to any descriptor. -/
  | silent
  /-- Descriptor 1 receives a prefix of each piece in turn (each piece a separate write, which
  may be cut short), and nothing is written to any other descriptor. -/
  | stdoutPieces (pieces : List (List Byte))
  /-- What is written to descriptor 1 is a prefix of what is read from descriptor 0, and
  nothing is written to any other descriptor. -/
  | echo
  deriving DecidableEq

/-- The bytes a trace writes to descriptor `fd`. -/
def written (fd : Word) : List Event → List Byte
  | [] => []
  | .writeEv ch b :: rest => if ch = fd then b :: written fd rest else written fd rest
  | _ :: rest => written fd rest

/-- Whether a trace writes to a descriptor other than `fd`. -/
def writesOtherThan (fd : Word) : List Event → Bool
  | [] => false
  | .writeEv ch _ :: rest => ch != fd || writesOtherThan fd rest
  | _ :: rest => writesOtherThan fd rest

/-- The bytes a trace reads from descriptor `fd`. -/
def readFrom (fd : Word) : List Event → List Byte
  | [] => []
  | .readEv ch b :: rest => if ch = fd then b :: readFrom fd rest else readFrom fd rest
  | _ :: rest => readFrom fd rest

def TraceSpec.denote : TraceSpec → List Event → Prop
  | .stdoutPrefix bytes => fun trace => written 1 trace <+: bytes ∧ writesOtherThan 1 trace = false
  | .stdoutNonemptyPrefix bytes => fun trace =>
    written 1 trace ≠ [] ∧ written 1 trace <+: bytes ∧ writesOtherThan 1 trace = false
  | .silent => fun trace => written 1 trace = [] ∧ writesOtherThan 1 trace = false
  | .stdoutPieces pieces => fun trace =>
    (∃ parts : List (List Byte), List.Forall₂ (fun part piece => part <+: piece) parts pieces ∧
      written 1 trace = parts.flatten) ∧ writesOtherThan 1 trace = false
  | .echo => fun trace => written 1 trace <+: readFrom 0 trace ∧ writesOtherThan 1 trace = false

/-- An extended statement: a published halting shape strengthened by a trace property. -/
inductive ExtStatement where
  /-- `haltsMayFail` with every execution's trace satisfying `spec`. -/
  | haltsMayFailWith (b : Build) (exits : ExitChoice) (spec : TraceSpec)

/-- The published statement an extended one strengthens. -/
def ExtStatement.base : ExtStatement → Statement
  | .haltsMayFailWith b exits _ => .haltsMayFail b exits

def ProfileProblem.denoteExt {Artifact : Type} (p : ProfileProblem Artifact) :
    ExtStatement → Prop
  | .haltsMayFailWith b exits spec =>
    p.withImage False b fun a => p.profile.haltsMayFailWith exits.codes spec.denote a

/-- An extended statement implies the published statement it strengthens. -/
theorem ProfileProblem.denote_of_denoteExt {Artifact : Type} (p : ProfileProblem Artifact)
    (s : ExtStatement) (h : p.denoteExt s) : p.denote s.base := by
  cases s with
  | haltsMayFailWith b exits spec =>
    simp only [denoteExt, ExtStatement.base, denote, withImage] at h ⊢
    cases found : p.images b with
    | none => simp only [found] at h
    | some a =>
      simp only [found] at h ⊢
      exact StatementProfile.haltsMayFail_of_with _ h

end Problems

end Silmaril.Process.LPS
