module

public import Silmaril.Compiler.Native.Driver.Defs
public import Silmaril.Cerberus.Elaboration.Functions.Defs
public import Silmaril.Cerberus.Institution.Defs
public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Compile.Category.Pass
public import Silmaril.X86.Features.Machine
public import Silmaril.X86.Features.Embed
public import Silmaril.X86.Features.Ext.X87.Extension

/-!
# Actual native compiler correctness obligations

The translation below is exactly `Native.Driver.compile`. Source meaning uses
the actual explicit-input Functions elaborator and unbounded Core LTS. The target
executes fetched bytes with the existing feature-parametric integer/SSE/x87
machine, including explicit unsupported outcomes and infinite executions.

These are frozen obligations, not a correctness certificate. In particular, the
source domain and its elaboration inputs are explicit. The process observation is a
closed main call returning an exit status without output; native Linux process
startup, syscalls, libc and external linking still need their richer contract.
No execution or observation relation is supplied by the caller of the theorem.
-/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness

open Silmaril.Cerberus
open Silmaril.Compile
open Silmaril.Compile.Category
open CategoryTheory
open Silmaril.Cerberus.Elaboration

abbrev NativeState := Silmaril.X86.Features.MState

/-- Inputs to the actual source elaborator, supplied independently of native
compilation. No target, runtime parser or freshness-history adequacy follows
from this record, and none is selected implicitly. -/
structure ElaborationInputs where
  config : Silmaril.Cerberus.Target.Config
  runtime : Functions.RuntimeInputs
  freshness : Freshness.Context

/-- Typed input and the exact source execution/provenance environment. -/
structure Source where
  program : Ail.TypedProgram
  elaboration : ElaborationInputs
  options : Silmaril.Compile.Driver.Options := {}
  tag : String := "native"
  optimize : Bool := true
  commit : String
  implementation : String
  enumBindings : List (Sym × IntegerType) := []
  arguments : List String := Core.Startup.execArguments

/-- One enum registry is shared by elaboration, native lowering and Core startup. -/
def Source.types (source : Source) : Silmaril.Cerberus.Target.Environment :=
  ⟨Map.ofList source.enumBindings⟩

/-- Exactly the successful/error result of the actual explicit-state elaborator.
Its returned diagnostic state is available from Functions.elaborate; source
meaning below uses the returned bindings, never native compiler output. -/
def elaborate (source : Source) : Except State.Error Codec.FileBindings :=
  (Functions.elaborate source.elaboration.config source.types source.elaboration.runtime
    source.program source.elaboration.freshness).1

/-- A single translation unit may be accepted without defining main. Whole
program observations below are restricted to units that actually define it. -/
def Source.DefinesMain (source : Source) : Prop :=
  ∃ main body, source.program.1 = some main ∧
    (main, body) ∈ source.program.2.functionDefinitions

def compile (source : Source) : Except String String :=
  Silmaril.Compiler.Native.Driver.compile source.options source.tag source.program source.optimize source.enumBindings

/-- Elaborated Core carries the same implementation, enum and argv context. -/
def document (source : Source) (bindings : Codec.FileBindings) : Codec.Document :=
  { commit := source.commit, implementation := source.implementation,
    bindings, file := bindings.toFile, file_eq := rfl,
    enumBindings := some source.enumBindings }

/-- Source models are the actual Core startup state and saved-label environment.
This is not defined through the native compiler or through a bounded runner. -/
def Elaborates (source : Source) (model : Silmaril.Cerberus.Institution.Model) : Prop :=
  ∃ bindings, elaborate source = .ok bindings ∧
    model.program = bindings.toFile ∧
    Core.Dynamics.initial model.program (Map.ofList source.enumBindings) source.arguments =
      .ok (model.initialState, model.labels)

/-- Use the existing canonical feature machine and its real decoding order. -/
def step (exit : Silmaril.X86.Word) (state : NativeState) :
    Silmaril.X86.Features.Outcome :=
  Silmaril.X86.Features.step Silmaril.X86.Features.FeatureSet.baseline64
    [Silmaril.X86.Features.floatExt, Silmaril.X86.Features.Fpu.ext] exit state

/-- Every finite stop is retained, including undecodable/unmodeled bytes,
feature faults and floating exceptions. Divergence is an infinite execution. -/
inductive Observation where
  | returned (final : NativeState)
  | stopped (state : NativeState) (outcome : Silmaril.X86.Features.Outcome)
  | diverges

def Retires (exit : Silmaril.X86.Word) (before after : NativeState) : Prop :=
  step exit before = .retired after

def Realises (exit : Silmaril.X86.Word) (initial : NativeState) : Observation → Prop
  | .returned final =>
      ∃ before, Relation.ReflTransGen (Retires exit) initial before ∧
        step exit before = .returned final
  | .stopped state outcome =>
      Relation.ReflTransGen (Retires exit) initial state ∧ step exit state = outcome ∧
        (∀ after, outcome ≠ .retired after) ∧ (∀ final, outcome ≠ .returned final)
  | .diverges =>
      ∃ states : Nat → NativeState, states 0 = initial ∧
        ∀ n, Retires exit (states n) (states (n + 1))

/-- Fixed closed-main observation, without a caller-chosen readback relation.
Unsupported target instructions remain faults and cannot silently disappear.
The native process/IO contract must replace this no-output milestone before a
whole process compiler-correctness claim is made. -/
def observe : Observation → Silmaril.Compile.Core.Spec.Obs
  | .returned final => .exit ((final.state.core.read .rax).toNat % 256) []
  | .stopped _ _ => .fault []
  | .diverges => .diverges

structure Image where
  codeBase : Nat
  code : List Silmaril.X86.Byte
  entry : Silmaril.X86.Word
  exit : Silmaril.X86.Word
  argvAddress : Nat
  initial : NativeState

/-- The trusted assembler/linker/loader must establish concrete code bytes,
execute permissions, entry, native argv registers/storage and return address.
Its relationship to the exact emitted assembly remains an explicit premise. -/
def Loaded (arguments : List String) (image : Image) : Prop :=
  image.initial.state.core.rip = image.entry ∧
  image.codeBase ≤ image.entry.toNat ∧
  image.entry.toNat < image.codeBase + image.code.length ∧
  (image.exit.toNat < image.codeBase ∨ image.codeBase + image.code.length ≤ image.exit.toNat) ∧
  image.initial.memory.readBytes image.codeBase image.code.length = some image.code ∧
  image.initial.memory.Permitted .execute image.codeBase image.code.length ∧
  image.initial.state.core.read .rdi = BitVec.ofNat 64 arguments.length ∧
  image.initial.state.core.read .rsi = BitVec.ofNat 64 image.argvAddress ∧
  image.initial.memory.readBytes image.argvAddress (Silmaril.Compile.Core.Spec.argBlock image.argvAddress arguments).length =
    some ((Silmaril.Compile.Core.Spec.argBlock image.argvAddress arguments).map fun byte => BitVec.ofNat 8 byte.toNat) ∧
  image.initial.memory.readBytes (image.initial.state.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [image.exit]) ∧
  ((image.initial.state.core.read .rsp).toNat + 8) % 16 = 0 ∧
  image.initial.state.mxcsr = Silmaril.X86.Float.MXCSR.reset ∧
  image.initial.state.x87.control = 0x037F ∧
  image.initial.state.x87.status = 0 ∧
  image.initial.state.x87.tag = 0xFFFF

/-- An explicit unformalized assembly/link/load trust boundary. `loaded` checks
memory shape, not assembly semantics or data relocations. Nonempty loading of
accepted main-defined units in the explicit domain remains a pending premise;
unresolved external units need a successful-link/context domain.
No default relation or certificate is provided. -/
structure Toolchain (domain : Source → Prop) where
  loads : String → List String → Image → Prop
  loaded : ∀ assembly arguments image, loads assembly arguments image → Loaded arguments image
  produces : ∀ source assembly, domain source → source.DefinesMain → compile source = .ok assembly →
    Silmaril.Compile.Core.Spec.ArgsOk source.arguments → ∃ image, loads assembly source.arguments image

def sourceBehaviors (source : Source) : Set Observation := {observation |
  ∃ bindings, elaborate source = .ok bindings ∧
    (Silmaril.Compile.Core.Spec.CoreUB (document source bindings) source.arguments ∨
      Silmaril.Compile.Core.Spec.CoreBeh (document source bindings) source.arguments (observe observation))}

structure Target where
  assembly : String
  arguments : List String

def targetBehaviors {domain : Source → Prop} (toolchain : Toolchain domain) (target : Target) : Set Observation :=
  {observation | ∃ image, toolchain.loads target.assembly target.arguments image ∧
    Realises image.exit image.initial observation}

/-- An explicitly selected source domain, main definition and admissible argv.
The domain must state its own syntax/input-coherence scope; neither elaboration
success nor compiler acceptance is silently used to select it. The raw no-IO
projection still needs a richer process/linking model for broader domains. -/
abbrev Program (domain : Source → Prop) :=
  { source : Source // domain source ∧ source.DefinesMain ∧
    Silmaril.Compile.Core.Spec.ArgsOk source.arguments }

def sourceLanguage (domain : Source → Prop) : Language where
  Iface := PUnit
  Prog := Program domain
  iface _ := ⟨⟩
  Obs := Observation
  beh source := sourceBehaviors source.val

def targetLanguage {domain : Source → Prop} (toolchain : Toolchain domain) : Language where
  Iface := PUnit
  Prog := Target
  iface _ := ⟨⟩
  Obs := Observation
  beh := targetBehaviors toolchain

def convention (domain : Source → Prop) (toolchain : Toolchain domain) :
    sourceLanguage domain ⟶ targetLanguage toolchain :=
  ⟨id, Eq⟩

/-- Exactly the successful result of the executable pure native compiler. -/
def run {domain : Source → Prop} (source : Program domain) : Option Target :=
  match compile source.val with
  | .ok assembly => some ⟨assembly, source.val.arguments⟩
  | .error _ => none

namespace Task

/-- Coverage of actual native acceptances within the explicitly admitted source
domain. No global coverage of arbitrary source/runtime/target contexts is
asserted; a domain-specific proof must establish successful actual elaboration. -/
def elaborationCoversAccepted (domain : Source → Prop) : Prop :=
  ∀ (source : Program domain) assembly, compile source.val = .ok assembly →
    ∃ bindings, elaborate source.val = .ok bindings

/-- Every actual machine behavior, including stops and divergence, must be
allowed by the actual elaborated Core of the same admitted source. An output
or external-linking restriction belongs explicitly in the domain until the
process projection and linking model support it. No target/runtime agreement
or native pass proof follows from domain membership alone. -/
def machineRefinement (domain : Source → Prop) (toolchain : Toolchain domain) : Prop :=
  ∀ (source : Program domain) target, run source = some target →
    targetBehaviors toolchain target ⊆ sourceBehaviors source.val

end Task

/-- A future certificate must exhibit an accepted admitted program and prove
both source coverage and machine refinement. Empty domains and reject-all
compilation cannot satisfy this record. No certificate value or instance is supplied. -/
structure Certificate (domain : Source → Prop) (toolchain : Toolchain domain) : Prop where
  acceptedProgram : ∃ source : Program domain, ∃ assembly, compile source.val = .ok assembly
  sourceCoverage : Task.elaborationCoversAccepted domain
  machineRefinement : Task.machineRefinement domain toolchain

end Silmaril.Compiler.Native.Correctness
