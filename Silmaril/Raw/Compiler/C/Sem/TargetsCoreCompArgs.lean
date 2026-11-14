module

public import Silmaril.Compiler.C.Sem.TargetsCoreComp.Defs
public import Silmaril.Compiler.Core.Arguments.Defs
@[expose] public section

/-!
# core-comp's `compile_sound` at any enum registry and any program arguments

`Silmaril.Compile.C.Sem.TargetsCoreComp` states core-comp's specification as `Valid c_CoreX86`
on documents **without enum registry**, run with Cerberus's **default arguments**: `Core.beh`
starts the dynamics there, while `Spec.coreStart` starts it with the document's registry and
any `Spec.ArgsOk` arguments. With `Core.behWith` (`Silmaril/Compile/Core/Arguments.lean`) both
premises go:

* **Arguments.** `modelAt args` is core-comp's x86 model run with `args` (`CoreComp.model` is
  `modelAt Startup.execArguments`, by `rfl`); `Core.langAt args` is Core with its programs run
  with the same `args`; `c_SourceX86 args M` relates them by crt0's process reading, as
  `c_CoreX86` does. A statement holds for every `args` that `Spec.ArgsOk` accepts.
* **Enums.** Documents are elaborated to `Core.Source.ofDoc doc`: the file with its registry.
* **Route.** C semantics have no command line, so the route C → Core → x86 is stated at the
  default arguments, with the elaboration valid at `Core.cAS S` (`Core.cAC` for sources).

On a document without enum registry, at the default arguments, each statement is the frozen
statement of the same name without the suffix (`Core.ofDoc_beh_of_enumFree`).
-/

namespace Silmaril.Compile.C.Sem.CoreComp

open Silmaril.Compile.Category Silmaril.Compile.C.Sem.CoreX86 CategoryTheory

/-- **core-comp's x86 model run with `args`**: as `model`, with the loaded artifact's entry called
with `args` (`Spec.MachineBeh … args`). -/
def modelAt (args : List String) : X86Model :=
  { model with
    beh := fun a c => {o | Core.Spec.MachineBeh a c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 args o} }

/-- `model` is `modelAt` Cerberus's default arguments. -/
theorem modelAt_execArguments : modelAt Cerberus.Core.Startup.execArguments = model := rfl

/-- Core sources run with `args` to x86: a process agrees, or the target exhausted a resource
(`processMatch`, as `c_CoreX86`). -/
def c_SourceX86 (args : List String) (M : X86Model) : Core.langAt args ⟶ M.lang :=
  ⟨fun _ => PUnit.unit, processMatch M⟩

/-- `CoreX86.SoundSpec` for Core sources run with `args`. -/
def SoundSpecAt (args : List String) (M : X86Model) {Document : Type}
    (elaborate : Document → Core.Source) (compile : Document → Option M.Artifact) : Prop :=
  ∀ doc a, compile doc = some a → ∀ ctx, M.loaded a ctx →
    ∀ x, x ∈ M.beh a ctx → x ∈ allows M ((elaborate doc).beh args)

end Silmaril.Compile.C.Sem.CoreComp

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem
open Silmaril.Compile.C.Sem.CoreX86 Silmaril.Compile.C.Sem.CoreComp CategoryTheory

/-- core-comp's specification gives the abstract soundness of its model run with any accepted
arguments, on every document elaborated with its enum registry. -/
def core_comp_sound_spec_args : Prop :=
  ∀ compile : Cerberus.Codec.Document → Option Core.Spec.Artifact,
    Core.Spec.SoundSpec compile →
      ∀ args : List String, Core.Spec.ArgsOk args →
        SoundSpecAt args (modelAt args) Core.Source.ofDoc compile

/-- core-comp's `compile_sound` makes every accepted document, run with any accepted arguments
for which it has a Core behaviour, a valid compilation at `c_SourceX86 args (modelAt args)`. -/
def core_comp_compile_valid_args : Prop :=
  ∀ compile : Cerberus.Codec.Document → Option Core.Spec.Artifact,
    Core.Spec.SoundSpec compile →
      ∀ (args : List String), Core.Spec.ArgsOk args →
        ∀ (doc : Cerberus.Codec.Document) (a : Core.Spec.Artifact), compile doc = some a →
          ((Core.Source.ofDoc doc).beh args).Nonempty →
            Valid (c_SourceX86 args (modelAt args)) (Core.Source.ofDoc doc) a

/-- The route C → Core → x86 on documents with any enum registry: a C → Core elaboration valid
at `Core.cAS S`, followed by a compiler meeting core-comp's specification, is valid at
`c_Cx86 S` with core-comp's model. -/
def core_comp_route_valid_enums : Prop :=
  ∀ (S : Semantics) (compile : Cerberus.Codec.Document → Option Core.Spec.Artifact),
    Core.Spec.SoundSpec compile →
      ∀ (p : Cerberus.Ail.TypedProgram) (doc : Cerberus.Codec.Document) (a : Core.Spec.Artifact),
        Valid (Core.cAS S) p (Core.Source.ofDoc doc) → compile doc = some a →
          ((Core.Source.ofDoc doc).beh Cerberus.Core.Startup.execArguments).Nonempty →
            Valid (c_Cx86 S CoreComp.model) p a

end Silmaril.Compile.Targets
