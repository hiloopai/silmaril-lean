module

public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Compiler.C.Sem.CoreX86.Defs
@[expose] public section

/-!
# core-comp's `compile_sound` as `Valid c_CoreX86`: the concrete x86 model

`Silmaril.Compile.C.Sem.CoreX86` states the Core → x86 route against an abstract `X86Model`.
This file instantiates it with core-comp's own frozen specification
(`Silmaril/Compile/Core/Spec.lean`): its artifacts, the loader contexts of `Spec.Loaded`, the
machine behaviours `Spec.MachineBeh` observed through crt0 (`Spec.observe`), and the process
reading of those observations. The statements below say that core-comp's `SoundSpec` gives
the abstract `CoreX86.SoundSpec` and `Valid (c_CoreX86 coreComp)` on the programs where csem's
`Core.beh` and core-comp's `Spec.Allowed` speak about the same run:

* **Arguments.** `Spec.SoundSpec` quantifies over every argument list; `Core.beh` runs `main`
  with Cerberus's default `Startup.execArguments` (`["cmdname"]`). The model's behaviours are
  the machine's for those arguments.
* **Enums.** `Spec.coreStart` starts the dynamics with the document's enum registry;
  `Core.beh` starts it with the empty one. The statements require `doc.enumBindings.getD [] = []`
  (`EnumFree`).
* **Observations.** `exit k out` is `⟨out, status k⟩`, `abort out` is `⟨out, signal 6⟩`, a trap is
  signal 4 (`SIGILL`), a fault signal 11 (`SIGSEGV`), divergence `⟨[], diverges⟩`; only
  exhaustion is `none` (`CoreX86.X86Model.process`).
* **Exhaustion.** `Spec.Allowed` allows it unconditionally; `Valid` needs a source behaviour
  for it (`CoreX86.core_x86_valid_iff`), hence the premise `(Core.beh doc.file).Nonempty`.

`compile` is any function with core-comp's specification: these statements import no compiler
and assert nothing about one that is not proved to meet `Spec.SoundSpec`.
-/

namespace Silmaril.Compile.C.Sem.CoreComp

open Silmaril.Cerberus
open Silmaril.X86 (Word Reg)
open Silmaril.X86.Backend (Space)

/-- A loader context of core-comp's specification: the address space, the return address of the
entry function, the initial stack pointer, the callee-saved registers and the initial machine
state (the arguments of `Spec.Loaded` and `Spec.MachineBeh`). -/
abbrev Context : Type := Space × Word × Nat × (Reg → Word) × X86.State

/-- crt0's observations as process observations; resource exhaustion is `none`. -/
def process : Core.Spec.Obs → Option Obs
  | .exit k out => some ⟨out, .status k⟩
  | .abort out => some ⟨out, .signal 6⟩
  | .trap out => some ⟨out, .signal 4⟩
  | .fault out => some ⟨out, .signal 11⟩
  | .diverges => some ⟨[], .diverges⟩
  | .exhausted => none

/-- **core-comp's x86 model**: its artifacts, loaded by the trusted loader in any context
(`Spec.Loaded`), run on `X86.Ext` with Cerberus's default arguments and observed by crt0
(`Spec.MachineBeh`). -/
def model : CoreX86.X86Model where
  Artifact := Core.Spec.Artifact
  Context := Context
  Observation := Core.Spec.Obs
  loaded a c := Core.Spec.Loaded a c.1 c.2.1 c.2.2.1
  beh a c := {o | Core.Spec.MachineBeh a c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
    (Core.Startup.execArguments) o}
  process := process

/-- Core documents whose enum registry is empty: on them `Spec.coreStart` (with the default
arguments) is the start of `Core.beh`. -/
def EnumFree : Type := {doc : Codec.Document // doc.enumBindings.getD [] = []}

end Silmaril.Compile.C.Sem.CoreComp

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem
open Silmaril.Compile.C.Sem.CoreX86 Silmaril.Compile.C.Sem.CoreComp CategoryTheory

/-- core-comp's specification gives the abstract `CoreX86.SoundSpec` of its model, on documents
without enum registry, elaborated to their Core file. -/
def core_comp_sound_spec : Prop :=
  ∀ compile : Cerberus.Codec.Document → Option Core.Spec.Artifact,
    Core.Spec.SoundSpec compile →
      CoreX86.SoundSpec CoreComp.model (fun d : EnumFree => d.1.file) (fun d => compile d.1)

/-- **Milestone (b).** core-comp's `compile_sound` makes every accepted document with a Core
behaviour (and no enum registry) a valid compilation at `c_CoreX86` of core-comp's x86 model. -/
def core_comp_compile_valid : Prop :=
  ∀ compile : Cerberus.Codec.Document → Option Core.Spec.Artifact,
    Core.Spec.SoundSpec compile →
      ∀ (doc : Cerberus.Codec.Document) (a : Core.Spec.Artifact), compile doc = some a →
        doc.enumBindings.getD [] = [] → (Core.beh doc.file).Nonempty →
          Valid (c_CoreX86 CoreComp.model) doc.file a

/-- The route C → Core → x86: a C → Core elaboration valid at `Core.cAC S`, followed by a
compiler meeting core-comp's specification, is valid at `c_Cx86 S` with core-comp's model. -/
def core_comp_route_valid : Prop :=
  ∀ (S : Semantics) (compile : Cerberus.Codec.Document → Option Core.Spec.Artifact),
    Core.Spec.SoundSpec compile →
      ∀ (p : Cerberus.Ail.TypedProgram) (doc : Cerberus.Codec.Document) (a : Core.Spec.Artifact),
        Valid (Core.cAC S) p doc.file → compile doc = some a →
          doc.enumBindings.getD [] = [] → (Core.beh doc.file).Nonempty →
            Valid (c_Cx86 S CoreComp.model) p a

end Silmaril.Compile.Targets
