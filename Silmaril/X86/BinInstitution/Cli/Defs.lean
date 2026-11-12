module

public import Silmaril.X86.BinInstitution.Defs
public import Silmaril.Cli.Institution.Defs

/-!
# Process sentences of the binary institution as CLI models (level `L1`)

A `ProcSen` of the binary institution (`Silmaril.X86.BinInstitution`) claims of every
process of an executable, started by an explicit `ProcLoader` with a fixed environment
(`ProcEnv`: argv, envp, auxv), that it ends with an exit status and stdout satisfying `post`.
It observes what the CLI level `L1` observes (stdout and the exit code); standard input is the
loader's business (the model's kernel delivers it), so a process template fixes it too.

* `ProcTmpl σ`: everything of a process sentence but the claim (loader, observation,
  executable, libraries, environment, imports' contracts), with the stdin its loader delivers.
* `ProcTmpl.sen T φ`: the `L1` sentence `φ` at the template's stdin, as a process sentence.
* `procModel C T`: the `L1` model of the template on the machine `C`: on the template's stdin,
  the ended states of finite runs (with the imports' contracts linked in) from every start the
  loader allows.

`Thms`: `procModel_sat` (a satisfied process sentence makes the model satisfy the CLI
sentence, when ended states stop) and `procModel_mono` (a model with fewer steps, a finer
ISA model, has fewer runs).
-/

@[expose] public section

namespace Silmaril.X86.BinInstitution

open Silmaril.X86 (Word Byte RelIsa)
open Silmaril.Cli.Institution (Level Out1)

variable {σ : Type}

/-- **A process template**: a process sentence without its claim, with the stdin its loader
delivers. -/
structure ProcTmpl (σ : Type) : Type where
  loader : ProcLoader σ
  obs : ProcObs σ
  exe : Silmaril.X86.Link.Blob
  libs : List (String × Silmaril.X86.Link.Blob)
  env : ProcEnv
  imports : Imports σ
  /-- The standard input the loader's kernel delivers. -/
  stdin : Silmaril.Cli.Bytes := []

/-- The `L1` observation of an ended process: its stdout and status. -/
def out1Of (e : Nat) (out : List Byte) : Out1 :=
  { stdout := out.map UInt8.ofBitVec, exit := UInt8.ofNat e }

/-- **An `L1` sentence as a process sentence** at the template's stdin. -/
def ProcTmpl.sen (T : ProcTmpl σ) (φ : Silmaril.Cli.Institution.Sen Level.stream.sig) : ProcSen σ :=
  { loader := T.loader, obs := T.obs, exe := T.exe, libs := T.libs, env := T.env,
    imports := T.imports, post := fun e out => φ T.stdin (out1Of e out) }

/-- One successful step of a machine. -/
def OkStep (C : RelIsa σ) (s t : σ) : Prop := C.step s (.ok t)

/-- **The `L1` model of a process template** on the machine `C`. -/
def procModel (C : RelIsa σ) (T : ProcTmpl σ) : Silmaril.Cli.Institution.Model Level.stream.sig :=
  ⟨fun s o => s = T.stdin ∧ ∃ r st u e out, T.loader.Starts T.exe T.libs T.env r st ∧ C.live st ∧
    r.Resolves T.imports ∧ Relation.ReflTransGen (OkStep (withImports C r T.imports)) st u ∧
    T.obs.ended u = some (e, out) ∧ o = out1Of e out⟩

/-- **Ended states stop**: on every load, an ended state's only outcome is `stop`. -/
def ProcTmpl.EndsStop (C : RelIsa σ) (T : ProcTmpl σ) : Prop :=
  ∀ r u, (T.obs.ended u).isSome → ∀ x, (withImports C r T.imports).step u x ↔ x = .stop

end Silmaril.X86.BinInstitution
