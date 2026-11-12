module

public import Silmaril.Elf.Link.Dyn.LibMod.Defs
public import Silmaril.Elf.Link.Dyn.Program.Defs

/-!
# A program on the C-runtime machine, and the obligations of its C library

The Program API states a C program's claim on the process model (`Program.Verified`: every run
of `Proc.proc` from every documented start ends with `spec w`). This module states the same claim
on the **C-runtime machine** of a library module (`VerifiedCrt Mod`: `LibMod.crt`, the library's
steps relaxed by the scratch stack, the client stopped on any write to the library's memory),
and the obligations that make it a claim about **real execution** (`RealVerified`):

* `Task.crtInit`: **initialisation**. Every real start state of world `w` (the ELF loaded by
  ld.so with libc.so.6 and ld.so, the kernel's initial stack with `argv`, `envp` and `auxv`)
  represents a documented start of the process model (`ExeLoaded`, `Placed`, `AtStart`) in the
  module's invariant, with the kernel having observed nothing (`Rel`);
* `Task.crtGate`, `Task.crtStartMain`, `Task.crtCxaFinalize`, `Task.crtNamed n off`:
  **realisation**, one per library entry point the process world binds: the code at the
  address realises its relaxed atomic step (`LibMod.Realises`). The gate is the library's code
  between callbacks (`__libc_start_main` calling the initialisers and `main`, `exit` calling
  the handlers and finalisers, flushing and `_exit`).

`Thms.realVerified_of`: `VerifiedCrt` and those Tasks give `RealVerified`, by `LibMod.crt_sound`;
the client steps (the C runtime's `_start`, the initialisers, `main`) are proved once there.
`Thms.VerifiedCrt.verified`: the C-runtime claim implies the process-model claim, so it is at
least as strong as `Program.Verified`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.LibMod

open Silmaril.X86 (Word)
open Silmaril.X86.Link (Blob)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Elf.Link.Dyn.Proc (PState)
open Silmaril.Elf.Link.Dyn.Program (Bin LibPin Spec Tier LibTable Std World Placed AtStart Observed world lib)

/-- A library module for each stdio environment and load base of `libc.so.6`. -/
abbrev Mod := Std → Word → LibModule

/-- **The claim on the C-runtime machine** (`Program.Verified` with `crt` for `proc`). -/
def VerifiedCrt (M : Mod) (B : Bin) (libc ld : LibPin) (spec : Spec) (tier : Tier) (L : LibTable := lib)
    (env : Std → Prop := fun _ => True) : Prop :=
  ∀ w, tier w → ∀ (Fc Fl : Blob), ChunksOf Fc libc.chunks → ChunksOf Fl ld.chunks →
  ∀ (S : Std), S.E.fs = w.fs → env S →
  ∀ (b lb ldb res gate : Word) (ifn : Word → Option Word) (args : Nat → Prop) (s : PState),
    Dyn.ExeLoaded [B.file, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory →
    Placed B b lb gate →
    AtStart B (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L) w b s →
    MustC (M S lb) (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L) (Observed (spec w)) s

/-- **Open (per C library): initialisation** (module doc). `start w c`: `c` is a real start state
of world `w`. -/
def Task.crtInit (X : Real) (M : Mod) (B : Bin) (libc ld : LibPin) (L : LibTable) (env : Std → Prop)
    (start : World → X.τ → Prop) : Prop :=
  ∀ w c, start w c → ∃ (Fc Fl : Blob) (S : Std) (b lb ldb res gate : Word) (ifn : Word → Option Word)
    (args : Nat → Prop) (s : PState),
    ChunksOf Fc libc.chunks ∧ ChunksOf Fl ld.chunks ∧ S.E.fs = w.fs ∧ env S ∧
    Dyn.ExeLoaded [B.file, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory ∧ Placed B b lb gate ∧
    AtStart B (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L) w b s ∧
    Rel X (M S lb) c s

/-- The process world of a run, as the realisation Tasks quantify over it. -/
abbrev runWorld (B : Bin) (L : LibTable) (S : Std) (w : World) (b lb gate : Word) (args : Nat → Prop)
    (fs : Word) : Proc.World :=
  world B S w b lb gate (!w.stdoutFull) args fs L

/-- **Open (per C library): the callback gate** realises `Proc.gateStep` (relaxed). -/
def Task.crtGate (X : Real) (M : Mod) (B : Bin) (L : LibTable) : Prop :=
  ∀ S w b lb gate args fs, Placed B b lb gate →
    Realises X (M S lb) (relax (runWorld B L S w b lb gate args fs)
      (Proc.gateStep (runWorld B L S w b lb gate args fs))) gate

/-- **Open (per C library): `__libc_start_main`** realises `Proc.startMainStep` (relaxed). -/
def Task.crtStartMain (X : Real) (M : Mod) (B : Bin) (L : LibTable) : Prop :=
  ∀ S w b lb gate args fs, Placed B b lb gate →
    Realises X (M S lb) (relax (runWorld B L S w b lb gate args fs)
      (Proc.fnStep (runWorld B L S w b lb gate args fs) .libcStartMain)) (lb + BitVec.ofNat 64 B.lsmOff)

/-- **Open (per C library): `__cxa_finalize`** realises `Proc.cxaFinalizeStep` (relaxed). -/
def Task.crtCxaFinalize (X : Real) (M : Mod) (B : Bin) (L : LibTable) : Prop :=
  ∀ S w b lb gate args fs, Placed B b lb gate →
    Realises X (M S lb) (relax (runWorld B L S w b lb gate args fs)
      (Proc.fnStep (runWorld B L S w b lb gate args fs) .cxaFinalize)) (lb + BitVec.ofNat 64 B.cxaOff)

/-- **Open (per C library and symbol): the import `n`** at offset `off` realises its contract in
the table `L` (relaxed). -/
def Task.crtNamed (X : Real) (M : Mod) (B : Bin) (L : LibTable) (n : Name) (off : Nat) : Prop :=
  ∀ S w b lb gate args fs, Placed B b lb gate →
    Realises X (M S lb) (relax (runWorld B L S w b lb gate args fs)
      (Proc.fnStep (runWorld B L S w b lb gate args fs) (.named n))) (lb + BitVec.ofNat 64 off)

/-- **The claim about real execution**: from every real start state of a world of the tier, the
real machine runs to a state representing an ended process whose outcome is `spec w` (the kernel
observed its stdout, stderr and exit status). -/
def RealVerified (X : Real) (M : Mod) (spec : Spec) (tier : Tier) (start : World → X.τ → Prop) :
    Prop :=
  ∀ w, tier w → ∀ c, start w c → ∃ c', Reaches X.J.step c c' ∧
    ∃ (S : Std) (lb : Word) (a : PState), Rel X (M S lb) c' a ∧ Observed (spec w) a

end Silmaril.Elf.Link.Dyn.LibMod
