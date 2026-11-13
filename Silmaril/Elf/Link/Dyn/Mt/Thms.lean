module

public import Silmaril.Elf.Link.Dyn.Mt.Defs
public import Silmaril.Process.Mt.Thms
import Silmaril.Proofs.Elf.Link.Dyn.Mt

/-!
# The dynamically linked process, multithreaded: single-threaded results transfer

PROVED (standard axioms; proofs in `Silmaril.Proofs.Elf.Link.Dyn.Mt`):

* `noThreadSys`: `mtDyn` never makes a system call (so never `clone` or `futex`);
* **`must_mt`**: a demonic result of the single-threaded process with XMM registers
  (`RelIsa.Must (ProcX.procX W) R Q`), from a state whose run never reaches a primitive's entry
  point (`R`-states are away from `prims`), holds of the one-thread multithreaded process
  under SC, with any primitive table and base relation: every run of `MtStep (mtDyn W prims)`
  from the one-thread configuration avoids faults, terminates and reaches a configuration
  that is a single-threaded state satisfying `Q`.

So every `ProcX` theorem (and, by `ProcX.mustX_of_must`, every `Proc` theorem) carries over to
the multithreaded model unchanged.
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Mt

open Silmaril.X86 (Word)
open Silmaril.X86.RelIsa (Must)
open Silmaril.Process (Memory)
open Silmaril.Process.Mt
open Silmaril.Process.Mt.X86 (Core)
open Silmaril.Elf.Link.Dyn.Proc (World Ghost)
open Silmaril.Elf.Link.Dyn.ProcX (XPState procX)

variable {W : World} {prims : List (Word × Nat)} {P : PrimTable Ghost} {base : Base Ghost} {tid : Nat}

theorem noThreadSys (x : SoloCfg Core Ghost) : NoThreadSys (mtDyn W prims) tid x :=
  Silmaril.Proofs.Elf.Link.Dyn.Mt.noThreadSys x

/-- **`ProcX` results transfer to the one-thread multithreaded process.** -/
theorem must_mt {R Q : XPState → Prop} {c : Core} {m : Memory} {g : Ghost}
    (h : Must (procX W) R Q (toX c m g))
    (hR : ∀ s, R s → prims.find? (·.1 == s.p.m.core.rip) = none) :
    SMust (MtStep (mtDyn W prims) sc P base) (MtFault (mtDyn W prims) sc P)
      (fun C => ∃ y : SoloCfg Core Ghost, SoloRel tid y C ∧ Q (toX y.st y.mem y.g))
      (MtCfg.init (S := sc.S) tid c m g) :=
  Silmaril.Proofs.Elf.Link.Dyn.Mt.must_mt h hR

end Silmaril.Elf.Link.Dyn.Mt
