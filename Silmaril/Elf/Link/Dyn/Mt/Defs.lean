module

public import Silmaril.Elf.Link.Dyn.ProcX.Defs
public import Silmaril.Process.Mt.X86.Defs

/-!
# The dynamically linked process, multithreaded

`mtDyn W prims : UIsa Ghost` runs `ProcX.procX W` (the executable's image on `Sse9`, each
libc import one atomic contract step) **per thread**, on the shared memory and the shared
library ghost (`Proc.Ghost`), with trusted primitives bound at `prims` (address ↦ primitive
number, called as in `Mt.X86`: System V arguments, return to the address on the stack).

* at a primitive's entry point: a primitive call (`UOut.prim`);
* in the executable's image: the `ProcX` instruction step, as a plain step (`UOut.step`,
  access list unknown);
* elsewhere: the library's contract step of `Proc.extStep` (an import, the lazy resolver, the
  callback gate), as a library step (`UOut.lib`), for the calling thread; a `stop` outcome is
  a fault.

The library ending the process (`Ghost.done = some (status, _)`) ends the multithreaded
process (`UIsa.ended`). The library contracts of `Proc` are single-threaded: none of them
creates a thread, so a thread-creating library contract (`pthread_create`) is future work;
threads come from `MtCfg`'s initial table or from `Mt.X86` code that calls `clone`.

`Thms.must_mt`: a `ProcX` result (`Must`) holds of the one-thread process, when the run never
reaches a primitive's entry point.
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Mt

open Silmaril.X86 (Word)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Process (Memory)
open Silmaril.Process.Mt
open Silmaril.Process.Mt.X86 (Core PrimRet retAddr callArgs)
open Silmaril.Elf.Link.Dyn.Proc (World Ghost)
open Silmaril.Elf.Link.Dyn.ProcX (XPState)

/-- The `ProcX` state of a thread core, memory and ghost. -/
def toX (c : Core) (m : Memory) (g : Ghost) : XPState := ⟨⟨⟨c.core, m⟩, g⟩, c.xmm⟩

/-- A `ProcX` outcome as a thread action: in the image a plain step, elsewhere a library
step. -/
def out : Bool → Res XPState → UOut Core Ghost
  | true, .ok s => .step ⟨s.p.m.core, s.x⟩ none s.p.m.memory
  | false, .ok s => .lib ⟨s.p.m.core, s.x⟩ s.p.m.memory s.p.g
  | _, .stop => .stop

/-- **What thread `t` does next.** -/
def step (W : World) (prims : List (Word × Nat)) (_t : Nat) (c : Core) (m : Memory) (g : Ghost)
    (o : UOut Core Ghost) : Prop :=
  match prims.find? (·.1 == c.core.rip) with
  | some (_, p) =>
    match retAddr c.core m with
    | some ra => ∃ k, (∀ w, PrimRet c.core ra w (k w)) ∧ o = .prim p (callArgs c.core) k
    | none => o = .stop
  | none => ∃ r, ProcX.step W (toX c m g) r ∧ o = out (decide (W.InImage c.core.rip.toNat)) r

/-- **The multithreaded dynamically linked process's user ISA.** -/
@[reducible] def mtDyn (W : World) (prims : List (Word × Nat)) : UIsa Ghost where
  St := Core
  step := step W prims
  ended g := g.done.map (·.1)

end Silmaril.Elf.Link.Dyn.Mt
