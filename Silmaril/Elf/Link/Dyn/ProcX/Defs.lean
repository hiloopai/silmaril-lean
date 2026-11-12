module

public import Silmaril.Elf.Link.Dyn.Proc.Defs
public import Silmaril.X86.Sse9.Defs

/-! # The process machine with XMM registers

`Proc.proc W` runs the executable's image on `Open9`, which has no XMM registers: at an SSE
instruction (`movdqa`, `movups`, `pxor`, …) it stops. `procX W` is the same process with
the sixteen XMM registers (`Silmaril.X86.Sse9.XFile`):

* in the image, the machine is silmaril's `Sse9.step` (`Open9.step` with the XMM registers
  unchanged; on bytes neither `Ext8` nor `Ext9` decodes, an SSE data-movement form);
* outside it, the library's contracts of `Proc.extStep`, unchanged; the library leaves the
  XMM registers arbitrary (all of them are caller-saved in the System V ABI), so a library
  step may set them to anything.

`ProcX.mustX_of_must` (in `Thms.lean`) carries every `Proc.MustQ` result over to `procX`, so
the integer-only proofs about `proc` are not redone; `mustX_sse` steps an SSE instruction
against `Sse9.exec`.

**Trusted** in addition to `Proc`'s assumptions: silmaril's `Sse9` semantics of the SSE
forms (`Sse9.exec`), and the claim that the library's steps change only what `Proc`'s
contracts say plus the XMM registers.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.ProcX

open Silmaril.X86 (Word MState)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Elf.Link.Dyn.Proc

/-- A process state with the XMM registers. -/
structure XPState where
  p : PState
  x : Silmaril.X86.Sse9.XFile

/-- A library outcome, with whatever XMM registers the library leaves. -/
def havoc : Res PState → Res XPState → Prop
  | .ok t, .ok u => u.p = t
  | .stop, .stop => True
  | _, _ => False

/-- **One step of the process with XMM registers.** -/
def step (W : World) (s : XPState) (r : Res XPState) : Prop :=
  match s.p.g.done with
  | some _ => r = .stop
  | none =>
    if W.InImage s.p.m.core.rip.toNat then
      match Silmaril.X86.Sse9.step ⟨s.p.m, s.x⟩ with
      | some y => r = .ok ⟨⟨y.m, s.p.g⟩, y.xmm⟩
      | none => r = .stop
    else ∃ r', extStep W s.p r' ∧ havoc r' r

/-- **The process machine with XMM registers.** -/
def procX (W : World) : Silmaril.X86.RelIsa XPState where
  core s := s.p.m.core
  mem s := s.p.m.memory
  upd s c m := ⟨⟨⟨c, m⟩, s.p.g⟩, s.x⟩
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  live _ := True
  step := step W
  live_step _ _ := trivial

/-- The process with XMM registers must reach `Q`. -/
abbrev MustX (W : World) (Q : XPState → Prop) (s : XPState) : Prop :=
  Silmaril.X86.RelIsa.Must (procX W) (fun _ => True) Q s

end Silmaril.Elf.Link.Dyn.ProcX
