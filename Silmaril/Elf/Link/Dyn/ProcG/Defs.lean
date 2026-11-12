module

public import Silmaril.Elf.Link.Dyn.Proc.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Extends.Defs

/-! # The process machine over a larger image ISA

`Proc.proc W` runs the executable's image with `Open9`, which stops on instructions it does
not decode (SSE moves, for instance). `procG L W` is the same process with the image run by
any machine `J` that extends `Open9` (`L : Open9.isa.Extends J`), such as a machine with
vector registers. A `J` state has an `MState` view (`L.view`); the rest (vector registers) is
a frame the `Open9` steps do not touch.

Library steps act on the view, as in `proc`; the frame after a library call is arbitrary (the
System V ABI lets a callee clobber every vector register). `Proc.proc` is unchanged: this
module is additive, and `ProcG.Thms.must_lift` moves every `MustQ` result over `proc W` to
`procG L W`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.ProcG

open Silmaril.X86 (MState State)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Elf.Link.Dyn.Proc

/-- A process state whose image machine has states `τ`. -/
structure GState (τ : Type) where
  x : τ
  g : Ghost

variable {τ : Type} {J : Isa τ}

/-- The `PState` a process state shows (its `MState` view and the ghost). -/
def GState.view (L : Silmaril.X86.Open9.isa.Extends J) (s : GState τ) : PState := ⟨L.view s.x, s.g⟩

/-- **One step of the extended process.** In the image, `J`; elsewhere, the library on the
view, with an arbitrary frame afterwards. -/
def stepG (L : Silmaril.X86.Open9.isa.Extends J) (W : World) (s : GState τ) (r : Res (GState τ)) : Prop :=
  match s.g.done with
  | some _ => r = .stop
  | none =>
    if W.InImage (L.view s.x).core.rip.toNat then
      match J.step s.x with
      | some x' => r = .ok ⟨x', s.g⟩
      | none => r = .stop
    else match r with
      | .stop => extStep W (s.view L) .stop
      | .ok y => ∃ t, extStep W (s.view L) (.ok t) ∧ L.view y.x = t.m ∧ y.g = t.g

/-- **The extended process machine.** -/
def procG (L : Silmaril.X86.Open9.isa.Extends J) (W : World) : Silmaril.X86.RelIsa (GState τ) where
  core s := J.core s.x
  mem s := J.mem s.x
  upd s c m := { s with x := J.upd s.x c m }
  core_upd _ _ _ := J.core_upd _ _ _
  mem_upd _ _ _ := J.mem_upd _ _ _
  upd_self s := by cases s; simp [J.upd_self]
  live _ := True
  step := stepG L W
  live_step _ _ := trivial

end Silmaril.Elf.Link.Dyn.ProcG
