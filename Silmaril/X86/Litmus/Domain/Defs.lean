module

public import Silmaril.X86.Litmus.Extract.Defs

/-!
# How extracted traces depend on the value domain: definitions

The litmus extractor (`Litmus.extract`) branches at every read over a finite value domain. This
module
fixes the vocabulary for comparing the trace sets of two domains, used by the domain-closure
theorem (`Silmaril.X86.MemoryModel.Litmus.Closure`):

* `InDom dom bs`: the bytes `bs` encode a value of `dom` (at their own length);
  `Act.ReadIn`, `StepRec.ReadsIn`: every read of an action or a step returns such bytes.
* **Straight-line code** (`straightForm`, `Thread.skelFrom`): every instruction from `rip` to the
  end of the code is a fence, `mov r32, imm32`, or one of the extractor's memory forms with an
  absolute operand (no base register, no index, not `rip`-relative), and execution falls
  through to the next instruction. On such code the **skeleton** of every trace (the events
  of each step: kind, address, size, `locked`) is the same whatever the domain and whatever the
  values read (`explore_skel` in `Domain/Thms.lean`); only the bytes differ. All 60
  x86-TSO-covered corpus tests are straight-line code (checked by `decide` in the closure
  module).
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State Word Byte)
open Silmaril.X86.Ext (Mem)
open MemEvent (Event)

/-! ## Reads inside a domain -/

/-- The bytes encode a value of the domain at their own length. -/
def InDom (dom : List Nat) (bs : List Byte) : Prop := ∃ v ∈ dom, valBytes v bs.length = bs

instance (dom : List Nat) (bs : List Byte) : Decidable (InDom dom bs) :=
  inferInstanceAs (Decidable (∃ v ∈ dom, valBytes v bs.length = bs))

/-- If the action reads, it reads bytes of a value of the domain. -/
def Act.ReadIn (dom : List Nat) (a : Act) : Prop := a.ev.kind.reads = true → InDom dom a.rd

/-- Every read of the step reads bytes of a value of the domain. -/
def StepRec.ReadsIn (dom : List Nat) (r : StepRec) : Prop := ∀ a ∈ r.acts, a.ReadIn dom

/-! ## Straight-line code -/

/-- An absolute memory operand `[disp32]`: no base register, no index (so the address depends on
neither the registers nor `rip`). -/
def Mem.isAbs (a : Ext.Mem) : Bool :=
  (match a.base with
   | .none => true
   | _ => false) && a.index.isNone

/-- The **straight-line forms**: fences, `mov r32, imm32`, and the memory forms of the
extractor (`memStep`) with an absolute operand. Each falls through to the next instruction and
has events that do not depend on the core (`straight_events`). -/
def straightForm : Atomic9.Instr → Bool
  | .new (.fence _) => true
  | .open9 (.ext8 (.base (.movI32 _ _))) => true
  | .open9 (.ext8 (.base (.mov _ (.mem a) _))) => Mem.isAbs a
  | .open9 (.ext8 (.base (.movI _ (.mem a) _))) => Mem.isAbs a
  | .open9 (.ext8 (.base (.load _ _ a))) => Mem.isAbs a
  | .new (.xadd _ _ (.mem a) _) => Mem.isAbs a
  | .new (.xchg _ (.mem a) _) => Mem.isAbs a
  | .new (.cmpxchg _ _ (.mem a) _) => Mem.isAbs a
  | .open9 (.ext8 (.base (.mov8 _ (.mem a)))) => Mem.isAbs a
  | .open9 (.ext8 (.base (.movI8 (.mem a) _))) => Mem.isAbs a
  | .open9 (.ext8 (.base (.incdec _ _ (.mem a)))) => Mem.isAbs a
  | .new (.lockIncDec _ _ a) => Mem.isAbs a
  | .new (.lockAluI _ op a _) => (op != .cmp) && Mem.isAbs a
  | _ => false

/-- The skeleton of the straight-line code from `rip`: the events of each instruction until
the end of the code, or `none` if some instruction is not decoded, not a straight-line form, or
`fuel` runs out. The events are computed in the core `t.init` with `rip` replaced (they do not
depend on the rest of the core). -/
def Thread.skelFrom (t : Thread) : Nat → Word → Option (List (List Event))
  | fuel, rip =>
    if rip = t.endRip then some []
    else
      match fuel with
      | 0 => none
      | f + 1 =>
        match t.fetch { t.init with rip } with
        | some (i, n) =>
          if straightForm i then
            (t.skelFrom f (rip + BitVec.ofNat 64 n)).map
              (MemEvent.atomic9Accesses i { t.init with rip } n :: ·)
          else none
        | none => none

/-- The skeleton of the thread from its initial core, step by step. -/
def Thread.skel (t : Thread) (fuel : Nat) : Option (List (List Event)) :=
  t.skelFrom fuel t.init.rip

end Silmaril.X86.Litmus
