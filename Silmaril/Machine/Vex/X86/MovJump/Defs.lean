module

public import Silmaril.Machine.Vex.X86.Defs
public import Silmaril.Machine.Region.X86.Defs
public import Silmaril.Semantics.Region.Simulation.Defs

/-! # MOV/JMP: projected scalar instructions and loaded x86 boundaries -/

@[expose] public section

namespace Silmaril.Machine.Vex.AMD64Scalar.MovJump

open Silmaril.Semantics.Region
open Silmaril.X86 (MState)
open Silmaril.X86.Decompile (Decoded)
open Silmaril.X86.Ext (Instr encode)

structure Fragment where
  base : Word
  displacement : BitVec 8

def mov : Instr := .mov .q (.reg .rax) .rdi

def Fragment.code (fragment : Fragment) : Silmaril.X86.Decompile.Region :=
  ⟨fragment.base.toNat, encode mov ++ encode (.jmp8 fragment.displacement)⟩

def Fragment.bytes (fragment : Fragment) : List UInt8 :=
  fragment.code.bytes.map fun byte => UInt8.ofNat byte.toNat

def Fragment.jumpPC (fragment : Fragment) : Word := fragment.base + 3

def Fragment.target (fragment : Fragment) : Word := fragment.jumpPC + 2 + fragment.displacement.signExtend 64

def Fragment.support (fragment : Fragment) (pc : Nat) : Prop :=
  pc = fragment.base.toNat ∨ pc = fragment.jumpPC.toNat

/-- The five instruction bytes do not wrap, and the jump leaves this cut.
No execution permission or supplied bytes are required at the boundary. -/
structure Fragment.Guard (fragment : Fragment) : Prop where
  noWrap : fragment.base.toNat + 5 < 2^64
  leaves : ¬ fragment.support fragment.target.toNat

def Fragment.listing (fragment : Fragment) : List Decoded :=
  [⟨fragment.base.toNat, mov, 3⟩, ⟨fragment.base.toNat + 3, .jmp8 fragment.displacement, 2⟩]

def Fragment.block (fragment : Fragment) : X86.Block :=
  ⟨[.movRdiToRax], .jmp fragment.target, [⟨fragment.base, 3⟩, ⟨fragment.jumpPC, 2⟩]⟩

def advance (input : Input) : Input :=
  { X86.Op.step X86.concrete input .movRdiToRax with rip := input.rip + 3 }

def Fragment.step? (fragment : Fragment) (input : Input) : Option Input :=
  if input.rip = fragment.base then some (advance input)
  else if input.rip = fragment.jumpPC then some { input with rip := fragment.target }
  else none

/-- This model describes a region only. Outside its two instruction starts it
has no transition, rather than an invented UB outcome. -/
def Fragment.simple (fragment : Fragment) : TransitionSystem Input Nat Empty Empty where
  pc := fun state => state.rip.toNat
  step := fun state es next => es = [] ∧ fragment.step? state = some next
  halt := fun _ stop => nomatch stop

/-- A scalar entry and its demonic partial WP. The guard and the totality
proof are separate: non-UB and a partial WP alone do not rule out a loop. -/
def Fragment.entryWP (fragment : Fragment) (Q : Nat → List Empty → Input → Prop) (input : Input) : Prop :=
  input.rip = fragment.base ∧ wp fragment.simple fragment.support Q (fun _ _ _ => False) input

/-- MOV and JMP do not read flags, so either completion of an undefined ZF is
admitted. For defined ZF, this projection reads its actual Boolean value. -/
def project (undefinedZF : Bool) (state : MState) : Input :=
  ⟨state.core.read .rax, state.core.read .rdi, state.core.read .rsi,
    state.core.flags.zero.getD undefinedZF, state.core.rip⟩

/-- The loading invariant is independent of the architectural projection.
It uses checked executable bytes from the existing process-memory model. -/
def Fragment.Related (fragment : Fragment) (undefinedZF : Bool) (small : Input) (full : MState) : Prop :=
  small = project undefinedZF full ∧ fragment.code.LoadedIn full.memory

end Silmaril.Machine.Vex.AMD64Scalar.MovJump
