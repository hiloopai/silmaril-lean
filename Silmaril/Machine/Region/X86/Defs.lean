module

public import Silmaril.Machine.Region.Defs
public import Silmaril.Machine.Region.X86.CFG.Defs

/-! # x86 region candidates and the existing Ext machine

The machine is the repository's handwritten `X86.Ext`, not a claim about all
x86 or hardware. Every retirement is a real step, including calls/returns;
there is no synthetic call fallthrough. All non-retirement outcomes are
separate halts (a returned outcome carries its final state). No syscall
instruction is present in Ext, so this adapter's event alphabet is Empty.
Unknown instructions stop as `undecodable`, rather than becoming an invented
edge. `instructionTargets` is deliberately Top for calls and returns.
-/

@[expose] public section
namespace Silmaril.Machine.Region.X86
open Silmaril.Semantics.Region
open Silmaril.X86 (MState Word)
open Silmaril.X86.Decompile

/-- Exact re-use of Ext.step, with its explicit designated return address. -/
def system (returnAddress : Word) : TransitionSystem MState Nat Empty Silmaril.X86.Ext.Outcome where
  pc s := s.core.rip.toNat
  step s es t := es = [] ∧ Silmaril.X86.Ext.step returnAddress s = .retired t
  halt s k := Silmaril.X86.Ext.step returnAddress s = k ∧ ∀ t, k ≠ .retired t

/-- Normal successor overapproximation for the supported decoded subset.
Calls/returns require state-dependent targets or summaries; Top preserves that
uncertainty. UD2 has no normal successor but remains a distinguished halt. -/
def instructionTargets (d : Decoded) : Targets Nat :=
  if interprocedural d.instr then .top else .finite (d.edges.filterMap edgeTarget).toFinset

/-- Ordered decoded instructions are kept separate from extensional support. -/
structure Candidate where
  listing : List Decoded
  entry : Nat
  allowance : Targets Nat

/-- Collect targets extensionally, with no enumeration of a Finset. -/
def collect : List (Targets Nat) → Targets Nat
  | [] => .finite ∅
  | .top :: _ => .top
  | .finite xs :: rest => match collect rest with
    | .top => .top
    | .finite ys => .finite (xs ∪ ys)

/-- An external heuristic may choose the listing; this function only unions
outward targets of that listing. It is not a certificate of decoding or entry. -/
def propose (listing : List Decoded) (entry : Nat) : Candidate :=
  let support := (listing.map Decoded.addr).toFinset
  let allowance := match collect (listing.map instructionTargets) with
    | .top => .top
    | .finite xs => .finite (xs.filter fun l => l ∉ support)
  ⟨listing, entry, allowance⟩

/-- Support of an arbitrary collection of half-open virtual-address ranges. -/
def labels (support : Finset Range) (l : Nat) : Prop := ∃ s ∈ support, s.Contains l

/-- Fixed interface includes all initial-state assumptions. Changing it may
change both the admitted domain and return handling; weakening only applies
when the transition system stays fixed. -/
structure Interface where
  returnAddress : Word
  admit : Nat → MState → Prop
  wellFormed : Nat → Prop

/-- Greatest sound rows for this exact operational context. -/
def greatestRows (iface : Interface) : Finset Range → Nat → Finset Nat → Prop :=
  greatest (system iface.returnAddress) iface.wellFormed iface.admit labels

end Silmaril.Machine.Region.X86
