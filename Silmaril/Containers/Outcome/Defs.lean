module

public import Silmaril.Containers.Behaviour.Defs

/-! # Experimental outcome variants

The current tagged `Stop` stays intact. This finite-outcome variant permits a reason type
`UB`, `Unit` or `Empty` and adds a defined guest trap, separate from host UB. The approximation
order intentionally identifies all UB reasons as a single top; this differs from equality
and from set/trace inclusion. -/

@[expose] public section
namespace Silmaril.Containers

inductive Outcome (U : Type) where
  | exited (code : UInt8)
  | signaled (signal : Nat)
  | killed (reason : Kill)
  | refused (reason : Refusal)
  | trapped (code : Nat)
  | undefined (reason : U)
  deriving DecidableEq, Repr

namespace Outcome
variable {U V : Type}

def ofStop : Stop → Outcome UB
  | .exited c => .exited c
  | .signaled s => .signaled s
  | .killed k => .killed k
  | .refused r => .refused r
  | .undefined u => .undefined u

def mapUB (f : U → V) : Outcome U → Outcome V
  | .exited c => .exited c
  | .signaled s => .signaled s
  | .killed k => .killed k
  | .refused r => .refused r
  | .trapped t => .trapped t
  | .undefined u => .undefined (f u)

def NoUB : Outcome U → Prop
  | .undefined _ => False
  | _ => True

def erase (s : Outcome U) : Outcome Unit := s.mapUB fun _ => ()

/-- Eliminating the UB constructor requires a noUB proof; no reasons can be fabricated from
`Empty`. This is a representation change, not an assumption that the execution is safe. -/
def toEmpty : (s : Outcome U) → s.NoUB → Outcome Empty
  | .exited c, _ => .exited c
  | .signaled sig, _ => .signaled sig
  | .killed k, _ => .killed k
  | .refused r, _ => .refused r
  | .trapped t, _ => .trapped t
  | .undefined _, h => False.elim h

/-- UB is top by explicit choice; a defined signal is below UB, never conversely. -/
def Approx (a b : Outcome U) : Prop := a = b ∨ ∃ u, b = .undefined u

/-- The optional **more UB** policy: guest traps become host-model UB. -/
def trapAsUB (reason : U) : Outcome U → Outcome U
  | .trapped _ => .undefined reason
  | s => s

/-- A masking policy, useful as a semantic implementation of UB but unsafe for transferring
noUB certificates from the result back to its source. -/
def ubToCrash (signal : Nat) : Outcome U → Outcome U
  | .undefined _ => .signaled signal
  | s => s

end Outcome
end Silmaril.Containers
