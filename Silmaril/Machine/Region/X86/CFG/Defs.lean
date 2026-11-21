module

public import Silmaril.X86.Decompile.Edges

/-! # Intrinsic direct-transfer CFG rows

A byte/decoder relation, with no execution, memory, graph-partition or function
extraction premise. Vertices are instruction starts, not every covered byte.
Edges and declared outward labels are extensional; list order is irrelevant.
These finite syntax certificates decorate, rather than constrain, the abstract
region-model lattice. Calls and returns are rejected by this direct subset.
-/

@[expose] public section
namespace Silmaril.Machine.Region.X86
open Silmaril.X86.Decompile

/-- Named target of an existing decoder edge. This does not justify a synthetic
call resumption; the direct CFG subset excludes calls and returns. -/
def edgeTarget : Edge → Option Nat
  | .fallthrough t | .jump t | .branch t | .call t => some t
  | .ret | .halt => none

namespace CFG

def targets (d : Decoded) : List Nat := d.edges.filterMap edgeTarget

def rawEdges (ds : List Decoded) : List (Nat × Nat) :=
  ds.flatMap fun d => (targets d).map (d.addr, ·)

def outward (ds : List Decoded) (edges : List (Nat × Nat)) : List Nat :=
  (edges.map Prod.snd).filter fun l => decide (l ∉ starts ds)

structure Row where
  code : Silmaril.X86.Decompile.Region
  fuel : Nat
  listing : List Decoded
  entry : Nat
  edges : List (Nat × Nat)
  exits : List Nat
  deriving DecidableEq, Repr

/-- Exact syntactic rows. Empty normal exits allow traps; they do not prove
termination, progress, absence of faults, or a function boundary. -/
def Row.Valid (r : Row) : Prop :=
  r.code.decode? r.fuel = some r.listing ∧
  (∀ d ∈ r.listing, interprocedural d.instr = false) ∧
  IsStart r.listing r.entry ∧
  r.code.base + r.code.bytes.length < 2 ^ 64 ∧
  r.edges.toFinset = (rawEdges r.listing).toFinset ∧
  r.exits.toFinset = (outward r.listing r.edges).toFinset

instance (r : Row) : Decidable r.Valid := by unfold Row.Valid; infer_instance

def Row.Support (r : Row) (label : Nat) : Prop := IsStart r.listing label

def Row.Edge (r : Row) (source target : Nat) : Prop := (source, target) ∈ r.edges

structure Certified where
  row : Row
  valid : row.Valid

end CFG
end Silmaril.Machine.Region.X86
