module

public import Silmaril.Machine.Region.X86.CFG.Defs
import Silmaril.Proofs.Machine.Region.X86.CFG

@[expose] public section
namespace Silmaril.Machine.Region.X86.CFG
open Silmaril.X86.Decompile

theorem edges_iff {r : Row} (h : r.Valid) (a b : Nat) :
    r.Edge a b ↔ ∃ d ∈ r.listing, d.addr = a ∧ b ∈ targets d := Proofs.edges_iff h a b

/-- Outward edges are recomputed using actual source/target wiring, including
cross edges and loops. Declared labels are neither blindly subtracted nor sorted. -/
theorem exits_iff {r : Row} (h : r.Valid) (b : Nat) :
    b ∈ r.exits ↔ (∃ a, r.Edge a b) ∧ ¬ r.Support b := Proofs.exits_iff h b

end Silmaril.Machine.Region.X86.CFG
