module

public import Silmaril.Machine.Region.X86.CFG.View.Defs
public import Silmaril.Machine.Region.X86.CFG.Thms

@[expose] public section
namespace Silmaril.Machine.Region.X86.CFG

/-- Every edge source is a decoded instruction start, including loops and
cross edges; no graph partition or tree reconstruction is needed. -/
theorem flat_source_closed {r : Row} (valid : r.Valid) : r.flat.SourceClosed :=
  fun a b edge => let ⟨d, hd, addr, _⟩ := (edges_iff valid a b).mp edge
    List.mem_map.mpr ⟨d, hd, addr⟩

theorem flat_exits {r : Row} (valid : r.Valid) (b : Nat) :
    b ∈ r.flat.exits ↔ (∃ a, b ∈ r.flat.successors a) ∧ b ∉ r.flat.internal :=
  exits_iff valid b

theorem flat_entry {r : Row} (valid : r.Valid) : r.flat.entry ∈ r.flat.internal := valid.2.2.1

end Silmaril.Machine.Region.X86.CFG
