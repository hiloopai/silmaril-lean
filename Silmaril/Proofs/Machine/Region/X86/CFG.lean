module

public import Silmaril.Machine.Region.X86.CFG.Defs

@[expose] public section
namespace Silmaril.Machine.Region.X86.CFG.Proofs
open Silmaril.X86.Decompile

theorem edges_iff {r : Row} (h : r.Valid) (a b : Nat) :
    r.Edge a b ↔ ∃ d ∈ r.listing, d.addr = a ∧ b ∈ targets d := by
  change (a, b) ∈ r.edges ↔ _
  have he := congrArg (fun s => (a, b) ∈ s) h.2.2.2.2.1
  simp only [List.mem_toFinset] at he
  rw [he]
  simp only [rawEdges, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨d, hd, l, hl, ha, rfl⟩
    exact ⟨d, hd, ha, hl⟩
  · rintro ⟨d, hd, ha, hb⟩
    exact ⟨d, hd, b, hb, ha, rfl⟩

theorem exits_iff {r : Row} (h : r.Valid) (b : Nat) :
    b ∈ r.exits ↔ (∃ a, r.Edge a b) ∧ ¬ r.Support b := by
  have he := congrArg (fun s => b ∈ s) h.2.2.2.2.2
  simp only [List.mem_toFinset] at he
  rw [he]
  simp only [outward, List.mem_filter, List.mem_map, decide_eq_true_eq,
    Row.Support, IsStart, Row.Edge]
  constructor
  · rintro ⟨⟨⟨a, target⟩, edge, rfl⟩, outside⟩
    exact ⟨⟨a, edge⟩, outside⟩
  · rintro ⟨⟨a, edge⟩, outside⟩
    exact ⟨⟨(a, b), edge, rfl⟩, outside⟩

end Silmaril.Machine.Region.X86.CFG.Proofs
