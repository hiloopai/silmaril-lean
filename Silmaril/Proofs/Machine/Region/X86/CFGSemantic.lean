module

public import Silmaril.Machine.Region.X86.CFG.Semantic.Defs
public import Silmaril.Machine.Region.X86.CFG.Thms
public import Silmaril.Machine.Region.X86.Thms

@[expose] public section
namespace Silmaril.Machine.Region.X86.CFG.SemanticProofs
open Silmaril.Semantics.Region
open Silmaril.X86.Decompile

theorem retirement_edge {r : Row} (valid : r.Valid) {ret : Silmaril.X86.Word}
    {s t : Silmaril.X86.MState} (loaded : r.code.LoadedIn s.memory)
    (inside : r.Support s.core.rip.toNat) (step : (system ret).step s [] t) :
    r.Edge s.core.rip.toNat t.core.rip.toNat := by
  obtain ⟨d, hd, pc⟩ := List.mem_map.mp inside
  have target := listing_step valid.1 loaded hd pc.symm step
  have direct := valid.2.1 d hd
  simp only [instructionTargets, direct, Bool.false_eq_true, ↓reduceIte, Targets.Allows] at target
  exact (edges_iff valid _ _).mpr ⟨d, hd, pc, List.mem_toFinset.mp target⟩

theorem local_certificate {r : Row} (valid : r.Valid) {Ambient : Type*} (c : ExecutionContract r Ambient) :
    Local c.interleaving r.Support c.invariant
      (fun t => (c.focus t).core.rip.toNat ∈ r.exits) := by
  intro s es t invariant inside edge
  constructor
  · intro _
    rcases edge.2 with thread | environment
    · exact c.thread_preserves s t invariant thread
    · exact c.environment_preserves s t invariant environment
  · intro outside
    rcases edge.2 with thread | environment
    · exact (exits_iff valid _).mpr
        ⟨⟨_, retirement_edge valid (c.loaded s invariant) inside (c.thread_step s t thread)⟩, outside⟩
    · apply False.elim; apply outside
      change r.Support (c.focus t).core.rip.toNat
      rw [c.environment_pc s t invariant environment]
      exact inside

end Silmaril.Machine.Region.X86.CFG.SemanticProofs
