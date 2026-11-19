module

public import Silmaril.Machine.Region.X86.CFG.Semantic.Defs
public import Silmaril.Semantics.Region.Semantic.Thms
import Silmaril.Proofs.Machine.Region.X86.CFGSemantic

@[expose] public section
namespace Silmaril.Machine.Region.X86.CFG
open Silmaril.Semantics.Region

theorem retirement_edge {r : Row} (valid : r.Valid) {ret : Silmaril.X86.Word}
    {s t : Silmaril.X86.MState} (loaded : r.code.LoadedIn s.memory)
    (inside : r.Support s.core.rip.toNat) (step : (system ret).step s [] t) :
    r.Edge s.core.rip.toNat t.core.rip.toNat := SemanticProofs.retirement_edge valid loaded inside step

/-- Normal first exits of a focused thread interleaved with PC-stuttering,
code-preserving environment steps follow the declared outward labels. No
fairness, progress, race freedom, or hardware concurrency theorem is inferred. -/
theorem interleaving_sound {r : Row} (valid : r.Valid) {Ambient : Type*}
    (c : ExecutionContract r Ambient) {A : Ambient → Prop}
    (admit : ∀ s, A s → c.invariant s) :
    Sound c.interleaving A r.Support (fun label => label ∈ r.exits) :=
  local_sound (SemanticProofs.local_certificate valid c) admit (fun _ h => h)

/-- Region-level validity additionally needs a nonempty admitted entry domain.
The byte CFG supplies no such domain or incoming-edge restriction by itself. -/
theorem semantic_valid {r : Row} (valid : r.Valid) {Ambient : Type*}
    (c : ExecutionContract r Ambient) {A : Ambient → Prop}
    (admit : ∀ s, A s → c.invariant s) (inhabited : ∃ s, A s)
    (entry : ∀ s, A s → c.interleaving.pc s = r.entry) :
    Valid c.interleaving (fun _ => True) A r.Support r.entry r.exits.toFinset :=
  ⟨trivial, valid.2.2.1, inhabited, entry, fun _ _ => trivial,
    fun s es t ha path => List.mem_toFinset.mpr (interleaving_sound valid c admit s es t ha path)⟩

end Silmaril.Machine.Region.X86.CFG
