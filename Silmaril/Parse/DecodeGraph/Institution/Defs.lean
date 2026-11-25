module

public import Silmaril.Parse.DecodeGraph.Defs

/-! # Exact-success decoder institution

Fix the query context and byte/span carriers. Signatures are instruction types,
with functions as signature arrows. Models are success graphs (taken as
discrete model categories). An atom asserts one exact graph entry.
-/

@[expose] public section

namespace Silmaril.Parse.DecodeGraph.Institution

abbrev Atom (Context Buffer Instr : Type*) := Input Context Buffer × (Instr × Nat)

variable {Context Buffer Source Target : Type*}

/-- Change only the named instruction, preserving the context, bytes and span. -/
def translate (f : Source → Target) (atom : Atom Context Buffer Source) : Atom Context Buffer Target :=
  (atom.1, (f atom.2.1, atom.2.2))

/-- Inverse image, not the forward transport of successes along `f`. -/
def reduct (f : Source → Target) (model : Graph Context Buffer Target) : Graph Context Buffer Source :=
  Set.preimage (translate f) model

def Satisfies (model : Graph Context Buffer Source) (atom : Atom Context Buffer Source) : Prop := atom ∈ model

end Silmaril.Parse.DecodeGraph.Institution
