module

public import Silmaril.Encoding.Lattice

/-!
# Executable codec laws against encoder graphs

Round trips are specifications in `EncRel`: canonicity is decoder soundness
for `ofFun enc`, and a bounded round trip is completeness on that graph.
The results here apply to any carrier and syntax, including field lists.
-/

@[expose] public section

namespace Silmaril.EncRel

variable {σ α : Type}

/-- Completeness on an encoder graph is a round trip on the stated values. -/
theorem ofFun_decoderCompleteOn_iff (enc : α → σ) (dec : σ → Option α)
    (P : α → Prop) :
    (ofFun enc).DecoderCompleteOn P dec ↔ (ofDecoder dec).EncoderCorrectOn P enc := by
  constructor
  · intro h a ha; exact h (enc a) a ha rfl
  · intro h s a ha hs; cases hs; exact h a ha

/-- A functional encoder graph is exactly an injective encoder. -/
theorem ofFun_functional_iff {enc : α → σ} :
    (ofFun enc).Functional ↔ Function.Injective enc := by
  constructor
  · intro h a b hab; exact h rfl hab.symm
  · intro h s a b ha hb; exact h (ha.trans hb.symm)

end Silmaril.EncRel
