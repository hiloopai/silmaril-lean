module

public import Silmaril.Wasm.SpecTec.Institution.Juxt.Defs

/-!
# Juxtaposing institutions: results

* `grammarInclusion_sat`: a grammar sentence holds in a model of `withGrammars G` iff it holds in
  the model's grammar component (the satisfaction condition of the inclusion).
* `relationInclusion_sat`: the same for relational sentences.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u₂ v₂

/-- **The satisfaction condition of the grammar inclusion.** -/
theorem grammarInclusion_sat (G : Inst.{u₂, v₂, 0, 0, 0}) (T : G.Sign)
    (M : ((withGrammars G).I.obj ((grammarInclusion G).Φ.obj T)).Mod) (ψ : (G.I.obj T).Sen) :
    ((withGrammars G).I.obj ((grammarInclusion G).Φ.obj T)).Sat M
        (((grammarInclusion G).ρ.app T).sen ψ) ↔ (G.I.obj T).Sat M.2 ψ :=
  Iff.rfl

/-- **The satisfaction condition of the relational inclusion.** -/
theorem relationInclusion_sat (G : Inst.{u₂, v₂, 0, 0, 0}) (T₀ : G.Sign) (S : Sig)
    (M : ((withGrammars G).I.obj ((relationInclusion G T₀).Φ.obj S)).Mod) (φ : Sen S) :
    ((withGrammars G).I.obj ((relationInclusion G T₀).Φ.obj S)).Sat M
        (((relationInclusion G T₀).ρ.app S).sen φ) ↔ φ.1.Sat backend M.1.as.env M.1.as.D :=
  Iff.rfl

end Silmaril.Wasm.SpecTec.Institution
