module

public import Silmaril.Wasm.Category.Exec.Defs
public import Silmaril.Proofs.Wasm.Category.Exec.Basic

@[expose] public section

/-!
# Execution semantics, cofunctors and simulations: results

Proofs in `Silmaril.Proofs.Wasm.Category.Exec.Basic`.

* `Exec.Deterministic.beh_subsingleton`: a deterministic program has at most one behaviour.
* `RelCofunctor.valid`, `RelCofunctor.valid_of_readBack`: a relational cofunctor with matched
  initial configurations and coherent final observations proves validity.
* `BackwardSim.valid`: a backward simulation (with stuttering measure) proves validity.
* `ForwardSim.preserves`, `ForwardSim.valid`: forward simulations preserve behaviours, and
  into a deterministic target prove validity (the flip).
* `compilerOfBackward`, `compilerOfForward`: compilers from simulations.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category

universe u

variable {L L' : Language.{u}}

/-- A compiler from a translation with backward simulations. -/
def compilerOfBackward (c : L ⟶ L') (E : Exec L) (E' : Exec L') (run : L.Prog → Option L'.Prog)
    (hΦ : ∀ p p', run p = some p' → c.Φ (L.iface p) = L'.iface p')
    (sim : ∀ p p', run p = some p' → Nonempty (BackwardSim c E E' p p')) : Compiler L L' where
  conv := c
  run := run
  sound p p' h := (sim p p' h).some.valid (hΦ p p' h)

/-- A compiler from a translation with forward simulations into a deterministic target, for
sources that have a behaviour (the forward-to-backward flip). -/
def compilerOfForward (c : L ⟶ L') (E : Exec L) (E' : Exec L') (run : L.Prog → Option L'.Prog)
    (hdet : E'.Deterministic)
    (hne : ∀ p p', run p = some p' → (L.beh p).Nonempty)
    (hΦ : ∀ p p', run p = some p' → c.Φ (L.iface p) = L'.iface p')
    (sim : ∀ p p', run p = some p' → Nonempty (ForwardSim c E E' p p')) : Compiler L L' where
  conv := c
  run := run
  sound p p' h := (sim p p' h).some.valid hdet (hne p p' h) (hΦ p p' h)

end Silmaril.Wasm.Category
