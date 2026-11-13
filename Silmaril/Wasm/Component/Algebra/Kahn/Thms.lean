module

public import Silmaril.Wasm.Component.Algebra.Kahn.Defs
public import Silmaril.Games.Composition.Defs
public import Silmaril.Wasm.Component.Adapter.Defs
public import Silmaril.Games.Handler.Thms
import Silmaril.Proofs.Wasm.Component.Algebra.Kahn

/-!
# Kahn strategies: composition and identity

* `denotes_kahn`: the Kahn machine of `F` denotes `kahn F` (its traces are exactly the plays).
* **`kahn_comp`**: for monotone stream functions, **composition of strategies is composition of
  stream functions**: `(kahn F).comp (kahn G) = kahn (G ∘ F)`. The upstream strategy is on the
  left (it answers the pulls of the downstream one).
* **`kahn_id`**: the Kahn strategy of the identity stream function is **copycat** on the stream
  interface, `Strategy.ofHandler (maskH 1)`.

Proofs in `Silmaril.Proofs.Wasm.Component.Algebra.Kahn` (mutual weak simulations, then
`LTS.Denotes.eq_of_simulation`).
-/

public section

namespace Silmaril.Wasm.Component.Algebra.Kahn

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Proofs.Wasm.Component.Algebra.Kahn (compSim compSim' idSim idSim')

/-- The Kahn machine denotes its strategy. -/
theorem denotes_kahn (F : List Ans → List Ans) : (kahnL F).Denotes (kahn F) :=
  Silmaril.Proofs.Wasm.Component.Algebra.Kahn.denotes_kahn F

/-- **Composition of Kahn strategies is composition of stream functions.** -/
theorem kahn_comp {F G : List Ans → List Ans} (hF : Mono F) (hG : Mono G) :
    (kahn F).comp (kahn G) = kahn fun h => G (F h) :=
  LTS.Denotes.eq_of_simulation ((denotes_kahn F).comp (denotes_kahn G))
    (denotes_kahn _) (compSim hF hG) (compSim' hF hG)

/-- **The identity stream function is copycat.** -/
theorem kahn_id : kahn id = Strategy.ofHandler (maskH 1) :=
  LTS.Denotes.eq_of_simulation (denotes_kahn id) (Handler.denotes_toLTS (maskH 1)) idSim idSim'

/-- Equal stream functions have equal Kahn strategies. -/
theorem kahn_congr {F G : List Ans → List Ans} (h : ∀ hs, F hs = G hs) : kahn F = kahn G := by
  rw [show F = G from funext h]

/-- The identity is monotone. -/
theorem mono_id : Mono id := fun h h' => List.prefix_append h h'

/-- Composites of monotone stream functions are monotone. -/
theorem Mono.comp {F G : List Ans → List Ans} (hF : Mono F) (hG : Mono G) :
    Mono fun h => G (F h) := fun h h' => by
  obtain ⟨t, ht⟩ := hF h h'
  show G (F h) <+: G (F (h ++ h'))
  rw [← ht]
  exact hG _ t

end Silmaril.Wasm.Component.Algebra.Kahn
