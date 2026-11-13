module

public import Silmaril.Wasm.Institution.GameReadings.Defs
import Silmaril.Proofs.Wasm.Institution.GameReadings.Copies

/-!
# The game reading of the game-semantics logic is model-expansive

**`GameInst.modOf_surjective`**: every assignment `β : V → Strategy E (G.sig X)` of strategies to
the program variables of a signature `(V, X)` is `modOf` of one strategy on the copies. So

* `GameInst.reading_surjective`, `GameInst.coHom_modelExpansive`: the comorphism
  `GameInst.coHom G E` into `GInst` is model-expansive, for every `G` and `E`;
* `GameInst.coHom_entails_iff`: **borrowing**: entailment in the game-semantics logic is
  entailment of the translated game properties in `GInst`.

The strategy is `copiesStrategy β` (`Silmaril.Proofs.Wasm.Institution.GameReadings.Copies`): its
plays are the legal plays all of whose single-copy prefixes, in copy `v`, are plays of `β v`.
The game is single-threaded and the restriction to copy `v` only sees the plays whose upper
questions are all in copy `v`, so no product of strategies over the shared lower interface is
needed: after a play that mixes copies, `copiesStrategy β` allows every legal continuation.

New theorems.
-/

@[expose] public section

open CategoryTheory Silmaril.Logic.Institution Silmaril.Inst
open Silmaril.Games (Game GSen GInst Strategy)

namespace Silmaril.Wasm.Institution.GameInst

open Silmaril.Wasm.Institution.Games (GameIfaces gameSem)

/-- **Every family of strategies is the restriction of one strategy on the copies.** -/
theorem exists_restrict_eq {V : Type} {E S : Silmaril.Games.Sig.{0}} (τ : V → Strategy E S) :
    ∃ σ : Strategy E (copies V S), ∀ v, σ.restrict (inj v) = τ v :=
  ⟨Silmaril.Proofs.Wasm.Institution.GameReadings.copiesStrategy τ,
    Silmaril.Proofs.Wasm.Institution.GameReadings.restrict_copiesStrategy τ⟩

variable (G : GameIfaces) (E : Silmaril.Games.Sig.{0})

/-- **`modOf` is surjective**: every model assignment is read off a strategy on the copies. -/
theorem modOf_surjective (A : Silmaril.Wasm.Institution.Sig G.I) :
    Function.Surjective (modOf G E A) := fun β =>
  (exists_restrict_eq β).elim fun σ hσ => ⟨σ, funext hσ⟩

/-- The game reading of the game-semantics logic has surjective model maps. -/
theorem reading_surjective (A : Silmaril.Wasm.Institution.Sig G.I) :
    Function.Surjective ((reading G E).mod A) :=
  modOf_surjective G E A

/-- **`GameInst.coHom` is model-expansive.** -/
theorem coHom_modelExpansive : Comorphism.ModelExpansive (coHom G E) :=
  (reading G E).modelExpansive (reading_surjective G E)

/-- **Borrowing along `GameInst.coHom`**: entailment in the game-semantics logic is entailment of
the translated game properties in `GInst`. -/
theorem coHom_entails_iff (A : Silmaril.Wasm.Institution.Sig G.I) (Γ : Set ((gameSem G E).Sen A))
    (s : (gameSem G E).Sen A) :
    Institution.Entails (gameSem G E).inst (S := A) Γ s ↔
      Institution.Entails GInst (S := gameOf G E A) (senOf G E A '' Γ) (senOf G E A s) :=
  (reading G E).entails_iff (reading_surjective G E) A Γ s

end Silmaril.Wasm.Institution.GameInst
