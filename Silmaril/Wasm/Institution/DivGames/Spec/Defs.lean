module

public import Silmaril.Wasm.Institution.DivGames.Edges.Defs
public import Silmaril.Wasm.Institution.Api.Defs

@[expose] public section

/-!
# The divergence-aware logic graph through the institution facade

`DivGames.divGraph` (`entry → red → game`) presented with the facade's typed graph builder
`Silmaril.Inst.GraphSpec`:

* `dinst P host R a`: the facade institution (`Institution₁`) of the node `a`,
  `Institution.ofObs (dsem P host R a)`;
* `divSpec P host R`: the two comorphism edges, each a facade `CoEdge` whose comorphism is
  `Comorphism.ofObs` of the edge's translation, type checked against its endpoints;
* `divSpec_comor_entryRed`, `divSpec_comor_redGame`: the edges of the built graph act by the
  comorphisms of `divGraph` (`rfl`), and `divSpec_inst`: the nodes carry the same institutions.

`divGraph` is not an `ObsGraph`: `ObsGraph` asks every comorphism edge to be a
model-expansive translation, and `entryToRed` is not claimed model-expansive (its semantic
map `entryObj` does not reach entry objects with a non-trivial `Ok` premise; see
`Silmaril.Wasm.Institution.DivGames.Graph`). So the facade statement is per edge:
`redGame_modelExpansive'` for the listed `red → game` edge, and borrowing along that edge in
facade terms (`valid_redToGame_iff'`). The spec's graph has edge type `ComorIdx` (indices of
the listed edges), not `DEdge`, so it is not literally equal to `divGraph`; the statements
above relate them edge by edge.
-/

namespace Silmaril.Wasm.Institution.DivGames

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Institution
open Silmaril.Inst (Institution₁ CoEdge GraphSpec)

variable {H : Type} (P : Profile) (host : HostSemantics H)

/-- The facade institution of a node of the divergence-aware graph. -/
abbrev dinst (R : BRel) (a : DNode) : Institution₁ :=
  Silmaril.Inst.Institution.ofObs (dsem P host R a)

/-- **The divergence-aware logic graph as a facade `GraphSpec`.** -/
noncomputable def divSpec (R : BRel) : GraphSpec (dinst P host R) where
  comors :=
    [⟨DNode.entry, DNode.red, Silmaril.Inst.Comorphism.ofObs (dedge P host R DEdge.entryRed)⟩,
     ⟨DNode.red, DNode.game, Silmaril.Inst.Comorphism.ofObs (dedge P host R DEdge.redGame)⟩]

/-- The nodes of the spec's graph carry the institutions of `divGraph`. -/
theorem divSpec_inst (R : BRel) (a : DNode) :
    (divSpec P host R).toLogicGraph.inst a = (divGraph P host R).inst a := rfl

/-- The first listed edge acts by the comorphism of `divGraph`'s `entryRed` edge. -/
theorem divSpec_comor_entryRed (R : BRel) :
    (divSpec P host R).toLogicGraph.comor ((divSpec P host R).coEdge ⟨0, Nat.zero_lt_two⟩) =
      (divGraph P host R).comor DEdge.entryRed := rfl

/-- The second listed edge acts by the comorphism of `divGraph`'s `redGame` edge. -/
theorem divSpec_comor_redGame (R : BRel) :
    (divSpec P host R).toLogicGraph.comor ((divSpec P host R).coEdge ⟨1, Nat.one_lt_two⟩) =
      (divGraph P host R).comor DEdge.redGame := rfl

/-- The `red → game` edge of the spec is model-expansive. -/
theorem redGame_modelExpansive' (R : BRel) :
    ((divSpec P host R).toLogicGraph.comor
      ((divSpec P host R).coEdge ⟨1, Nat.one_lt_two⟩)).ModelExpansive :=
  redGame_modelExpansive P host R

/-- Borrowing along `redToGame`, in the facade's terms: validity in the facade institution of
`red` is validity of the translated sentence in that of `game`. -/
theorem valid_redToGame_iff' (R : BRel) {K : Sig (Set String)}
    (s : ObsSemantics.Sen (dsem P host R .red) K) :
    (dinst P host R .red).Valid s ↔
      (dinst P host R .game).Valid
        ((Silmaril.Inst.Comorphism.ofObs (dedge P host R DEdge.redGame)).sen K s) :=
  (Silmaril.Inst.Comorphism.ofObs (dedge P host R DEdge.redGame)).valid_iff
    (redGame_modelExpansive P host R) s

end Silmaril.Wasm.Institution.DivGames
