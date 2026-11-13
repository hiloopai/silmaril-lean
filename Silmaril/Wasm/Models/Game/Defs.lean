module

public import Silmaril.Wasm.Models.Model.Defs
public import Silmaril.Games.Reindex.Defs

/-!
# Wasm models in the institution of game semantics

Every Wasm model `A` (`Silmaril.Wasm.Models.WasmModel`) is read as a family of `GInst` models, one
per point (`docs/projects/spectec/README.md` §1.3, §2):

* `callSig C O`: the signature with one operation per call `c : C`, answered by an observation
  `o : O`; `callPlay c o` is the one-call play "question `c`, answer `o`";
* `obsStrat obs : Strategy Sig.empty (callSig C O)`: **the observation strategy** of
  `obs : C → Set O`. Its plays are the legal plays of the closed game `∅ ↠ callSig C O` whose
  answers are all observations: an answer `o` to `c` is allowed iff `o ∈ obs c`. Calls are
  independent of each other, so the strategy reads `obs` as the observations of a *fresh* point
  for each call. It is the one-call reading of a model; the stateful game semantics of a Core
  instance is `Silmaril.Wasm.Game.ScalarInstance.strategy` (M2);
* `WasmModel.game A`: the closed game `∅ ↠ callSig A.Call A.Obs`; `WasmModel.strat A p`, the
  observation strategy of point `p`;
* `WasmModel.Emb.Total e`: the read-back of an embedding is total (`readback = some ∘ g`);
  `Emb.gameHom e t : A.game ⟶ B.game` renames calls along `e.call` and reads answers back along
  `g`;
* `WasmModel.ginst A : Inst`: `GInst` reindexed at the single game `A.game`; `Emb.ginstCoHom e t`,
  the comorphism of the game morphism (`GInst.reindex`), and `WasmModel.toGInst A`, the
  comorphism into `GInst`.

`Thms`: `mem_callPlay_iff`, `obsStrat_mono`, `obsStrat_le_iff` (refinement of observation
strategies is inclusion of observations), and `Emb.reduct_le`: for an embedding of direction
`eq` or `sup` with a total read-back, the reduct of the target's strategy at `e.pt p` refines the
source's strategy at `p`, so universal sentences true of the source hold of the target after
translation (`Emb.sat_translate`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open CategoryTheory Silmaril.Games Silmaril.Logic.Institution

/-- The call signature: one operation per call, answered by an observation. -/
def callSig (C O : Type) : Sig.{0} := ⟨C, fun _ => O⟩

/-- The one-call play: the question `c` answered by `o`. -/
def callPlay {C O : Type} (c : C) (o : O) : List (Move Sig.empty (callSig C O)) :=
  [.inr (.ask c), .inr (.ans c o)]

/-- The plays of the observation strategy: legal plays whose answers are observations. -/
def obsPlays {C O : Type} (obs : C → Set O) : Set (List (Move Sig.empty (callSig C O))) :=
  {s | Legal s ∧ ∀ (c : C) (o : O), (.inr (.ans c o) : Move Sig.empty (callSig C O)) ∈ s →
    o ∈ obs c}

/-- **The observation strategy** of `obs : C → Set O`: every call is answered by one of its
observations, calls being independent. -/
def obsStrat {C O : Type} (obs : C → Set O) : Strategy Sig.empty (callSig C O) where
  plays := obsPlays obs
  nil_mem := ⟨Legal.nil, fun _ _ h => absurd h List.not_mem_nil⟩
  legal h := h.1
  of_prefix := by
    rintro s t ⟨ht, hans⟩ hst
    exact ⟨ht.of_prefix hst, fun c o hm => hans c o (hst.subset hm)⟩
  receptive := by
    rintro s x y o ⟨-, hans⟩ hx hxy ho
    refine ⟨⟨y, hx.append (Path.single hxy)⟩, fun c a hm => ?_⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact hans c a hm
    · rw [List.mem_singleton] at hm
      subst hm
      exact absurd ho id

namespace WasmModel

/-- The closed game of a model: no imports, its calls answered by its observations. -/
def game (A : WasmModel) : Game.{0} := ⟨Sig.empty, callSig A.Call A.Obs⟩

/-- **The strategy of a point**: its observation strategy. -/
def strat (A : WasmModel) (p : A.Pt) : A.game.Model := obsStrat (A.obs p)

/-- `GInst` at the game of a model (signatures: one object). -/
def ginst (A : WasmModel) : Inst.{0, 0, 0, 0, 0} :=
  GInst.along ((Functor.const (Discrete PUnit.{1})).obj A.game)

/-- The comorphism from the game institution of a model into `GInst`. -/
def toGInst (A : WasmModel) : Inst.CoHom A.ginst GInst :=
  GInst.alongCoHom _

variable {A B : WasmModel}

/-- **A total read-back**: target observations are always read back. -/
structure Emb.Total (e : A.Emb B) where
  /-- The read-back function. -/
  g : B.Obs → A.Obs
  /-- The read-back is `g`. -/
  readback_eq : ∀ b, e.readback b = some (g b)

/-- **The game morphism of an embedding** with a total read-back: calls renamed along
`e.call`, answers read back along `g`. -/
def Emb.gameHom (e : A.Emb B) (t : e.Total) : A.game ⟶ B.game :=
  (⟨Sig.Hom.id Sig.empty, ⟨e.call, fun _ => t.g⟩⟩ : Game.Hom A.game B.game)

/-- **The comorphism of game institutions of an embedding** (through `GInst.reindex`). -/
def Emb.ginstCoHom (e : A.Emb B) (t : e.Total) : Inst.CoHom A.ginst B.ginst :=
  GInst.reindex (𝟭 _)
    { app := fun _ => e.gameHom t
      naturality := fun _ _ _ => by simp }

end WasmModel

end Silmaril.Wasm.Models
