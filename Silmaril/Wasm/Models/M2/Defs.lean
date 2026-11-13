module

public import Silmaril.Wasm.Models.Game.Defs
public import Silmaril.Wasm.Models.Model.Thms
public import Silmaril.Wasm.Atlas.Games.Thms

/-!
# The stateful game reading (M2) as a Wasm model

`Emb.ginstCoHom` (`Silmaril.Wasm.Models.Game`) reads every Wasm model through its *observation
strategies*, in which each call is answered as at a fresh point. The game semantics of a scalar
Core instance (M2, `Silmaril.Wasm.Game`) is stateful: the store persists from one export call to
the next. This module puts the two side by side.

* `m2Model P I S`: the Wasm model of the game chart of `I` (`Atlas.Games.chart`). Points are a
  store and an environment, calls are the export calls of `I`, and observations are those of the
  closed program `K.strategy ≫ I.strategy P s`. The domain is M2's domain intersected with the
  domain of `core|S`, and the syntax is Core's.
* `m2Emb P I S : (m2Model P I S).Emb (coreModel P Nat S)` (direction `sub`, every profile, from
  `compositeObs_subset_behaviours`) and `m2EmbDet o I S` (direction `eq`, deterministic profiles,
  from `adequacy`), with total read-back `m2TotalDet`.
* `toBeh I`: the renaming of the call signature `callSig I.F.Op (Behaviour Val)` into the export
  signature `I.F`, reading answers as behaviours; `statefulStrat P I x`: **the stateful reading**
  of point `x = (s, K)`, the closed program restricted along `toBeh I`. It is a strategy of the
  same game as the observation strategy `(m2Model P I S).strat x`.

`Thms` relates them: the first calls of the stateful reading are the terminating observations
(`callPlay_stateful_iff`), so it agrees with the fresh observation strategy on first calls
(`callPlay_strat_iff_stateful`); after an answered call it continues as the stateful reading at the
store that some Core run of that call leaves (`stateful_after_iff`); and at deterministic profiles
the reduct of the Core observation strategy along `m2EmbDet` is the fresh observation strategy
(`m2_reduct_eq`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Numerics (Profile)

namespace M2

/-- **The Wasm model of the game chart** of a scalar instance. -/
noncomputable def m2Model (P : Profile) (I : ScalarInstance) (S : FeatureSet) : WasmModel where
  feats := S
  Module := Silmaril.Wasm.Module
  Valid := ValidIn S
  Pt := Atlas.Games.Pt I
  Call := I.F.Op
  Obs := Behaviour Val
  obs := Atlas.Games.obs P I
  dom x := Atlas.Games.Dom I x ∧ coreDom S (Atlas.Games.corePt I x)

/-- **M2 as an embedding into `core|S`**, every profile: game observations are Core
observations. -/
noncomputable def m2Emb (P : Profile) (I : ScalarInstance) (S : FeatureSet) :
    (m2Model P I S).Emb (coreModel P Nat S) where
  mod m := m
  valid _ h := h
  pt := Atlas.Games.corePt I
  call := Atlas.Games.call I
  readback := some
  dom _ hx := hx.2
  dir := .sub
  sat x hx f := fun b hb =>
    ⟨b, ScalarInstance.compositeObs_subset_behaviours hx.1.1 x.2 hx.1.2 f hb, rfl⟩

/-- **M2 as an equality embedding into `core|S`**, deterministic profiles. -/
noncomputable def m2EmbDet (o : GrowOracle) (I : ScalarInstance) (S : FeatureSet) :
    (m2Model (profile o) I S).Emb (coreModel (profile o) Nat S) where
  mod m := m
  valid _ h := h
  pt := Atlas.Games.corePt I
  call := Atlas.Games.call I
  readback := some
  dom _ hx := hx.2
  dir := .eq
  sat x hx f :=
    (WasmModel.view_some (coreModel (profile o) Nat S) _ _).trans
      (ScalarInstance.adequacy hx.1.1 x.2 hx.1.2 f)

/-- The read-back of `m2EmbDet` is total. -/
noncomputable def m2TotalDet (o : GrowOracle) (I : ScalarInstance) (S : FeatureSet) :
    (m2EmbDet o I S).Total :=
  ⟨fun b => b, fun _ => rfl⟩

/-- Reading the answers of export calls as behaviours. -/
noncomputable def toBeh (I : ScalarInstance) : Sig.Hom (callSig I.F.Op (Behaviour Val)) I.F :=
  ⟨fun f => f, fun f w => Answer.toBehaviour (ft := I.exports.get f.1) w⟩

/-- **The stateful reading** of a point: the closed program, with answers read as behaviours. -/
noncomputable def statefulStrat (P : Profile) (I : ScalarInstance) (x : Atlas.Games.Pt I) :
    Strategy Sig.empty (callSig I.F.Op (Behaviour Val)) :=
  (I.closedWith P x.1 x.2).restrict (toBeh I)

end M2

end Silmaril.Wasm.Models
