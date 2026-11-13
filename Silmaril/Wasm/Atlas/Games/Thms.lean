module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.Core.Thms
public import Silmaril.Wasm.Atlas.Games.Defs
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Wasm.Game.Linking.Thms

/-!
# The game charts: transitions (M2, M3)

* `Games.toCore P I` (**M2 as a transition**, every profile): equal on the sentences that ignore
  `diverges` (`BSen.Ignores .diverges`: divergence-tolerant partial correctness, terminating
  witnesses), from `adequacy_profile`.
* `Games.toCoreDet o I` (**M2, deterministic profiles**): equal on every sentence, from
  `adequacy`.
* `Games.toCoreUniv P I` / `Games.toCoreExist P I` (every profile, every sentence of the class):
  Core reflects universal sentences into games and games preserve existential ones into Core,
  from `compositeObs_subset_behaviours`.
* `Games.linkToCore P S` (**M2 + M3**): the composite of the parts' strategies against the
  closed linked program in Core, equal on `diverges`-ignoring sentences
  (`linked_adequacy_profile`); `Games.linkToCoreDet o S` equal on all (`linked_adequacy`).
* `Games.linkToGame P S` (**M3 as amalgamation**): the composite of the parts against the game
  chart of the linked instance, equal on every sentence (`link_is_composition_profile`).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Games

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game

/-- **M2 as a transition**, every profile: equal on `diverges`-ignoring sentences. -/
noncomputable def toCore (P : Profile) (I : ScalarInstance) : Transition (chart P I) (Core.chart P Nat) :=
  BTrans.ofEqUnion .diverges (corePt I) (call I) (fun _ _ => trivial) (extraDiv P I)
    (fun _ _ _ hb => hb.1)
    (fun x hx f => ScalarInstance.adequacy_profile hx.1 x.2 hx.2 f)

/-- **M2 as a transition**, deterministic profiles: equal on every sentence. -/
noncomputable def toCoreDet (o : GrowOracle) (I : ScalarInstance) :
    Transition (chart (profile o) I) (Core.chart (profile o) Nat) :=
  BTrans.ofEq (corePt I) (call I) (fun _ _ => trivial)
    (fun x hx f => ScalarInstance.adequacy hx.1 x.2 hx.2 f)

/-- Every profile: Core reflects universal sentences into games. -/
noncomputable def toCoreUniv (P : Profile) (I : ScalarInstance) : Transition (chart P I) (Core.chart P Nat) :=
  BTrans.ofSubsetUniv (corePt I) (call I) (fun _ _ => trivial)
    (fun x hx f => ScalarInstance.compositeObs_subset_behaviours hx.1 x.2 hx.2 f)

/-- Every profile: game witnesses are Core witnesses. -/
noncomputable def toCoreExist (P : Profile) (I : ScalarInstance) : Transition (chart P I) (Core.chart P Nat) :=
  BTrans.ofSubsetExist (corePt I) (call I) (fun _ _ => trivial)
    (fun x hx f => ScalarInstance.compositeObs_subset_behaviours hx.1 x.2 hx.2 f)

/-- **A game proof is a Core proof** (every profile): a `diverges`-ignoring sentence holds in
the game chart iff its renaming holds in Core. -/
theorem sat_core_iff {P : Profile} {I : ScalarInstance} {x : Pt I} (hx : Dom I x)
    {s : BSen I.F.Op (Behaviour Val)} (hs : s.Ignores .diverges) :
    (chart P I).Sat x s ↔ (Core.chart P Nat).Sat (corePt I x) (s.rename (call I)) :=
  (toCore P I).sat_iff rfl hx hs

/-- The linked closed program in Core: the shared store and the empty host. -/
def linkCorePt (S : Linking.Setup) (_ : Env (ifaceSig [])) : Core.Pt Nat := (S.sl, emptyHost)

/-- **M2 + M3 as a transition**, every profile: the composite of the parts against the closed
linked program, equal on `diverges`-ignoring sentences. -/
noncomputable def linkToCore (P : Profile) (S : Linking.Setup) : Transition (linkChart P S) (Core.chart P Nat) :=
  BTrans.ofEqUnion .diverges (linkCorePt S) (call S.linkedI) (fun _ _ => trivial)
    (fun _ f => {b | b = .diverges ∧ Diverges P emptyHost (invoke S.sl (S.linkedI.addr f.1) f.2.1)})
    (fun _ _ _ hb => hb.1)
    (fun K hS f => S.linked_adequacy_profile hS P K f)

/-- **M2 + M3**, deterministic profiles: equal on every sentence. -/
noncomputable def linkToCoreDet (o : GrowOracle) (S : Linking.Setup) :
    Transition (linkChart (profile o) S) (Core.chart (profile o) Nat) :=
  BTrans.ofEq (linkCorePt S) (call S.linkedI) (fun _ _ => trivial)
    (fun K hS f => S.linked_adequacy hS o K f)

/-- Environments of the empty interface throw nothing. -/
theorem throwsBelow_nil (K : Env (ifaceSig [])) (n : Nat) : ThrowsBelow K n :=
  fun e => Fin.elim0 e.1

/-- **M3 as amalgamation**: the composite of the parts' strategies against the game chart of the
linked instance (at the shared store), equal on every sentence. -/
noncomputable def linkToGame (P : Profile) (S : Linking.Setup) :
    Transition (linkChart P S) (chart P S.linkedI) :=
  BTrans.ofEq (fun K => (S.sl, K)) id (fun K hS => ⟨hS.linked, throwsBelow_nil K _⟩)
    (fun K hS f => by
      show compositeObs (K.strategy.comp (S.linkedI.σ P)) f = _
      rw [S.link_is_composition_profile hS P]
      rfl)

end Silmaril.Wasm.Atlas.Games
