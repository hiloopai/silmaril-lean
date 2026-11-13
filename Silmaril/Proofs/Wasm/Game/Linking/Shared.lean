module

public import Silmaril.Proofs.Wasm.Game.Linking.Setup
public import Silmaril.Proofs.Wasm.Game.Linking.Simulation
public import Silmaril.Wasm.Link.PreparedObservation

/-!
# Linked = shared, over any number of export calls (M3, step A)

The linked module and the shared world (provider and consumer instantiated
separately in one store) have the same plays. This extends silmaril-lean's
forward simulation of terminating runs (`PreparedObservation`) with the
reverse direction, divergence and persistence of the store relation across
export calls. The forward inclusion (shared plays are linked plays,
`shared_plays_subset_linked`) holds for every profile; the reverse one needs
the reverse simulation `ReachReverse P`, proved for every profile
(`reachReverse_all`, `Silmaril.Proofs.Wasm.Game.Linking.Reverse`; for the deterministic profiles
also `reachReverse_profile`, from `reach_reverse`): `Persistent` (`StoreRelation.Related` together
with well-formedness of the shared instance) holds initially and is preserved
by each export activation, so the play-level bisimulation continues.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.Linking
  Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC

namespace ScalarInstance

variable {I : ScalarInstance}

/-- A single activation of an instance answered without callouts. -/
theorem path_pair_iff {P : Profile} {s s₁ : Store Nat} {f : I.F.Op} {v : I.F.Ar f} :
    I.Path P (.idle s) [.inr (.ask f), .inr (.ans f v)] (.idle s₁) ↔
      ∃ (t₁ : Thread) (r : Result), Reach P (s, I.initThread f) (s₁, t₁) ∧ ResultAt s₁ t₁ r ∧
        Answer.ofResult? (I.exports.get f.1) r = some v := by
  constructor
  · intro hp
    cases hp with
    | cons h1 h2 =>
      cases h1
      cases h2 with
      | cons h3 h4 =>
        cases h4
        cases h3 with
        | oret run final answer => exact ⟨_, _, run, final, answer⟩
  · rintro ⟨t₁, r, run, final, answer⟩
    exact .cons (.call s f) (.cons (.oret run final answer) (.nil _))

/-- A play of a closed instance from an idle state with at least two moves starts with a
complete single activation. -/
theorem path_cons_cons_closed (hI : I.imports = []) {P : Profile} {s : Store Nat}
    {q : I.HState} {m n : Move I.E I.F} {rest : List (Move I.E I.F)}
    (h : I.Path P (.idle s) (m :: n :: rest) q) :
    ∃ (f : I.F.Op) (v : I.F.Ar f) (s₁ : Store Nat), m = .inr (.ask f) ∧ n = .inr (.ans f v) ∧
      I.Path P (.idle s) [m, n] (.idle s₁) ∧ I.Path P (.idle s₁) rest q := by
  cases h with
  | cons h1 h2 =>
    cases h1
    cases h2 with
    | cons h3 h4 =>
      cases h3 with
      | @ucall _ _ _ _ _ _ _ e _ _ _ => exact (ScalarInstance.not_underlay_move hI (.ask e)).elim
      | oret run final answer =>
        exact ⟨_, _, _, rfl, rfl, .cons (.call s _) (.cons (.oret run final answer) (.nil _)),
          h4⟩

/-- The invocation of an export from a well-formed store is typed. -/
theorem invoke_typed {s : Store Nat} (hw : I.WellFormed s) (f : I.F.Op) :
    ∃ ts, ConfigOk (invoke s (I.addr f.1) f.2.1) ts ∧
      ∃ fi : FuncInst Nat, s.funcs[I.addr f.1]? = some fi := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type f.1
  have hinv : InvokeOk s (I.addr f.1) f.2.1 := by
    refine ⟨fi, Ty.ofList ((I.exports.get f.1).params.map ScalarType.toC),
      Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC), hfi, hexp, ?_⟩
    rw [Ty.toList_ofList]
    exact forall₂_valOk_of_hasVal s f.2.2
  obtain ⟨fi', ps, rs, -, -, hok⟩ := invoke_ok hw.storeOk hinv
  exact ⟨_, hok, fi, hfi⟩

end ScalarInstance

namespace Linking

/-- A result of the source is a result of a matching target. -/
theorem resultAt_matching {s s' : Store Nat} {t t' : Thread} {r : Result}
    {mode : AdminRelation.Mode} (final : ResultAt s t r)
    (hm : Simulation.Matching mode (t.config s) (t'.config s')) : ResultAt s' t' r := by
  have code := hm.code
  rw [show (t.config s).code = r.toAdmin from final] at code
  change (t'.config s').code = r.toAdmin
  cases r with
  | values vs => exact code.values_left
  | trap => exact code.trap_singleton
  | throw a => exact code.throwing_left

namespace Setup

variable (S : Setup)

/-- The relation between stores of the shared and linked worlds that persists across export
calls. -/
def Persistent (s s' : Store Nat) : Prop :=
  StoreRelation.Related s s' ∧ S.sharedI.WellFormed s

/-- Initial stores are related. -/
theorem persistent_initial (hS : S.Scalar) : S.Persistent S.sc S.sl :=
  ⟨S.related, hS.shared⟩

/-- One export activation preserves the relation, and the linked module performs the same
activation (same export call, same answer). -/
theorem activation_transfer {P : Profile} {s s' : Store Nat} (hs : S.Persistent s s')
    {f : S.sharedI.F.Op} {v : S.sharedI.F.Ar f} {s₁ : Store Nat}
    (hc : S.sharedI.Path P (.idle s) [.inr (.ask f), .inr (.ans f v)] (.idle s₁)) :
    ∃ s₁', S.linkedI.Path P (.idle s') [.inr (.ask f), .inr (.ans f v)] (.idle s₁') ∧
      S.Persistent s₁ s₁' := by
  obtain ⟨t₁, r, run, final, answer⟩ := ScalarInstance.path_pair_iff.mp hc
  obtain ⟨ts, typed, fi, hfi⟩ := ScalarInstance.invoke_typed hs.2 f
  have matching : Simulation.Matching .same ((S.sharedI.initThread f).config s)
      ((S.linkedI.initThread f).config s') := Simulation.Matching.invoke hs.1 hfi f.2.1
  obtain ⟨⟨s₁', t₁'⟩, run', hm⟩ :=
    reach_simulation (x' := (s', S.linkedI.initThread f)) (ts := ts) run typed matching
  have hc' : S.linkedI.Path P (.idle s') [.inr (.ask f), .inr (.ans f v)] (.idle s₁') :=
    ScalarInstance.path_pair_iff.mpr ⟨t₁', r, run', resultAt_matching final hm, answer⟩
  refine ⟨s₁', hc', ?_,
    (ScalarInstance.WellFormed.activation hs.2 (fun e => Fin.elim0 e.1) hc).1⟩
  have hst := hm.stores
  rwa [Thread.config_store, Thread.config_store] at hst

/-- Conversely, every activation of the linked module from a related store is an activation
of the shared world. -/
theorem activation_reflect {P : Profile} (hrev : ReachReverse P) {s s' : Store Nat}
    (hs : S.Persistent s s')
    {f : S.linkedI.F.Op} {v : S.linkedI.F.Ar f} {s₁' : Store Nat}
    (hc : S.linkedI.Path P (.idle s') [.inr (.ask f), .inr (.ans f v)] (.idle s₁')) :
    ∃ s₁, S.sharedI.Path P (.idle s) [.inr (.ask f), .inr (.ans f v)] (.idle s₁) ∧
      S.Persistent s₁ s₁' := by
  obtain ⟨t₁', r, run', final', answer⟩ := ScalarInstance.path_pair_iff.mp hc
  obtain ⟨ts, typed, fi, hfi⟩ := ScalarInstance.invoke_typed hs.2 f
  have matching : Simulation.Matching .same ((S.sharedI.initThread f).config s)
      ((S.linkedI.initThread f).config s') := Simulation.Matching.invoke hs.1 hfi f.2.1
  obtain ⟨⟨s₁, t₁⟩, run, final, hm⟩ :=
    hrev (x := (s, S.sharedI.initThread f)) (x' := (s', S.linkedI.initThread f))
      (ts := ts) typed matching run' final'
  have hc' : S.sharedI.Path P (.idle s) [.inr (.ask f), .inr (.ans f v)] (.idle s₁) :=
    ScalarInstance.path_pair_iff.mpr ⟨t₁, r, run, final, answer⟩
  refine ⟨s₁, hc', ?_,
    (ScalarInstance.WellFormed.activation hs.2 (fun e => Fin.elim0 e.1) hc').1⟩
  have hst := hm.stores
  rwa [Thread.config_store, Thread.config_store] at hst

/-- Forward transfer of plays between related stores. -/
theorem plays_transfer {P : Profile} :
    ∀ (p : List (Move S.sharedI.E S.sharedI.F)) {s s' : Store Nat}, S.Persistent s s' →
      p ∈ S.sharedI.plays P s → p ∈ S.linkedI.plays P s'
  | [], _, _, _, _ => ⟨_, .nil _⟩
  | [_], _, s', _, ⟨_, hp⟩ => by
    cases hp with
    | cons h1 h2 =>
      cases h1
      exact ⟨_, .cons (.call s' _) (.nil _)⟩
  | _ :: _ :: rest, _, _, hs, ⟨q, hp⟩ => by
    obtain ⟨f, v, s₁, rfl, rfl, hc, hrest⟩ :=
      ScalarInstance.path_cons_cons_closed (I := S.sharedI) rfl hp
    obtain ⟨s₁', hc', hs₁⟩ := S.activation_transfer hs hc
    exact ScalarInstance.append_mem_plays_of (c := [_, _]) hc' (plays_transfer rest hs₁ ⟨q, hrest⟩)

/-- Reverse transfer of plays between related stores. -/
theorem plays_reflect {P : Profile} (hrev : ReachReverse P) :
    ∀ (p : List (Move S.linkedI.E S.linkedI.F)) {s s' : Store Nat}, S.Persistent s s' →
      p ∈ S.linkedI.plays P s' → p ∈ S.sharedI.plays P s
  | [], _, _, _, _ => ⟨_, .nil _⟩
  | [_], s, _, _, ⟨_, hp⟩ => by
    cases hp with
    | cons h1 h2 =>
      cases h1
      exact ⟨_, .cons (.call s _) (.nil _)⟩
  | _ :: _ :: rest, _, _, hs, ⟨q, hp⟩ => by
    obtain ⟨f, v, s₁', rfl, rfl, hc, hrest⟩ :=
      ScalarInstance.path_cons_cons_closed (I := S.linkedI) rfl hp
    obtain ⟨s₁, hc', hs₁⟩ := S.activation_reflect hrev hs hc
    exact ScalarInstance.append_mem_plays_of (c := [_, _]) hc'
      (plays_reflect hrev rest hs₁ ⟨q, hrest⟩)

/-- **(A), forward, every profile.** Every play of the shared world is a play of the linked
module. -/
theorem shared_plays_subset_linked (hS : S.Scalar) (P : Profile) :
    S.sharedI.plays P S.sc ⊆ S.linkedI.plays P S.sl :=
  fun p => S.plays_transfer p (S.persistent_initial hS)

/-- **(A), every profile, given the reverse simulation.** The linked module and the shared
world have the same plays, over any number of export calls. -/
theorem linked_plays_eq_shared_of (hS : S.Scalar) {P : Profile} (hrev : ReachReverse P) :
    S.linkedI.plays P S.sl = S.sharedI.plays P S.sc :=
  Set.ext fun p => ⟨S.plays_reflect hrev p (S.persistent_initial hS),
    S.plays_transfer p (S.persistent_initial hS)⟩

/-- **(A)** The linked module and the shared world have the same plays, over any number of
export calls (deterministic profiles). -/
theorem linked_plays_eq_shared (hS : S.Scalar) (o : GrowOracle) :
    S.linkedI.plays (profile o) S.sl = S.sharedI.plays (profile o) S.sc :=
  S.linked_plays_eq_shared_of hS (reachReverse_profile o)

/-- **(A)**, object form, forward, every profile. -/
theorem shared_objPlays_subset_linked (hS : S.Scalar) (P : Profile) :
    S.sharedI.objPlays P S.sc ⊆ S.linkedI.objPlays P S.sl :=
  Set.image_mono (S.shared_plays_subset_linked hS P)

/-- **(A)**, object form, every profile, given the reverse simulation. -/
theorem linked_objPlays_eq_shared_of (hS : S.Scalar) {P : Profile} (hrev : ReachReverse P) :
    S.linkedI.objPlays P S.sl = S.sharedI.objPlays P S.sc := by
  unfold ScalarInstance.objPlays
  rw [S.linked_plays_eq_shared_of hS hrev]
  rfl

/-- **(A)**, object form (deterministic profiles). -/
theorem linked_objPlays_eq_shared (hS : S.Scalar) (o : GrowOracle) :
    S.linkedI.objPlays (profile o) S.sl = S.sharedI.objPlays (profile o) S.sc :=
  S.linked_objPlays_eq_shared_of hS (reachReverse_profile o)

end Setup

end Linking

end Silmaril.Wasm.Game
