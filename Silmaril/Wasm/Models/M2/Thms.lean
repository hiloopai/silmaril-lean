module

public import Silmaril.Wasm.Models.M2.Defs
public import Silmaril.Wasm.Models.Game.Thms
public import Mathlib.Data.List.Forall2

/-!
# The stateful game reading (M2) and the observation strategies: theorems

* `callPlay_stateful_iff`: a first call of the stateful reading answered `b` is exactly a
  terminating observation `b` of the game chart;
* `callPlay_strat_iff_stateful`: **the fresh observation strategy carried by `Emb.ginstCoHom` and
  the stateful M2 reading agree on first calls** (terminating answers);
* `stateful_after_iff`: **the stateful reading after an answered call** is the stateful reading
  at the store left by some Core run of that call (every profile, from `closedWith_after_iff`);
  later calls are therefore not read at a fresh point;
* `m2_reduct_eq`: at deterministic profiles the reduct of the Core observation strategy along
  `m2EmbDet` is the observation strategy of the game chart (`Emb.reduct_eq`); `m2_le_reduct`:
  at every profile it refines it (`Emb.le_reduct`).
-/

@[expose] public section

namespace Silmaril.Wasm.Models.M2

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance}

/-- A legal play followed by a complete call is legal. -/
theorem legal_callPlay_append {C O : Type} {c : C} {o : O}
    {p : List (Move Sig.empty (callSig C O))} :
    Legal (callPlay c o ++ p) ↔ Legal p := by
  have hc : Path (.idle : Pos Sig.empty (callSig C O)) (callPlay c o) .idle :=
    .cons (Step.ask (E := Sig.empty) (F := callSig C O) c)
      (.cons (Step.ret (E := Sig.empty) (F := callSig C O) c o) (.nil _))
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, hp⟩ := Path.append_iff.1 hy
    cases Path.det hz hc
    exact ⟨y, hp⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hc.append hy⟩

/-- The preimages of a complete call under `toBeh`. -/
theorem upRel_callPlay_iff {f : I.F.Op} {b : Behaviour Val} {s : List (Move Sig.empty I.F)} :
    List.Forall₂ (UpRel (toBeh I)) s (callPlay f b) ↔
      ∃ w : I.F.Ar f, s = [.inr (.ask f), .inr (.ans f w)] ∧
        Answer.toBehaviour (ft := I.exports.get f.1) w = b := by
  constructor
  · intro h
    obtain _ | ⟨h₁, _ | ⟨h₂, h₃⟩⟩ := h
    cases h₃
    cases h₁ with
    | ask _ =>
      cases h₂ with
      | ans _ w => exact ⟨w, rfl, rfl⟩
  · rintro ⟨w, rfl, rfl⟩
    exact .cons (UpRel.ask (ρ := toBeh I) f) (.cons (UpRel.ans (ρ := toBeh I) f w) .nil)

/-- **The first calls of the stateful reading** are the terminating observations. -/
theorem callPlay_stateful_iff (P : Profile) (x : Atlas.Games.Pt I) (f : I.F.Op)
    (b : Behaviour Val) :
    callPlay f b ∈ statefulStrat P I x ↔ b ∈ Atlas.Games.obs P I x f ∧ b ≠ .diverges := by
  rw [statefulStrat, Strategy.mem_restrict_iff]
  constructor
  · rintro ⟨-, s, hs, hr⟩
    obtain ⟨w, rfl, rfl⟩ := upRel_callPlay_iff.1 hr
    exact ⟨.inl ⟨w, hs, rfl⟩, Result.toBehaviour_ne_diverges _⟩
  · rintro ⟨(⟨w, hw, rfl⟩ | ⟨rfl, -⟩), hb⟩
    · exact ⟨callPlay_legal f _, _, hw, upRel_callPlay_iff.2 ⟨w, rfl, rfl⟩⟩
    · exact absurd rfl hb

/-- **The fresh observation strategy and the stateful reading agree on first calls.** -/
theorem callPlay_strat_iff_stateful (P : Profile) (S : FeatureSet) (x : Atlas.Games.Pt I)
    (f : I.F.Op) {b : Behaviour Val} (hb : b ≠ .diverges) :
    callPlay f b ∈ (m2Model P I S).strat x ↔ callPlay f b ∈ statefulStrat P I x := by
  rw [callPlay_stateful_iff]
  exact ⟨fun h => ⟨mem_callPlay_iff.1 h, hb⟩, fun h => mem_callPlay_iff.2 h.1⟩

/-- **The stateful reading after an answered call** continues at the store left by some Core
run of that call. -/
theorem stateful_after_iff (P : Profile) (s : Store Nat) (K : Env I.E) (f : I.F.Op)
    (b : Behaviour Val) (p : List (Move Sig.empty (callSig I.F.Op (Behaviour Val)))) :
    callPlay f b ++ p ∈ statefulStrat P I (s, K) ↔
      ∃ (w : I.F.Ar f) (c' : Config Nat) (r : Result),
        Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
        c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        Answer.toBehaviour (ft := I.exports.get f.1) w = b ∧ p ∈ statefulStrat P I (c'.store, K) := by
  simp only [statefulStrat, Strategy.mem_restrict_iff, legal_callPlay_append]
  constructor
  · rintro ⟨hp, s', hs', hr⟩
    have h₁ := List.forall₂_take_append _ _ _ hr
    have h₂ := List.forall₂_drop_append _ _ _ hr
    obtain ⟨w, hw, rfl⟩ := upRel_callPlay_iff.1 h₁
    have hsplit : s' = [.inr (.ask f), .inr (.ans f w)] ++ s'.drop (callPlay f
        (Answer.toBehaviour (ft := I.exports.get f.1) w)).length := by
      rw [← hw, List.take_append_drop]
    rw [hsplit] at hs'
    obtain ⟨c', r, hrun, hfin, hres, hc'⟩ := (ScalarInstance.closedWith_after_iff _).1 hs'
    exact ⟨w, c', r, hrun, hfin, hres, rfl, hp, _, hc', h₂⟩
  · rintro ⟨w, c', r, hrun, hfin, hres, rfl, hp, s', hs', hr⟩
    refine ⟨hp, [.inr (.ask f), .inr (.ans f w)] ++ s',
      (ScalarInstance.closedWith_after_iff _).2 ⟨c', r, hrun, hfin, hres, hs'⟩, ?_⟩
    exact List.rel_append (upRel_callPlay_iff.2 ⟨w, rfl, rfl⟩) hr

/-- **At deterministic profiles the reduct of the Core observation strategy is the observation
strategy of the game chart.** -/
theorem m2_reduct_eq (o : GrowOracle) (S : FeatureSet) {x : Atlas.Games.Pt I}
    (hx : (m2Model (profile o) I S).dom x) :
    Game.reduct ((m2EmbDet o I S).gameHom (m2TotalDet o I S))
        ((coreModel (profile o) Nat S).strat (Atlas.Games.corePt I x)) =
      (m2Model (profile o) I S).strat x :=
  (m2EmbDet o I S).reduct_eq (m2TotalDet o I S) rfl hx

/-- At every profile the observation strategy of the game chart refines the reduct of the Core
observation strategy. -/
theorem m2_le_reduct (P : Profile) (S : FeatureSet) {x : Atlas.Games.Pt I}
    (hx : (m2Model P I S).dom x) :
    (m2Model P I S).strat x ≤
      Game.reduct ((m2Emb P I S).gameHom ⟨fun b => b, fun _ => rfl⟩)
        ((coreModel P Nat S).strat (Atlas.Games.corePt I x)) :=
  (m2Emb P I S).le_reduct _ nofun hx

end Silmaril.Wasm.Models.M2
