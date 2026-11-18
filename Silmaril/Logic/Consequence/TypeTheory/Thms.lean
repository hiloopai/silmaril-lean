module

public import Silmaril.Logic.Consequence.TypeTheory.Defs
public import Silmaril.Logic.Consequence.Institution.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic.Thms
public import Silmaril.Logic.Consequence.Thms
public import Silmaril.Logic.Consequence.Soundness.Defs
public import Silmaril.Logic.Concrete.Codec.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Soundness.Thms
import Silmaril.Proofs.Logic.Consequence.TypeTheory.Basic

/-!
# Martin-Löf type theories as consequence systems: laws and soundness

* `extensionalDerives_closed`, `intensionalDerives_closed`, `lambdaPiDerives_closed` and the
  semantic `…Entails_closed`: identity, weakening and cut on judgment hypotheses.
* The extensional systems are pullbacks along `ULift.up`, which keep these laws
  (`Proofs.Logic.Consequence.TypeTheory.closed_pullback_map`).
* `bounded_soundFor` (and `…_one`, `…_two`, `…_three`): bounded extensional MLTT is sound for its
  finite-tower interpretation (`boundedTowers`); `bounded_empty_consistent_one/two/three`: it does
  not derive `⊢ 0 : 𝟘`. `boundedCodec`: bounded judgments as S-expressions; `bounded_zero_derived`
  and `bounded_zero_true`: `⊢ 0 : ℕ` is derived and holds in every tower.
* `extensionalDerives_le_entails` (from `ExtensionalMLTT.Institution.logic_sound`) and
  `intensionalDerives_le_entails` (from `IntensionalMLTT.OriginalInstitution.logic_sound`):
  soundness. Completeness is not claimed.
-/

@[expose] public section

namespace Silmaril.Consequence.TypeTheory

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution Silmaril.Logic.TypeTheory

universe u

theorem extensionalDerives_closed :
    Structural.Closed Structural.tarskiRules extensionalDerives :=
  Proofs.Logic.Consequence.TypeTheory.closed_pullback_map ULift.up
    (listSys_closed (ExtensionalMLTT.Institution.logic.{0}.er ⟨⟨⟩⟩))

theorem extensionalEntails_closed :
    Structural.Closed Structural.tarskiRules extensionalEntails.{u} :=
  Proofs.Logic.Consequence.TypeTheory.closed_pullback_map ULift.up
    (roomSeq_closed ExtensionalMLTT.Institution.room.{u})

/-- **Soundness of extensional MLTT** for set hierarchies (in universe `0`). -/
theorem extensionalDerives_le_entails : extensionalDerives ≤ extensionalEntails.{0} :=
  System.pullback_mono _ _ (listSys_le_roomSeq ExtensionalMLTT.Institution.logic_sound ⟨⟨⟩⟩)

theorem intensionalDerives_closed (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    Structural.Closed Structural.tarskiRules (intensionalDerives stage) :=
  listSys_closed ((IntensionalMLTT.OriginalInstitution.logic stage).er ⟨⟨⟩⟩)

theorem intensionalEntails_closed (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    Structural.Closed Structural.tarskiRules (intensionalEntails stage) :=
  roomSeq_closed (IntensionalMLTT.OriginalInstitution.room stage)

/-- **Soundness of intensional MLTT** for realizability, at every stage. -/
theorem intensionalDerives_le_entails (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    intensionalDerives stage ≤ intensionalEntails stage :=
  listSys_le_roomSeq (IntensionalMLTT.OriginalInstitution.logic_sound stage) ⟨⟨⟩⟩

theorem lambdaPiDerives_closed (C : LambdaPi.Calculus) :
    Structural.Closed Structural.tarskiRules (lambdaPiDerives C) :=
  listSys_closed (C.logic.er ⟨⟨⟩⟩)

/-! ## Consistency (nontriviality) of the supported variants -/

/-- Closure nontriviality of a logic's entailment relation at a signature is nontriviality of its
list-premise consequence system from no premises. -/
theorem listSys_contextConsistent.{u₁, v₁, w₁, m₁, m₂} {Sign : Type u₁} [Category.{v₁} Sign]
    {L : Metatheory.LogicalSystem.{u₁, v₁, w₁, m₁, m₂} Sign} {S : Sign} (h : (L.er S).Consistent ∅) :
    (LogicalSystem.listSys L S).ContextConsistent [] := by
  intro hall
  obtain ⟨φ, hφ⟩ := h
  exact hφ ((L.er S).mono (fun x hx => absurd hx (List.not_mem_nil (a := x))) (hall φ))

/-- **Extensional MLTT with one universe level is consistent** (some judgment is not derivable),
relative to Lean and the one-level ZFSet tower at universe 1. -/
theorem bounded_consistent_one : (boundedDerives.{1} 1).ContextConsistent [] :=
  listSys_contextConsistent ExtensionalMLTT.Finite.logic_consistent_one.{0}

/-- **Two universe levels** (the tower at universe 2). -/
theorem bounded_consistent_two : (boundedDerives.{2} 2).ContextConsistent [] :=
  listSys_contextConsistent ExtensionalMLTT.Finite.logic_consistent_two.{0}

/-- **Three universe levels** (the tower at universe 3). -/
theorem bounded_consistent_three : (boundedDerives.{3} 3).ContextConsistent [] :=
  listSys_contextConsistent ExtensionalMLTT.Finite.logic_consistent_three.{0}

/-- **Intensional MLTT (original rules, J, unbounded cumulative universes) is consistent** at
every stage, by term realizability. -/
theorem intensional_consistent (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    (intensionalDerives stage).ContextConsistent [] :=
  listSys_contextConsistent (IntensionalMLTT.OriginalInstitution.logic_consistent stage)

/-! ## Bounded extensional MLTT: soundness for its finite towers -/

/-- **Bounded extensional MLTT is sound for its finite-tower interpretation**, at every number of
universe levels and in every Lean universe. -/
theorem bounded_soundFor (levels : ℕ) :
    (boundedDerives.{u} levels).SoundFor (boundedTowers.{u} levels) :=
  listSys_le_roomSeq (ExtensionalMLTT.Finite.logic_sound levels) _

/-- **One universe level**, interpreted in towers at Lean universe 1. -/
theorem bounded_soundFor_one : (boundedDerives.{1} 1).SoundFor (boundedTowers.{1} 1) :=
  bounded_soundFor 1

/-- **Two universe levels**, at Lean universe 2. -/
theorem bounded_soundFor_two : (boundedDerives.{2} 2).SoundFor (boundedTowers.{2} 2) :=
  bounded_soundFor 2

/-- **Three universe levels**, at Lean universe 3. -/
theorem bounded_soundFor_three : (boundedDerives.{3} 3).SoundFor (boundedTowers.{3} 3) :=
  bounded_soundFor 3

/-- **`⊢ 0 : 𝟘` is not derivable with one universe level** (no inhabitant of the empty type). -/
theorem bounded_empty_consistent_one :
    (boundedDerives.{1} 1).ConsistentWrt (ExtensionalMLTT.Finite.emptySentence 1) [] :=
  Proofs.Logic.Consequence.TypeTheory.bounded_empty_consistent 1

/-- With two universe levels. -/
theorem bounded_empty_consistent_two :
    (boundedDerives.{2} 2).ConsistentWrt (ExtensionalMLTT.Finite.emptySentence 2) [] :=
  Proofs.Logic.Consequence.TypeTheory.bounded_empty_consistent 2

/-- With three universe levels. -/
theorem bounded_empty_consistent_three :
    (boundedDerives.{3} 3).ConsistentWrt (ExtensionalMLTT.Finite.emptySentence 3) [] :=
  Proofs.Logic.Consequence.TypeTheory.bounded_empty_consistent 3

/-- **Bounded judgments as S-expressions** (`silmaril.mltt.judgment.bounded`, v1): the judgment
syntax `silmaril.mltt.judgment`, accepting only judgments whose universes are below `levels`. -/
def boundedCodec (levels : ℕ) : Concrete.SExpCodec (ExtensionalMLTT.Finite.Sentence levels) :=
  .ofReader "silmaril.mltt.judgment.bounded" "1" (fun j => ExtensionalMLTT.SExp.codec.encode j.1)
    (fun e => (ExtensionalMLTT.SExp.codec.decode e).bind fun j =>
      if h : j.universeBound ≤ levels then some ⟨j, h⟩ else none)
    (fun ⟨j, h⟩ => by
      simp [Concrete.SExpCodec.decode_encode, show j.universeBound ≤ levels from h])

/-- **`⊢ 0 : ℕ` with one universe level**: derived by the bounded rules. -/
theorem bounded_zero_derived : boundedDerives.{1} 1 [] (ExtensionalMLTT.Finite.zeroSentence 1) :=
  (ExtensionalMLTT.Finite.logic.{1} 1).mono _ (Set.empty_subset _)
    (ExtensionalMLTT.Finite.zero_derivable 1)

/-- **`⊢ 0 : ℕ` holds in every tower** of one universe level. -/
theorem bounded_zero_true :
    ∀ m, (boundedTowers.{1} 1).satC m (ExtensionalMLTT.Finite.zeroSentence 1) :=
  fun m => bounded_soundFor_one [] _ bounded_zero_derived m (fun _ h => nomatch h)

end Silmaril.Consequence.TypeTheory
