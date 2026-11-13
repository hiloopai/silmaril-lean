module

public import Silmaril.Wasm.Institution.GameInstMaps.Defs
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Games.Institution.Thms
public import Silmaril.Wasm.Behaviour.Adapters.Core

/-!
# Scalar Wasm instances in the institution of game semantics: M2

`m2_answers_iff`: **M2 read in `GInst`**. For a well-formed instance and a strategy-definable
host, a terminating closed-world behaviour `b` of an export call `f` is exactly the reading of
an answer `w` such that the `◇` sentence "`f` may be answered `w`" holds of the closed program
`K.strategy ≫ I.strategy P s` (which is `GInst`'s composition). This is `adequacy_answers` with
`Responds` unfolded to `GSen.diaPlay`.

`m2_diverges_iff`: divergence is observed exactly when no such `◇` sentence holds and the
invocation has an infinite run (`adequacy_profile`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.GameInstMaps

open Silmaril.Games (GSen Move Sig)
open Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance}

/-- **M2 in `GInst`, terminating behaviours.** -/
theorem m2_answers_iff {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) (b : Behaviour Val) (hb : b ≠ .diverges) :
    b ∈ behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 ↔
      ∃ w, (GSen.diaPlay [.inr (.ask f), .inr (.ans f w)]).holds (I.closedWith P s K) ∧
        b = Answer.toBehaviour (ft := I.exports.get f.1) w := by
  rw [ScalarInstance.adequacy_answers hw K hK f b hb]
  constructor
  · rintro (⟨w, hw', rfl⟩ | ⟨rfl, -⟩)
    · exact ⟨w, GSen.holds_diaPlay.mpr hw', rfl⟩
    · exact absurd rfl hb
  · rintro ⟨w, hw', rfl⟩
    exact Or.inl ⟨w, GSen.holds_diaPlay.mp hw', rfl⟩

/-- **M2 in `GInst`, divergence**: `diverges` is a behaviour iff no answer `◇` sentence holds
of the closed program, or the invocation has an infinite run. -/
theorem m2_diverges_iff {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    Behaviour.diverges ∈ behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 ↔
      (∀ w, ¬ (GSen.diaPlay [.inr (.ask f), .inr (.ans f w)]).holds (I.closedWith P s K)) ∨
        Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) := by
  rw [ScalarInstance.adequacy_profile hw K hK f]
  constructor
  · rintro ((⟨w, -, hw'⟩ | ⟨-, hno⟩) | ⟨-, hd⟩)
    · exact absurd hw'.symm (Result.toBehaviour_ne_diverges _)
    · exact Or.inl fun w h => hno w (GSen.holds_diaPlay.mp h)
    · exact Or.inr hd
  · rintro (hno | hd)
    · exact Or.inl (Or.inr ⟨rfl, fun w h => hno w (GSen.holds_diaPlay.mpr h)⟩)
    · exact Or.inr ⟨rfl, hd⟩

end Silmaril.Wasm.Institution.GameInstMaps
