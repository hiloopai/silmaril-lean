module

public import Silmaril.Wasm.Tools.Gen.Wit.Defs
public import Silmaril.Wasm.Tools.Gen.API.Thms
public import Silmaril.Wasm.Wit.Valid.Thms

/-!
# The WIT instance: restriction along the feature flags, shrinking

* the verified objects over `Defs`: `witCheck_iff`, `witLang F`, `emptyU_valid` (kernel
  evaluation of the checker), `witGen F`, `witMut F` (computing `witGenRun F`, `witMutRun F`:
  `witGen_run_eq`, `witMut_run_eq`);
* `universeInF_mono`: feature use is monotone in the flags;
* `witValid_mono`, `witGen_mono`: **a WIT generator of `F` is one of `G ≥ F`** (same outputs);
* `Mutator.restrictWit`: a mutator of `G` that keeps `F` universes inside `F` is one of `F`;
* `witShrink_spec`: checked shrinking keeps validity and the predicate, does not grow and ends
  in a local minimum.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Wit

open Silmaril.Wasm.Wit

/-! ## The verified objects -/

theorem witCheck_iff (F : WitFeat) (U : Universe) : witCheck F U = true ↔ WitValidIn F U := by
  rw [witCheck, Bool.and_eq_true, check_iff]
  rfl

/-- **The WIT language** of the flags `F`. -/
def witLang (F : WitFeat) : DecLang where
  Syn := Universe
  Valid := WitValidIn F
  check := witCheck F
  check_iff := witCheck_iff F

/-- The empty package is valid at every flag (kernel evaluation of the checker). -/
theorem emptyU_valid (F : WitFeat) : WitValidIn F emptyU :=
  ⟨check_iff.mp (by decide +kernel), rfl⟩

/-- **The WIT generator** of the flags `F`, checked (fallback: the empty package). -/
def witGen (F : WitFeat) : Generator (witLang F).toLang :=
  Generator.guarded (witLang F) (fun r n => Rand.run (Raw.univ F n) r) emptyU (emptyU_valid F)

/-- **The WIT mutator**, checked. -/
def witMut (F : WitFeat) : Mutator (witLang F).toLang :=
  Mutator.guarded (witLang F) (Raw.mutate F)

theorem witGen_run_eq (F : WitFeat) : (witGen F).run = witGenRun F := rfl

theorem witMut_run_eq (F : WitFeat) : (witMut F).run = witMutRun F := rfl

/-! ## Restriction and shrinking -/

variable {F G : WitFeat}

theorem flag_mono {x y z : Bool} (h₁ : (!x || y) = true) (h₂ : y = true → z = true) :
    (!x || z) = true := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- `leB` is monotone in its right argument. -/
theorem leB_mono {a : WitFeat} (h : F.le G) (ha : a.leB F = true) : a.leB G = true := by
  simp only [WitFeat.leB, Bool.and_eq_true] at ha ⊢
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := ha
  exact ⟨⟨⟨⟨flag_mono h₁ h.1, flag_mono h₂ h.2.1⟩, flag_mono h₃ h.2.2.1⟩,
    flag_mono h₄ h.2.2.2.1⟩, flag_mono h₅ h.2.2.2.2⟩

/-- Feature use is monotone in the flags. -/
theorem universeInF_mono (h : F.le G) (U : Universe) :
    universeInF F U = true → universeInF G U = true :=
  leB_mono h

/-- Validity is monotone in the flags. -/
theorem witValid_mono (h : F.le G) {U : Universe} (hU : WitValidIn F U) : WitValidIn G U :=
  ⟨hU.1, universeInF_mono h U hU.2⟩

/-- **A WIT generator of `F` is one of `G ≥ F`** with the same outputs. -/
def witGen_mono (h : F.le G) (g : Generator (witLang F).toLang) : Generator (witLang G).toLang :=
  g.mapValid id fun _ hU => witValid_mono h hU

/-- **A mutator of `G` that keeps `F` universes inside `F` is a mutator of `F`.** -/
def _root_.Silmaril.Wasm.Tools.Gen.Mutator.restrictWit (h : F.le G) (μ : Mutator (witLang G).toLang)
    (hF : ∀ r U, universeInF F U = true → universeInF F (μ.run r U) = true) :
    Mutator (witLang F).toLang where
  run := μ.run
  valid r U hU := ⟨(μ.valid r U (witValid_mono h hU)).1, hF r U hU.2⟩

/-- **Checked WIT shrinking.** -/
theorem witShrink_spec (F : WitFeat) (p : Universe → Bool) {U : Universe} (hv : WitValidIn F U)
    (hp : p U = true) :
    let U' := witShrinker.shrink (fun x => witCheck F x && p x) U
    WitValidIn F U' ∧ p U' = true ∧ Raw.size U' ≤ Raw.size U ∧
      ∀ c ∈ Raw.cands U', Raw.size c < Raw.size U' → (witCheck F c && p c) = false := by
  obtain ⟨h₁, h₂⟩ := Shrinker.shrink_valid (witLang F) witShrinker p hv hp
  exact ⟨h₁, h₂, witShrinker.shrink_size_le _ U, witShrinker.shrink_local_min _ U⟩

end Silmaril.Wasm.Tools.Gen.Wit
