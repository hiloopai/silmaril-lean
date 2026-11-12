module

public import Silmaril.Wasm.FnInst.Comor.Defs
public import Silmaril.Logic.Inst.Thms

/-!
# Model expansion and borrowing for the focus comorphisms

`oneToSet`, `setToAll`, `holeToAll` and `oneToAll` are the identity on handlers, so they are
model-expansive, and a sentence is valid in the source institution iff its translation is
valid in the target (`*_valid_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

open CategoryTheory Silmaril.Inst

variable (L : Lang) (W : Type)

theorem oneToSet_modelExpansive : (oneToSet L W).ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem setToAll_modelExpansive : (setToAll L W).ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem holeToAll_modelExpansive : (holeToAll L W).ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem oneToAll_modelExpansive : (oneToAll L W).ModelExpansive :=
  Comorphism.ModelExpansive.comp (oneToSet_modelExpansive L W) (setToAll_modelExpansive L W)

/-- Satisfaction in the one-function institution, unfolded. -/
theorem one_sat_iff (S : OneSig) (h : Handler L W S.C) (φ : (oneInst L W).Sen S) :
    h ⊨[oneInst L W] φ ↔ Formula.Holds (FnAtom.Holds (fun _ => S.f) h) φ :=
  Iff.rfl

/-- Satisfaction in the hole institution, unfolded. -/
theorem hole_sat_iff (S : HoleSig) (h : Handler L W S.C) (φ : (holeInst L W).Sen S) :
    h ⊨[holeInst L W] φ ↔ Formula.Holds (fun p => SegEq h S.ty p.1 p.2) φ :=
  Iff.rfl

/-- Satisfaction in the all-function institution, unfolded. -/
theorem all_sat_iff (C : Ctx) (h : Handler L W C) (φ : (allInst L W).Sen C) :
    h ⊨[allInst L W] φ ↔ Formula.Holds (FnAtom.Holds id h) φ :=
  Iff.rfl

theorem oneToAll_valid_iff (S : OneSig) (φ : (oneInst L W).Sen S) :
    (oneInst L W).Valid φ ↔ (allInst L W).Valid ((oneToAll L W).sen S φ) :=
  (oneToAll L W).valid_iff (oneToAll_modelExpansive L W) φ

theorem holeToAll_valid_iff (S : HoleSig) (φ : (holeInst L W).Sen S) :
    (holeInst L W).Valid φ ↔ (allInst L W).Valid ((holeToAll L W).sen S φ) :=
  (holeToAll L W).valid_iff (holeToAll_modelExpansive L W) φ

end Silmaril.Wasm.FnInst
