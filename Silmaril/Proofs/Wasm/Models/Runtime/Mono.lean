module

public import Silmaril.Proofs.Wasm.Models.Runtime.Basic
public import Silmaril.Wasm.Models.Syntax.Thms

/-!
# The runtime invariant is monotone in the feature set

`instrB_mono`, `codeIn_mono`, `storeIn_mono`: runtime code and stores of `S` are runtime code
and stores of every `T ≥ S`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Rt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models Silmaril.Wasm.Models.Rt

variable {S T : FeatureSet}

theorem bor_mono {a b a' b' : Bool} (h₁ : a = true → a' = true) (h₂ : b = true → b' = true)
    (h : (a || b) = true) : (a' || b') = true := by
  cases a <;> cases b <;> simp_all

theorem band_mono {a b a' b' : Bool} (h₁ : a = true → a' = true) (h₂ : b = true → b' = true)
    (h : (a && b) = true) : (a' && b') = true := by
  cases a <;> cases b <;> simp_all

theorem instrB_mono (h : S ≤ T) (i : Instr) (hs : instrB S i = true) : instrB T i = true := by
  have hc : ∀ c, S.has c = true → T.has c = true := le_iff.mp h
  have hi : ∀ i, Instr.inFeatB S i = true → Instr.inFeatB T i = true := inFeatB_mono h
  cases i
  case callRef y => exact bor_mono (hi _) (hc _) hs
  case returnCallRef y => exact bor_mono (hi _) (band_mono (hc _) (hc _)) hs
  case refCast rt => exact bor_mono (hi _) (hc _) hs
  case tableGet x => exact bor_mono (hi _) (band_mono (bor_mono (hc _) (hc _)) (tblIdx_mono h _)) hs
  case tableSet x => exact bor_mono (hi _) (band_mono (hc _) (tblIdx_mono h _)) hs
  all_goals simp_all [instrB]

theorem codeIn_mono (h : S ≤ T) (l : List Admin) (hs : CodeIn S l) : CodeIn T l := by
  have hc := le_iff.mp h
  have hi := instrB_mono h
  have hb := insInFeatB_mono h
  revert hs
  induction l using Admin.rec_1 (motive_1 := fun a => AdmIn S a → AdmIn T a)
  all_goals simp_all [AdmIn, CodeIn]

theorem storeIn_mono {H : Type} (h : S ≤ T) {s : Store H} (hs : StoreIn S s) : StoreIn T s :=
  fun a fi fn ha hf => insInFeatB_mono h _ (hs a fi fn ha hf)

end Silmaril.Proofs.Wasm.Models.Rt
