module

public import Silmaril.Wasm.LimeCompile.PassiveData.Defs
public import Silmaril.Wasm.LimeCompile.Preserve.Thms

/-!
# The passive-data container: the compiled module

Static facts about `emuModule` and `compile`: what is kept (the export API and every
non-function section except data), where the helpers are, what `memory.init 0 y` becomes, and
code sizes.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.PassiveData

open Silmaril.Wasm Silmaril.Wasm.LimeCompile.PassiveData

theorem compile_eq_limeView (m : Module) : compile m = Silmaril.Wasm.LimeCompile.Preserve.limeView (emuModule m) := by
  unfold compile Silmaril.Wasm.LimeCompile.Preserve.limeView
  cases h : Lime1.Module.ofCore? (emuModule m) <;> cases Silmaril.Wasm.LimeCompile.Preserve.ElemsCanon (emuModule m) <;> rfl

theorem compile_toCore {m : Module} {L : Lime1.Module} (h : compile m = some L) :
    L.toCore = emuModule m :=
  Silmaril.Wasm.LimeCompile.Preserve.limeView_eq_some_iff.mp ((compile_eq_limeView m) ▸ h)

theorem helpers_getElem? (m : Module) (y : Nat) :
    (helpers m)[y]? = (m.data[y]?).map (helperFunc m y) := by
  unfold helpers
  rw [List.getElem?_map, List.zip_eq_zipWith, List.getElem?_zipWith]
  by_cases hy : y < m.data.length
  · simp [List.getElem?_range hy, List.getElem?_eq_getElem hy]
  · rw [List.getElem?_eq_none (by simpa using hy), List.getElem?_eq_none (by omega)]
    rfl

theorem helpers_length (m : Module) : (helpers m).length = m.data.length := by
  simp [helpers]

theorem rwL_length (base : Nat) : ∀ l : List Instr, (rwL base l).length = l.length
  | [] => by rw [rwL]
  | _ :: l => by rw [rwL, List.length_cons, List.length_cons, rwL_length base l]

theorem rwI_memoryInit (base : Nat) (y : DataIdx) :
    rwI base (.memoryInit (idx 0) y) = .call (idx (base + y.toNat)) := by
  rw [rwI]
  rfl

theorem chain_length : ∀ (bs : List UInt8) (k : Nat), (chain bs k).length = 5 * bs.length
  | [], _ => rfl
  | _ :: bs, k => by
    simp only [chain, List.length_append, List.length_cons, List.length_nil, chain_length bs (k + 1)]
    omega

theorem stepCode_length (bs : List UInt8) (h : Nat) :
    (stepCode bs h).length = 5 * bs.length + 13 := by
  simp only [stepCode, List.length_append, List.length_cons, List.length_nil, chain_length]
  omega

end Silmaril.Proofs.Wasm.LimeCompile.PassiveData
