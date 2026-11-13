module

public import Silmaril.Wasm.Models.V10Lime1.Defs

/-!
# The image of a 1.0 point of the domain lies in the domain of `lime1own`

* `storeWF_lime`: the Lime1 store of a 1.0 point of the domain is well formed for the Core
  simulation (`Lime1.Execution.StoreWF`): module functions are allocated (`ModsWF`), memories
  fit 32 bits (from `ToV2.StoreWF`);
* `gate_preserves`, `gate_keeps`: the gated host preserves `Lime1.Execution.StoreWF` with store
  extension, and keeps functions;
* **`ptL_dom`**.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10Lime1
open Silmaril.Wasm.Models.V10 (LStore LHost HostKeepsL)

variable {H : Type}

/-- The memory half of `Lime1.Execution.StoreWF` follows from `ToV2.StoreWF`. -/
theorem mems_of_toV2 {s : LStore H} (h : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF s) (i : Nat)
    (mi : MemInst) (hi : s.memories[i]? = some mi) :
    mi.data.size ≤ 2 ^ 32 ∧ ∀ j, mi.max = some j → j < 2 ^ 64 := by
  have hmem := List.mem_of_getElem? hi
  refine ⟨h.memSize mi hmem, fun j hj => ?_⟩
  have h32 : j < 2 ^ 32 := h.memMax mi hmem j (by simp [hj])
  omega

/-- The Lime1 store of a 1.0 point of the domain is well formed for the Core simulation. -/
theorem storeWF_lime {p : V10.Pt H} (hp : V10.dom p) :
    Silmaril.Wasm.Lime1.Execution.StoreWF (V10.limeStore p) := by
  refine ⟨fun i t m c hi => ?_, mems_of_toV2 hp.1⟩
  obtain ⟨f, hf, hfi⟩ : ∃ f, p.1.funcs[i]? = some f ∧
      FuncInst.mapCode Silmaril.Wasm.V1.Func.toLime f = .wasm t m c := by
    simpa [V10.limeStore, Store.mapCode] using hi
  intro a ha
  cases f with
  | wasm t' m' c' =>
    simp only [FuncInst.mapCode, FuncInst.wasm.injEq] at hfi
    obtain ⟨-, rfl, -⟩ := hfi
    simpa [V10.limeStore, Store.mapCode] using
      hp.2.2.2.2 _ (List.mem_of_getElem? hf) t' m' c' rfl a ha
  | host t' c' => simp [FuncInst.mapCode] at hfi

/-- **The gated host preserves the Core simulation's well-formedness**, with store extension. -/
theorem gate_preserves {src : LHost H}
    (hp : Silmaril.Wasm.Lime1.Execution.ToV2.HostPreserves src) (hk : HostKeepsL src) :
    Silmaril.Wasm.Lime1.Execution.HostPreserves (gate src) := by
  rintro h s args s' r ⟨hsrc, hv2⟩ ⟨hmods, -⟩
  have hfuncs : s'.funcs = s.funcs := hk h s args s' r hsrc
  have hv2' := hp h s args s' r hsrc hv2
  refine ⟨⟨fun i t m c hi => ?_, mems_of_toV2 hv2'⟩, ?_⟩
  · rw [hfuncs] at hi
    intro a ha
    rw [hfuncs]
    exact hmods i t m c hi a ha
  · unfold Silmaril.Wasm.Lime1.Execution.StoreExt
    rw [hfuncs]
    exact ListExt.refl _ _

/-- The gated host keeps functions. -/
theorem gate_keeps {src : LHost H} (hk : HostKeepsL src) : HostKeepsL (gate src) :=
  fun h s vs s' r hg => hk h s vs s' r hg.1

/-- **The image of a 1.0 point of the domain lies in the domain of `lime1own`.** -/
theorem ptL_dom {p : V10.Pt H} (hp : V10.dom p) : Lime1Core.dom (ptL p) :=
  ⟨storeWF_lime hp, gate_preserves hp.2.1 hp.2.2.1, gate_keeps hp.2.2.1⟩

end Silmaril.Proofs.Wasm.Models.V10Lime1
