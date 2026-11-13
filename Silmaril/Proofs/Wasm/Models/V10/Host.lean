module

public import Silmaril.Wasm.Models.V10.Defs

/-!
# The induced 2.0 host of a Lime1 host

* `compatL`: `ToV2.HostCompatible src (liftHostL src)` for a Lime1 host that preserves the
  simulation's store invariant, keeps functions and preserves `MemTabWF` of the 2.0 image;
* `keepsV`, `preservesV`: the induced host keeps functions and preserves 2.0's `StoreWF`
  (with `StoreExt`), so 2.0 points built from it lie in the domain of `v20own`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10
open Silmaril.Wasm.Models.V2Core (VStore VHost)
open Silmaril.Wasm.Lime1.Execution.ToV2 (Store.erase)

variable {H : Type}

/-- The memories and tables of a 2.0 store are those of its erasure. -/
theorem memTab_erase {sV : VStore H} : MemTabWF (Store.erase sV) ↔ MemTabWF sV := Iff.rfl

/-- `MemTabWF` is the memory and table part of 2.0's `StoreWF`. -/
theorem memTab_of_storeWF {sV : VStore H} (h : Silmaril.Wasm.V2.Execution.StoreWF sV) :
    MemTabWF sV := h.2

/-- The 2.0 image of the returned store with the old functions. -/
theorem erase_withFuncs {s s' : LStore H} {sV : VStore H} (hf : s'.funcs = s.funcs)
    (hE : Store.erase sV = s.toV2) :
    Store.erase { s'.toV2 with funcs := sV.funcs } = s'.toV2 := by
  have h₁ := Silmaril.Wasm.Lime1.Execution.ToV2.erase_funcs hE
  have h₂ := Silmaril.Wasm.Lime1.Execution.ToV2.Store.erase_toV2 s'
  have h₄ : (s'.toV2.funcs.map fun fi => { fi with
      module := Silmaril.Wasm.Lime1.Execution.ToV2.ModuleInst.erase fi.module }) =
      s'.funcs.map FuncInst.toV2 := by
    have h := congrArg Silmaril.Wasm.V2.Execution.Store.funcs h₂
    simp only [Store.erase] at h
    exact h
  have h₃ : (Store.erase { s'.toV2 with funcs := sV.funcs }) = Store.erase s'.toV2 := by
    simp only [Store.erase]
    rw [h₁, ← hf, h₄]
  rw [h₃, h₂]

/-- The returned store keeps 2.0's `StoreWF`. -/
theorem storeWF_withFuncs {src : LHost H} (hw : HostPreservesW src) {h : H} {s s' : LStore H}
    {vs : List Value} {r : Result} (hsrc : src h s vs (.returned s' r)) {sV : VStore H}
    (hE : Store.erase sV = s.toV2) (hwf : Silmaril.Wasm.V2.Execution.StoreWF sV) :
    Silmaril.Wasm.V2.Execution.StoreWF { s'.toV2 with funcs := sV.funcs } := by
  have hm : MemTabWF s.toV2 := hE ▸ (memTab_erase.mpr (memTab_of_storeWF hwf))
  have hm' : MemTabWF s'.toV2 := hw h s vs s' r hsrc hm
  exact ⟨hwf.1, hm'⟩

/-- The induced host matches every behaviour of the Lime1 host. -/
theorem liftL_matches {src : LHost H} (hk : HostKeepsL src) (hw : HostPreservesW src) {h : H}
    {s : LStore H} {vs : List Value} {out : HostOutcome Silmaril.Wasm.Lime1.Func H}
    {sV : VStore H} (hsrc : src h s vs out) (hE : Store.erase sV = s.toV2) :
    ∃ out', liftHostL src h sV (vs.map Value.toV2) out' ∧
      Silmaril.Wasm.Lime1.Execution.ToV2.HostOutcomeSim out out' := by
  cases out with
  | diverged => exact ⟨.diverged, ⟨s, vs, hE, rfl, Or.inl ⟨hsrc, rfl⟩⟩, trivial⟩
  | returned s' r =>
    have hf : s'.funcs = s.funcs := hk h s vs s' r hsrc
    have he := erase_withFuncs hf hE
    exact ⟨.returned { s'.toV2 with funcs := sV.funcs } r.toV2,
      ⟨s, vs, hE, rfl, Or.inr ⟨s', r, _, hsrc, rfl, he, rfl, storeWF_withFuncs hw hsrc hE⟩⟩,
      he, rfl⟩

/-- **The induced 2.0 host is compatible with the Lime1 host.** -/
theorem compatL {src : LHost H} (hp : Silmaril.Wasm.Lime1.Execution.ToV2.HostPreserves src)
    (hk : HostKeepsL src) (hw : HostPreservesW src) :
    Silmaril.Wasm.Lime1.Execution.ToV2.HostCompatible src (liftHostL src) :=
  ⟨hp, fun _ _ _ _ _ hsrc hE => liftL_matches hk hw hsrc hE⟩

/-- The induced host keeps functions. -/
theorem keepsV (src : LHost H) : V2Core.HostKeepsV (liftHostL src) := by
  rintro h sV args sV' r ⟨s, vs, -, -, ⟨-, hout⟩ | ⟨s', r', sV'', -, hout, -, hfun, -⟩⟩
  · cases hout
  · cases hout
    exact hfun

/-- The induced host preserves 2.0's store invariant. -/
theorem preservesV (src : LHost H) :
    Silmaril.Wasm.V2.Execution.HostPreserves (liftHostL src) := by
  rintro h sV args sV' r ⟨s, vs, -, -, ⟨-, hout⟩ | ⟨s', r', sV'', -, hout, -, hfun, hwf⟩⟩ hpre
  · cases hout
  · cases hout
    refine ⟨hwf hpre, ?_⟩
    rw [Silmaril.Wasm.V2.Execution.StoreExt, hfun]
    exact Silmaril.ListExt.refl _ _

end Silmaril.Proofs.Wasm.Models.V10
