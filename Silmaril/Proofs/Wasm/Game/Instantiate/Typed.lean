module

public import Silmaril.Proofs.Wasm.Game.Instantiate.Basic

/-!
# Instantiation against typed imports is typed: proofs

`instantiateOnce?_configOk`: the typing of `instantiateOnce?`'s preparation
(`prepare?_globalResidue_ok`, `Silmaril.Proofs.Wasm.Game.Instantiate.Residue`) carried along the
segment initialisation (`instantiateOnce?_steps`, `Steps.withStart`, `steps_configOk`), for any
well-typed store, any imports of the right types and any start function.
`importStore_nil_ok`: the empty store is typed.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Proofs.Wasm.Game.InstantiateAux
  Silmaril.Wasm.SingleThreaded

/-- The empty store of `importStore []` is well typed. -/
theorem importStore_nil_ok : StoreOk (importStore []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [importStore]

/-- **Instantiation against typed imports is typed.** -/
theorem instantiateOnce?_configOk {s : Store Nat} {m : Module} {xas : List ExternAddr}
    {mt : CModuleType} {s' : Store Nat} {f : Frame} {st : Option FuncIdx} (hs : StoreOk s)
    (hm : ModuleOk m mt) (hx : List.Forall₂ (ExternAddrOk s) xas mt.imports)
    (h : instantiateOnce? s m xas = some (s', f, st)) :
    ConfigOk ⟨s', f, startCode st⟩ [] := by
  obtain ⟨s₁, f₁, vs, c, hg, hp, hS⟩ := instantiateOnce?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail) (host := SingleThreaded.divHost) h
  obtain ⟨hc, -⟩ := prepare?_globalResidue_ok (P := SingleThreaded.profile SingleThreaded.neverFail)
    SingleThreaded.divHost_ok hs ⟨mt.exports, mt.imports, hm, hx⟩ hg hp
  have hS₂ := Steps.withStart (st := st) hS
  rw [Config.withStart_nil] at hS₂
  exact steps_configOk SingleThreaded.divHost_ok hc hS₂

end Silmaril.Proofs.Wasm.Game

end
