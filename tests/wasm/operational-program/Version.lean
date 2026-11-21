module

import Silmaril.Wasm.Execution.Core.Entry.Program.Versions.Thms
import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Entry Silmaril.Wasm.SingleThreaded Silmaril.Semantics.Operational
open Silmaril.Wasm.V1.Intrinsic.Scalar

private def sig : V1.FuncType := ⟨[.i32], [.i32]⟩
private def module_ : ClosedModule sig where
  exportName := "plusSeven"
  fn := {
    resolved := rfl
    singleResult := Nat.le_refl 1
    locals := []
    body := .step [] (.localGet ⟨0⟩ rfl) <|
      .step [.i32] (.intConst .i32 7) <|
      .step [] (.intBinOp .i32 .add) (.nil [.i32]) }

private def store : Store Unit := {}
private theorem storeOk : StoreOk store := by constructor <;> simp [store]
private def model := ((rawModule (Profile.spec false) divHost).precompose
    (fun mod : V1.Module => ⟨store, mod.toCore, []⟩)).precompose (ClosedModule.erase (sig := sig))

private def interface : CModuleType := (validate? module_.toCore).get (by decide +kernel)
private def allocated : Config Unit := (instantiate? evalConst? store module_.toCore []).getD ⟨{}, {}, []⟩
private theorem initialized : Instantiate (Profile.spec false) divHost store module_.toCore [] allocated :=
  (instantiate?_iff ⟨interface.exports, [], validate?_sound rfl, .nil⟩).mp rfl

example : model.May module_ (.returned (.ok [])) := by
  change (((rawModule (Profile.spec false) divHost).precompose (fun mod : V1.Module => ⟨store, mod.toCore, []⟩)).precompose
    (ClosedModule.erase (sig := sig))).May module_ _
  rw [wasm1Scalar_core_entry]
  exact ⟨allocated, initialized, allocated, .refl, Instantiate.ok divHost_ok storeOk initialized, .values [], rfl, rfl⟩

#print axioms wasm1Scalar_core_entry
