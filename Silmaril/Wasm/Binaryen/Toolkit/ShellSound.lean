module

public import Silmaril.Wasm.Binaryen.Toolkit.Shell
public import Silmaril.Wasm.Binaryen.Toolkit.ByteInputSound
public import Silmaril.Wasm.Binaryen.Exe.ExceptSound
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core SingleThreaded SingleThreaded.Exec Validation

private theorem empty_store_ok : StoreOk ({} : Store Empty) := by
  constructor <;> simp

theorem initializeForShell_sound {o : GrowOracle} {budget : Nat} {m : Wasm.Module}
    {c : Config Empty} (h : initializeForShell o budget m = .ok c) :
    ModuleValid m ∧ ConfigOk c [] ∧ c.code = [] ∧
      ∃ initial, Instantiate (SingleThreaded.profile o) divHost ({} : Store Empty) m [] initial ∧
        Steps (SingleThreaded.profile o) divHost initial c := by
  unfold initializeForShell at h
  split at h
  · cases h
  · cases h
  · rename_i initialized actual
    cases h
    have sound := CheckedRun.runChecked?_sound empty_store_ok actual
    have valid := (CheckedRun.runChecked?_inv actual).1
    obtain ⟨exports, imports, valid, _⟩ := valid
    exact ⟨⟨_, valid⟩, sound.2.1, sound.2.2 _ rfl, sound.1⟩
  · cases h
  · cases h

/-- A successful invocation executes the validated decoded module: complete
initialization, exact named export lookup, checked arguments, a genuine Core
step sequence, and the actual terminal result. File IO and printing are outside
this pure theorem. The numerical/growth policy is the explicit `SingleThreaded.profile o`.
-/
theorem shellModule_sound {o : GrowOracle} {budget : Nat} {name : String}
    {args : List Val} {m : Wasm.Module} {artifact : ShellArtifact}
    (h : shellModule o budget name args m = .ok artifact) :
    artifact.module = m ∧ ModuleValid m ∧
      ConfigOk artifact.initialized [] ∧ artifact.initialized.code = [] ∧
      (∃ initial, Instantiate (SingleThreaded.profile o) divHost ({} : Store Empty) m [] initial ∧
        Steps (SingleThreaded.profile o) divHost initial artifact.initialized) ∧
      exportFunc? artifact.initialized.frame.module name = some artifact.address ∧
      InvokeOk artifact.initialized.store artifact.address args ∧
      Steps (SingleThreaded.profile o) divHost
        (invoke artifact.initialized.store artifact.address args) artifact.final ∧
      artifact.final.code = artifact.result.toAdmin := by
  unfold shellModule at h
  obtain ⟨initialized, hi, h⟩ := Exe.bind_ok h
  obtain ⟨address, ha, h⟩ := Exe.bind_ok h
  have lookup : exportFunc? initialized.frame.module name = some address := by
    unfold resolveShellExport at ha
    split at ha
    · cases ha
    · cases ha; assumption
  split at h
  · rename_i checked
    split at h
    · cases h
    · cases h
    · rename_i final result actual
      cases h
      have init := initializeForShell_sound hi
      have hs : StoreOk initialized.store := init.2.1.choose_spec.1.1
      have invoked := InvokeRun.runInvoke?_sound hs (invokeOk?_sound checked) actual
      exact ⟨rfl, init.1, init.2.1, init.2.2.1, init.2.2.2, lookup,
        invokeOk?_sound checked, invoked.1, invoked.2.2 _ rfl⟩
    · cases h
  · cases h

theorem shellBytes_sound {o : GrowOracle} {budget : Nat} {name : String}
    {args : List Val} {bytes : ByteArray} {artifact : ShellArtifact}
    (h : shellBytes o budget name args bytes = .ok artifact) :
    Binary.Core.Encodes bytes.data.toList artifact.module ∧
      ModuleValid artifact.module ∧
      (∃ initial, Instantiate (SingleThreaded.profile o) divHost ({} : Store Empty)
        artifact.module [] initial ∧
        Steps (SingleThreaded.profile o) divHost initial artifact.initialized) ∧
      exportFunc? artifact.initialized.frame.module name = some artifact.address ∧
      InvokeOk artifact.initialized.store artifact.address args ∧
      Steps (SingleThreaded.profile o) divHost
        (invoke artifact.initialized.store artifact.address args) artifact.final ∧
      artifact.final.code = artifact.result.toAdmin := by
  unfold shellBytes at h
  obtain ⟨m, hm, h⟩ := Exe.bind_ok h
  have decoded : decodeInput "module" bytes = .ok m := by
    cases hd : decodeInput "module" bytes <;> simp_all [Except.mapError]
  obtain ⟨rfl, valid, _, _, initialization, lookup, typed, steps, result⟩ := shellModule_sound h
  exact ⟨decodeInput_sound decoded, valid, initialization, lookup, typed, steps, result⟩

/-- The named function belongs to the instance produced by Core instantiation.
Initialization preserves that instance even while running a state-changing start
function, so lookup after initialization uses its original export table. -/
theorem shellBytes_initial_export {o : GrowOracle} {budget : Nat} {name : String}
    {args : List Val} {bytes : ByteArray} {artifact : ShellArtifact}
    (h : shellBytes o budget name args bytes = .ok artifact) :
    ∃ initial, Instantiate (SingleThreaded.profile o) divHost ({} : Store Empty)
      artifact.module [] initial ∧
      Steps (SingleThreaded.profile o) divHost initial artifact.initialized ∧
      artifact.initialized.frame.module = initial.frame.module ∧
      exportFunc? initial.frame.module name = some artifact.address := by
  obtain ⟨_, _, ⟨initial, instantiated, steps⟩, lookup, _⟩ := shellBytes_sound h
  refine ⟨initial, instantiated, steps, steps.frame_module, ?_⟩
  rw [← steps.frame_module]
  exact lookup

end Silmaril.Wasm.Binaryen.Toolkit
