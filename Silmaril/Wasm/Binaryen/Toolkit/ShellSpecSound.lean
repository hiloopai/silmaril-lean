module

public import Silmaril.Wasm.Binaryen.Toolkit.ShellSound
public import Silmaril.Wasm.Execution.Core.InstantiationMono
public import Silmaril.Wasm.Execution.Core.SpecProfile
public import Silmaril.Wasm.Behaviour.Semantics.Core

@[expose] public section

/-! # Shell runs admitted by nondeterministic specification semantics

The executable chooses concrete numerical results and a grow oracle. These
theorems transport its actual successful artifact, including initialization
and the named invocation, to any profile admitting those finite executions.
In particular every chosen execution is admitted by `Profile.spec nd {}` for
either value of `$ND`, with one global all-zero relaxed choice.

This is one-way conformance: neither enumeration of all permitted outcomes,
equivalence of behavior sets, nor completeness for specification executions
is asserted. The existing deterministic-profile theorem remains available.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core SingleThreaded Numerics Validation

/-- A successful shell run is sound in every profile admitting the runner's
finite executions. The original bytes, initialized state and terminal result
are unchanged. -/
theorem shellBytes_profile_sound {o : GrowOracle} {P : Profile}
    (admitted : ∀ {c c' : Config Empty},
      Steps (SingleThreaded.profile o) divHost c c' → Steps P divHost c c')
    {budget : Nat} {name : String} {args : List Val} {bytes : ByteArray}
    {artifact : ShellArtifact} (h : shellBytes o budget name args bytes = .ok artifact) :
    Binary.Core.Encodes bytes.data.toList artifact.module ∧
      ModuleValid artifact.module ∧
      (∃ initial, Instantiate P divHost ({} : Store Empty) artifact.module [] initial ∧
        Steps P divHost initial artifact.initialized) ∧
      exportFunc? artifact.initialized.frame.module name = some artifact.address ∧
      InvokeOk artifact.initialized.store artifact.address args ∧
      Steps P divHost (invoke artifact.initialized.store artifact.address args) artifact.final ∧
      artifact.final.code = artifact.result.toAdmin := by
  obtain ⟨meaning, valid, ⟨initial, instantiated, initialized⟩, lookup, typed, invoked, result⟩ :=
    shellBytes_sound h
  exact ⟨meaning, valid, ⟨initial, instantiated.mono admitted, admitted initialized⟩,
    lookup, typed, admitted invoked, result⟩

/-- Every chosen shell result is a genuine execution of the nondeterministic
specification profile for either value of `$ND`, with the default relaxed choices
fixed throughout initialization and invocation. In particular the specification
permits the runner's NaN and growth choices. The default is `$ND = false`. -/
theorem shellBytes_spec_sound {o : GrowOracle} {budget : Nat} {name : String}
    {args : List Val} {bytes : ByteArray} {artifact : ShellArtifact}
    (h : shellBytes o budget name args bytes = .ok artifact) (nd : Bool := false) :
    Binary.Core.Encodes bytes.data.toList artifact.module ∧
      ModuleValid artifact.module ∧
      (∃ initial, Instantiate (Profile.spec nd {}) divHost ({} : Store Empty)
        artifact.module [] initial ∧
        Steps (Profile.spec nd {}) divHost initial artifact.initialized) ∧
      exportFunc? artifact.initialized.frame.module name = some artifact.address ∧
      InvokeOk artifact.initialized.store artifact.address args ∧
      Steps (Profile.spec nd {}) divHost
        (invoke artifact.initialized.store artifact.address args) artifact.final ∧
      artifact.final.code = artifact.result.toAdmin :=
  shellBytes_profile_sound
    (fun steps => Steps.deterministic_refines_spec nd steps) h

/-- The exact terminal value, trap, or escaping exception selected by the shell
belongs to the specification's invocation behavior set after initialization. -/
theorem shellBytes_result_mem_spec {o : GrowOracle} {budget : Nat} {name : String}
    {args : List Val} {bytes : ByteArray} {artifact : ShellArtifact}
    (h : shellBytes o budget name args bytes = .ok artifact) (nd : Bool := false) :
    artifact.result.toBehaviour ∈ behaviours (Profile.spec nd {}) divHost
      artifact.initialized.store artifact.address args := by
  obtain ⟨_, _, _, _, _, steps, result⟩ := shellBytes_spec_sound h nd
  exact mem_behavioursOf steps result

/-- The named export is from the original specification instantiation, even
when initialization executes a state-changing start function. -/
theorem shellBytes_spec_initial_export {o : GrowOracle} {budget : Nat} {name : String}
    {args : List Val} {bytes : ByteArray} {artifact : ShellArtifact}
    (h : shellBytes o budget name args bytes = .ok artifact) (nd : Bool := false) :
    ∃ initial, Instantiate (Profile.spec nd {}) divHost ({} : Store Empty)
      artifact.module [] initial ∧
      Steps (Profile.spec nd {}) divHost initial artifact.initialized ∧
      artifact.initialized.frame.module = initial.frame.module ∧
      exportFunc? initial.frame.module name = some artifact.address := by
  obtain ⟨_, _, ⟨initial, instantiated, initialized⟩, lookup, _⟩ := shellBytes_spec_sound h nd
  refine ⟨initial, instantiated, initialized, initialized.frame_module, ?_⟩
  rw [← initialized.frame_module]
  exact lookup

end Silmaril.Wasm.Binaryen.Toolkit
