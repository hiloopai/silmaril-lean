module

public import Silmaril.Machine.Abi.CrossAbi.Defs
public import Silmaril.Machine.Abi.Thunk.Thms
public import Silmaril.Machine.Abi.Win64.Thms
import Silmaril.Proofs.Machine.Abi.CrossAbi.Bridge
/-! # Verified cross-ABI thunks between System V and Microsoft x64

For prototypes with at most four parameters (`Small`):

* `sysvToMs_simulates`: a thunk that implements `SysvToMs` and makes progress is
  a simulation from System V callers to Microsoft x64 callees.
* `sysv_of_ms`: **composition theorem**. If an `ms_abi` callee satisfies the
  Microsoft x64 translation of a strict C contract `c` and provides the
  thunk's guarantee, then the callee reached through the thunk satisfies the
  System V translation of `c` (on caller states meeting the thunk's room
  assumption).
* `msToSysv_simulates`, `ms_of_sysv`: the reverse direction, for adapters that
  also restore RSI, RDI and XMM6–15.
* `sysv_of_ms_reduce`: the C-level reading of `sysv_of_ms`, through both
  satisfaction conditions, for thunks with no room assumption.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CrossAbi

open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (Proto CallSite vocab sysv Options)
open Silmaril.Machine.Abi.Win64 (win64 reg RaxResult win64_resultAt_iff sysv_resultAt_iff)
open Silmaril.Machine.Abi.Convention (Thunk Strict Guarantees)

variable {p : Proto}

/-- An implementing, progressing System V → Microsoft x64 thunk is a simulation. -/
theorem sysvToMs_simulates (options : Options) (small : Small p)
    {t : Thunk (sysv options) win64 p} {room : Ffi.State → Prop}
    {guar : Ffi.State → Ffi.State → Prop}
    (impl : Implements t SysvToMs.Enter SysvToMs.Leave room guar) (progress : Progress t room guar) :
    t.Simulates room guar where
  enter_entry a s entry roomy s₁ entered :=
    Silmaril.Proofs.Machine.Abi.CrossAbi.sysvToMs_entry options small entry
      (impl.enter a s entry roomy s₁ entered)
  enter_progress := progress.enter
  leave_progress := progress.leave
  leave_return a s entry roomy s₁ entered s₂ proper g s₃ left :=
    Silmaril.Proofs.Machine.Abi.CrossAbi.sysvToMs_return options p (impl.enter a s entry roomy s₁ entered)
      proper.1 (impl.leave a s entry roomy s₁ entered s₂ proper g s₃ left)
  leave_result a s entry roomy s₁ entered s₂ proper g s₃ left := by
    have hrax := (impl.leave a s entry roomy s₁ entered s₂ proper g s₃ left).rax
    obtain ⟨r, at_⟩ := proper.2
    refine ⟨⟨r, ?_⟩, fun r' at' => ?_⟩
    · rw [sysv_resultAt_iff, Silmaril.Proofs.Machine.Abi.CrossAbi.raxResult_congr _ _ hrax]
      exact at_
    · rw [sysv_resultAt_iff, Silmaril.Proofs.Machine.Abi.CrossAbi.raxResult_congr _ _ hrax] at at'
      exact at'

/-- An implementing, progressing Microsoft x64 → System V thunk is a simulation. -/
theorem msToSysv_simulates (options : Options) (small : Small p)
    {t : Thunk win64 (sysv options) p} {room : Ffi.State → Prop}
    {guar : Ffi.State → Ffi.State → Prop}
    (impl : Implements t MsToSysv.Enter MsToSysv.Leave room guar) (progress : Progress t room guar) :
    t.Simulates room guar where
  enter_entry a s entry roomy s₁ entered :=
    Silmaril.Proofs.Machine.Abi.CrossAbi.msToSysv_entry options small entry
      (impl.enter a s entry roomy s₁ entered)
  enter_progress := progress.enter
  leave_progress := progress.leave
  leave_return a s entry roomy s₁ entered s₂ proper g s₃ left :=
    Silmaril.Proofs.Machine.Abi.CrossAbi.msToSysv_return options p (impl.enter a s entry roomy s₁ entered)
      proper.1 (impl.leave a s entry roomy s₁ entered s₂ proper g s₃ left)
  leave_result a s entry roomy s₁ entered s₂ proper g s₃ left := by
    have hrax := (impl.leave a s entry roomy s₁ entered s₂ proper g s₃ left).rax
    obtain ⟨r, at_⟩ := proper.2
    rw [sysv_resultAt_iff] at at_
    refine ⟨⟨r, ?_⟩, fun r' at' => ?_⟩
    · show RaxResult _ r s₃
      rw [Silmaril.Proofs.Machine.Abi.CrossAbi.raxResult_congr _ _ hrax]
      exact at_
    · rw [sysv_resultAt_iff]
      have : RaxResult _ r' s₃ := at'
      rwa [Silmaril.Proofs.Machine.Abi.CrossAbi.raxResult_congr _ _ hrax] at this

/-- **Composition theorem (System V caller, `ms_abi` callee).** -/
theorem sysv_of_ms (options : Options) (small : Small p)
    {t : Thunk (sysv options) win64 p} {room : Ffi.State → Prop}
    {guar : Ffi.State → Ffi.State → Prop}
    (impl : Implements t SysvToMs.Enter SysvToMs.Leave room guar) (progress : Progress t room guar)
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} (strict : Strict c)
    {model : Contracts.Model Ffi.State Ffi.State}
    (callee : Contracts.Sat model (win64.translate p c))
    (guaranteed : Guarantees win64 p c model guar) :
    Contracts.Sat (t.wrap model) (within ((sysv options).translate p c) room) :=
  (sysvToMs_simulates options small impl progress).sound strict callee guaranteed

/-- **Composition theorem (`ms_abi` caller, System V callee).** -/
theorem ms_of_sysv (options : Options) (small : Small p)
    {t : Thunk win64 (sysv options) p} {room : Ffi.State → Prop}
    {guar : Ffi.State → Ffi.State → Prop}
    (impl : Implements t MsToSysv.Enter MsToSysv.Leave room guar) (progress : Progress t room guar)
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} (strict : Strict c)
    {model : Contracts.Model Ffi.State Ffi.State}
    (callee : Contracts.Sat model ((sysv options).translate p c))
    (guaranteed : Guarantees (sysv options) p c model guar) :
    Contracts.Sat (t.wrap model) (within (win64.translate p c) room) :=
  (msToSysv_simulates options small impl progress).sound strict callee guaranteed

/-- The composition theorem at C level: the System V read-back of the adapted
callee meets every strict C contract that the Microsoft x64 read-back of the
callee meets. -/
theorem sysv_of_ms_reduce (options : Options) (small : Small p)
    {t : Thunk (sysv options) win64 p} {guar : Ffi.State → Ffi.State → Prop}
    (impl : Implements t SysvToMs.Enter SysvToMs.Leave (fun _ => True) guar)
    (progress : Progress t (fun _ => True) guar)
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} (strict : Strict c)
    {model : Contracts.Model Ffi.State Ffi.State}
    (callee : Contracts.Sat (win64.reduce p model) c)
    (guaranteed : Guarantees win64 p c model guar) :
    Contracts.Sat ((sysv options).reduce p (t.wrap model)) c :=
  (sysvToMs_simulates options small impl progress).sound_reduce strict callee guaranteed

end Silmaril.Machine.Abi.CrossAbi
