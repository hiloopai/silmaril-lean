module

public import Silmaril.Machine.X86.Ext9.Defs
public import Silmaril.Machine.Process.LpsBridge.Rel.Defs

/-!
# The LPS x86-64 user machine over the `Ext9` variant (`x86WithFlagOracle9`)

silmaril's
`x86WithFlagOracle8 oracle` is the LPS flag-oracle machine with the `Ext8` fetch. This module
adds the `Ext9` forms (`Silmaril.Machine.X86.Ext9`: `imul r, r/m, imm`, `imul r/m`, `bsf`, `bsr`,
`adc`/`sbb`, `call`/`jmp r/m64`, `push imm`, 16-bit ALU and `test` forms, `test r/m, imm`,
`bt r, r`), in the same way `X86FlagChoices8.lean` (silmaril-lean) adds the `Ext8` forms to
`x86WithFlagOracle`:

* `X86Accesses9.new9`: the data spans of an `Ext9` form (the `r/m` operand at its width; for
  `call r/m64` and `push imm` also the 8 stack bytes below `rsp`), as `X86Accesses.new8` does
  for the `Ext8` forms.
* `x86NativeStep9`: at `0F 05`, exactly `x86NativeStep8` (the trap). Elsewhere, where
  `Ext8.fetch` is `undecodable`, fetch an `Ext9` form (`Ext9.fetchNew`): if decoded and
  executable, execute it (`Ext9.execNew`) and report the fetch and data spans; if decoded but
  not executable, a fault; if not decoded, `unmodeled`. Everywhere else, `x86NativeStep8`.
  This is `Open9.step` off `0F 05` (`agrees_open9` in `Lps9/Thms`).
* `X86FlagChoices9.step9`, **`x86WithFlagOracle9 oracle`**: `{ x86WithFlagOracle oracle with
  step := step9 }`, the `step8` pattern over `x86NativeStep9`.

**Trust.** Like `x86WithFlagOracle8`, a model: silmaril's LPS port with the handwritten
`X86.Ext`/`Ext8` semantics and Silmaril's handwritten `Ext9` forms (differentially tested, see
`Silmaril.Machine.X86.Ext9.Defs`). The `Ext9` access spans are written here from `Ext9.execNew`;
they matter only for lazy (`MAP_NORESERVE`) reservations, which the bridge theorems exclude
(`AlignedF.lazy`), and are not proved complete.
-/

@[expose] public section

namespace Silmaril.Machine.Process.Lps9

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (State)
open Silmaril.Machine.X86

namespace X86Accesses9

/-- Data spans of a new `Ext9` form. -/
def new9 (core : State) (next : Silmaril.X86.Word) : Ext9.New → List (Silmaril.X86.Word × Nat)
  | .imulI sz _ src _ | .imul1 sz src | .bsf sz _ src | .bsr sz _ src | .adcR sz _ _ src =>
    X86Accesses.rm core next sz.bytes src
  | .adc sz _ dst _ | .adcI sz _ dst _ | .testI sz dst _ => X86Accesses.rm core next sz.bytes dst
  | .callInd src => X86Accesses.rm core next 8 src ++ [(core.read .rsp - 8, 8)]
  | .jmpInd src => X86Accesses.rm core next 8 src
  | .pushI _ => [(core.read .rsp - 8, 8)]
  | .alu16 _ dst _ | .alu16I _ dst _ | .test16 dst _ | .test16I dst _ =>
    X86Accesses.rm core next 2 dst
  | .alu16R _ _ src => X86Accesses.rm core next 2 src
  | .testI8 dst _ => X86Accesses.rm8 core next dst
  | .alu16A .. | .test16A .. | .bt .. => []
  | .repRet => X86Accesses.canonical core 2 .ret

end X86Accesses9

/-- **The native LPS x86 step over `Ext9`.** -/
def x86NativeStep9 (s : X86State) : MachineResult (AccessReport X86State) :=
  if s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] then x86NativeStep8 s
  else
    match Silmaril.X86.Ext8.fetch s.m.memory s.m.core.rip.toNat with
    | .inl .undecodable =>
      match Ext9.fetchNew s.m.memory s.m.core.rip.toNat with
      | some (some (i, n)) =>
        x86ExecResult ((s.m.core.rip, n) ::
            X86Accesses9.new9 s.m.core (s.m.core.rip + BitVec.ofNat 64 n) i)
          (Ext9.execNew i s.m.core s.m.memory (s.m.core.rip + BitVec.ofNat 64 n))
      | some none => .fault
      | none => .unmodeled
    | _ => x86NativeStep8 s

namespace X86FlagChoices9

/-- `X86FlagChoices.step` over the `Ext9` variant (the `step8` pattern). -/
def step9 (oracle : Nat → X86FlagChoices.Choice) (state : X86FlagChoices.State) :
    MachineResult (AccessReport X86FlagChoices.State) :=
  if state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    X86FlagChoices.lift (state.counter + 1)
      (x86NativeStep9 (X86FlagChoices.completeState state.native (oracle state.counter)))
  else X86FlagChoices.lift state.counter (x86NativeStep9 state.native)

end X86FlagChoices9

/-- **`x86WithFlagOracle` over the `Ext9` variant.** -/
def x86WithFlagOracle9 (oracle : Nat → X86FlagChoices.Choice) : UserIsa :=
  { x86WithFlagOracle oracle with step := fun _ => X86FlagChoices9.step9 oracle }

end Silmaril.Machine.Process.Lps9
