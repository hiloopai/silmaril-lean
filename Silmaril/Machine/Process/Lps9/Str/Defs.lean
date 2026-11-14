module

public import Silmaril.Machine.Process.Lps9.Defs
public import Silmaril.Machine.X86.Str9.Defs

/-!
# The LPS x86-64 user machine with the `Str9` string forms (`x86WithFlagOracle9Str`)

`x86WithFlagOracle9`
(P7, `Lps9/Defs.lean`) executes the `Ext8` and `Ext9` forms. musl's `memcpy`, `memset` and
startup also execute three string forms, `movsb` (`A4`), `rep movsq` (`F3 48 A5`) and
`rep stosq` (`F3 48 AB`) (Z3a, `Silmaril.Machine.X86.Str9`). This sub-topic adds them, without
touching P7's files:

* `strAccesses`: the data spans of one string step: `movsb` reads `[rsi]` and writes `[rdi]`
  (1 byte each); one element of `rep movsq` reads `[rsi]` and writes `[rdi]` (8 bytes each);
  one element of `rep stosq` writes `[rdi]` (8 bytes); with `rcx = 0` the `rep` forms touch no
  data.
* `x86NativeStep9Str`: `x86NativeStep9`, except where `Ext8.fetch` is `undecodable` and
  `Ext9.fetchNew` decodes nothing: there fetch a string form (`Str9.fetchStr`); if decoded
  and executable, execute one step of it (`Str9.execStr`) and report the fetch and the data
  spans; if decoded but not executable, a fault; if not decoded, `unmodeled`. This is exactly
  the structure of `Str9.step` (`agrees_str9` in `Lps9/Str/Thms`).
* **`x86WithFlagOracle9Str oracle`**: `flagMachine oracle x86NativeStep9Str`, the
  flag-oracle machine over it.

**Trust.** A model: silmaril's LPS port, the handwritten `X86.Ext`/`Ext8` semantics,
Silmaril's handwritten `Ext9` forms and Z3a's handwritten string forms (one element per step,
DF clear; not differentially tested yet, ). The access spans are written here from
`Str9.execStr`; like `X86Accesses9.new9` they matter only for lazy (`MAP_NORESERVE`)
reservations, which every bridge theorem excludes, and are not proved complete.
-/

@[expose] public section

namespace Silmaril.Machine.Process.Lps9.Str

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (State)
open Silmaril.Machine.X86
open Silmaril.Machine.Process.LpsBridge (flagMachine Oracle)

/-- Data spans of one step of a string form. -/
def strAccesses (core : State) : Str9.Str → List (Silmaril.X86.Word × Nat)
  | .movsb => [(core.read .rsi, 1), (core.read .rdi, 1)]
  | .repMovsq => if core.read .rcx = 0 then [] else [(core.read .rsi, 8), (core.read .rdi, 8)]
  | .repStosq => if core.read .rcx = 0 then [] else [(core.read .rdi, 8)]

/-- **The native LPS x86 step over `Ext9` and the `Str9` string forms.** -/
def x86NativeStep9Str (s : X86State) : MachineResult (AccessReport X86State) :=
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
      | none =>
        match Str9.fetchStr s.m.memory s.m.core.rip.toNat with
        | some (some (i, n)) =>
          x86ExecResult ((s.m.core.rip, n) :: strAccesses s.m.core i)
            (Str9.execStr i s.m.core s.m.memory (s.m.core.rip + BitVec.ofNat 64 n))
        | some none => .fault
        | none => .unmodeled
    | _ => x86NativeStep8 s

/-- **`x86WithFlagOracle` over `Ext9` and the string forms.** -/
abbrev x86WithFlagOracle9Str (oracle : Oracle) : UserIsa := flagMachine oracle x86NativeStep9Str

end Silmaril.Machine.Process.Lps9.Str
