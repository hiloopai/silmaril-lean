module

public import Silmaril.Machine.Abi.Conformance.LeafArith.Defs

/-!
# ABI conformance of rung 01: the witness state and the test machines

The concrete admitted call used for non-vacuity and the negative tests: the 181 code bytes at
`0x401370`, `rsp = 0x8ff8` with the return address `0x401000`, one region mapping every
address read-write, the arguments in `rdi`, `rsi`, `rdx` (`ffiSt`). And the small machines of
the schema tests (`toy`: a segment machine given by its step function, with no decoder).
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.LeafArith.Witness

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (vocab)
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.LeafArith
open Silmaril.X86.Ladder.LeafArith (code base)

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩

def retAt : Word := 0x401000

def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAt]

def mem : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ 0x8ff8 retEnc) 0x401370 code⟩

/-- `rip` at offset `off`, `rsp = 0x8ff8`, `rdi`, `rsi`, `rdx` as given. -/
def st (off : Nat) (x y z : Word) : MState :=
  ⟨⟨fun r => match r with | .rdi => x | .rsi => y | .rdx => z | .rsp => 0x8ff8 | _ => 0,
    base + BitVec.ofNat 64 off, ⟨none, none, none, none, none, none⟩, 0⟩, mem⟩

def ffiSt (off : Nat) (x y z : Word) : Ffi.State :=
  ⟨st off x y z, fun _ => 0, fun _ => 0, false, true, 0, 0, 0⟩

/-- The C arguments `clamp_i32(5, 0, 3)`. -/
def clampArgs : vocab.Args clampProto :=
  .cons (5 : BitVec 32) (.cons (0 : BitVec 32) (.cons (3 : BitVec 32) .nil))

/-- The C arguments `sat_add_u32(0xfffffff0, 0x20)`. -/
def satArgs : vocab.Args satProto :=
  .cons (0xfffffff0 : BitVec 32) (.cons (0x20 : BitVec 32) .nil)

/-- A segment machine whose step is `f` (no decoder: the law `step_of` is vacuous). -/
def toy (f : MState → Option MState) : Mach where
  Instr := Unit
  instDecEq := inferInstance
  decode _ := none
  exec _ _ _ _ := .dataFault
  core := MState.core
  mem := MState.memory
  upd _ c m := ⟨c, m⟩
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  ok _ _ := True
  live _ := True
  step := f
  live_step _ _ := trivial
  step_of _ _ _ _ hd _ _ := nomatch hd

/-- The admitted call `clamp_i32(5, 0, 3)`, on any toy machine. -/
def s0 : Ffi.State := ffiSt 0x30 5 0 3

/-- A state returned from `s0`: `rip` at its return address, `rsp + 8`, core `c`. -/
def ret0 (c : State) (m : Memory) : MState :=
  ⟨{ c with rip := retAt, regs := Silmaril.Machine.RegisterFile.write c.regs .rsp (0x8ff8 + 8) }, m⟩

/-- A machine stepping from the entry of `clamp_i32` straight to `ret0 c m`, then stuck. -/
def oneStep (c : State) (m : Memory) : MState → Option MState :=
  fun x => if x.core.rip = clampCode.entry then some (ret0 c m) else none

/-- The core of `s0` with `rbx` incremented. -/
def clobbered : State := s0.machine.core.write .rbx (s0.machine.core.read .rbx + 1)

/-- `s0`'s memory with the byte at `rsp − 8` set. -/
def scribbled : Memory :=
  { s0.machine.memory with bytes := Memory.install s0.machine.memory.bytes (0x8ff8 - 8) [0xab] }

/-- The core of `s0` "returned" with `rsp` 16 above its entry. -/
def unbalancedCore : State :=
  { s0.machine.core with
    rip := retAt
    regs := Silmaril.Machine.RegisterFile.write s0.machine.core.regs .rsp (0x8ff8 + 16) }

/-- A machine stepping from the entry to `unbalancedCore`, then stuck. -/
def unbalancedStep : MState → Option MState :=
  fun x => if x.core.rip = clampCode.entry then some ⟨unbalancedCore, s0.machine.memory⟩ else none

/-- `long clamp_i32(long, long, long)`. -/
def longProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[.int64, .int64, .int64], some .int64⟩, by decide⟩

/-- `unsigned clamp_i32(int, int, int)`: `clamp_i32` with an unsigned result. -/
def uRetProto : Silmaril.Machine.Abi.SystemV.Proto :=
  ⟨⟨[.int32, .int32, .int32], some .uint32⟩, by decide⟩

/-- A header that declares `clamp_i32` with an unsigned result. -/
def hdrU : HeaderSrc := ⟨[("arith.h", "unsigned clamp_i32(int x, int lo, int hi);")], "arith.h"⟩

end Silmaril.Machine.Abi.Conformance.LeafArith.Witness

end
