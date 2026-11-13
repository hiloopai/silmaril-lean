module

public import Silmaril.X86.Str9FsX.Defs
public import Silmaril.X86.Narrow9.Defs

/-!
# `Str9FsXN`: `Str9FsX` with the 8- and 16-bit shift, rotate and carry forms

`Str9FsX` stops on the narrow integer forms that zlib's compressor and musl's formatted
output use: `shr r/m16, imm8` (`66 C1 /5 ib`) in `deflate_fast`, `deflate_slow`, `_tr_align`
and `_tr_flush_bits`, and `sbb r/m8, imm8` (`80 /3 ib`) in `deflate`. `Narrow9` defines them
and the rest of their family (16-bit shifts and rotates, 8-bit rotates, 8- and 16-bit
ADC/SBB). `Str9FsXN` adds them **at the end of `Str9FsX`'s fetch chain**, on the same state
`Sse9.XState`: `Ext8` → `Ext9` → string forms → `Str9Fs`'s atomic and FS forms → `Sse9`'s SSE
forms → `rep stosd` → the `Narrow9` forms. A `Narrow9` form is therefore tried only on bytes
every lower decoder rejects, so every `Str9FsX` step is a step (`Thms.step_of_str9fsx`) and
every machine below lifts (`extendsStr9FsX`, `extendsSse9`, `extendsStr9Fs`, `extendsStr9`,
`extendsOpen9`, `extendsOpen`).

The `SegVC` machine `isa` has `Str9FsX`'s integer instructions and the `Narrow9` forms, which
see only the core and the memory and keep the XMM file. The SSE forms keep their own listing
law (`Str9FsX.step_of_listed_sse` lifted as `Thms.step_of_listed_sse`).
-/

@[expose] public section

namespace Silmaril.X86.Str9FsXN

open Silmaril.X86 (Reg Word State Byte MState fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Result)
open Silmaril.X86.Sse9 (XState XFile)
open Silmaril.Process (Memory)

/-! ## Listing decoder -/

/-- `rep stosd`'s decoder reads nothing that starts with these bytes. -/
def stosdBad : List Byte → Bool
  | [] => false
  | b :: _ => b != 0xF3#8

/-- The listing decoder of a `Narrow9` form: `Narrow9.decodeNew` reads a form of 1 to 15
bytes, and every lower decoder rejects the slice in a way that no following byte can
change. Checked on each listing by `decide`. -/
def decodeNarrowL (w : List Byte) : Option (Narrow9.New × Nat) :=
  match Narrow9.decodeNew w with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode w = none ∧ Silmaril.X86.Open9.newBad w = true ∧
        Silmaril.X86.Open9.rawNotEof w = true ∧ Silmaril.X86.Str9.ext9Bad w = true ∧
        Silmaril.X86.Str9Fs.strBad w = true ∧ Silmaril.X86.Str9FsX.atomicBad w = true ∧
        Silmaril.X86.Str9FsX.fsBad w = true ∧ Silmaril.X86.Str9FsX.sseBad w = true ∧
        stosdBad w = true ∧ 0 < n ∧ n ≤ maxInstrLength then
      some (i, n)
    else none
  | none => none

/-! ## The integer instructions -/

/-- The integer instructions of the machine: `Str9FsX`'s and the `Narrow9` forms. -/
inductive Instr where
  | base (i : Silmaril.X86.Str9FsX.Instr)
  | narrow (i : Narrow9.New)
  deriving DecidableEq, Repr

/-- The listing decoder of the integer instructions. -/
def decode (w : List Byte) : Option (Instr × Nat) :=
  match Silmaril.X86.Str9FsX.decode w with
  | some (i, n) => some (.base i, n)
  | none => (decodeNarrowL w).map fun (i, n) => (.narrow i, n)

/-- The executor of the integer instructions. -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .base i => Silmaril.X86.Str9FsX.exec i s memory length
  | .narrow i => Narrow9.execNew i s memory (s.rip + BitVec.ofNat 64 length)

/-! ## Step -/

/-- **One step**: `Str9FsX`'s fetch chain, and on bytes that all of it rejects, a `Narrow9`
form (the XMM file kept). -/
def step (x : XState) : Option XState :=
  match Silmaril.X86.Ext8.fetch x.m.memory x.m.core.rip.toNat with
  | .inl .undecodable =>
    match Silmaril.X86.Ext9.fetchNew x.m.memory x.m.core.rip.toNat with
    | some (some (i, n)) =>
      Str9FsX.keep x
        (Silmaril.X86.Ext9.execNew i x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 n))
    | some none => none
    | none =>
      match Silmaril.X86.Str9.fetchStr x.m.memory x.m.core.rip.toNat with
      | some (some (i, n)) =>
        Str9FsX.keep x
          (Silmaril.X86.Str9.execStr i x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 n))
      | some none => none
      | none =>
        match Silmaril.X86.Str9Fs.fetchNew x.m.memory x.m.core.rip.toNat with
        | some (some (i, n)) => Str9FsX.keep x (Silmaril.X86.Str9Fs.execNew i x.m.core x.m.memory n)
        | some none => none
        | none =>
          match Silmaril.X86.Sse9.fetchSse x.m.memory x.m.core.rip.toNat with
          | some (some (i, n)) =>
            (Silmaril.X86.Sse9.exec i x.m.core x.xmm x.m.memory
              (x.m.core.rip + BitVec.ofNat 64 n)).toOption
          | some none => none
          | none =>
            match Str9FsX.fetchStosd x.m.memory x.m.core.rip.toNat with
            | some (some n) =>
              Str9FsX.keep x (Str9FsX.execStosd x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 n))
            | some none => none
            | none =>
              match Narrow9.fetchNew x.m.memory x.m.core.rip.toNat with
              | some (some (i, n)) =>
                Str9FsX.keep x
                  (Narrow9.execNew i x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 n))
              | _ => none
  | _ => (Silmaril.X86.Open.step x.m).map fun m' => ⟨m', x.xmm⟩

end Silmaril.X86.Str9FsXN
