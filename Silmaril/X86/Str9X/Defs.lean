module

public import Silmaril.X86.Str9D.Defs
public import Silmaril.X86.Features.Ext.X87.Extension

/-!
# `Str9X`: `Str9D` with the x87 FPU

The x87 instructions of the C libraries and tools the tower is aimed at (glibc's
`strtold`, `__printf_fp`, `printf_size` and the `long double` paths of `vfprintf`/`vfscanf`,
gzip's `fldt`/`fstpt`, coreutils `seq`, `numfmt`, `df`, `ls`, `du`, `sort`, `od`) are decoded by
no layer of the tower. silmaril's feature-parametric machine has them: the x87 lane
`Features.Fpu.ext` (`Fpu.Instr`, `Fpu.decode`, `Fpu.exec`, with 6,840 native vectors).
`Str9X` puts that lane **at the end of `Str9D`'s fetch chain**, unchanged.

**State.** `XState` is a `Str9D.DState` (`d`) and the x87 state `Features.X87` (`fpu`: the
eight 80-bit data registers, the status word with TOP, the control word and the tag word;
FIP/FDP/FOP are not modelled, as in the lane).

**Step.** Where some decoder of `Str9D` claims the bytes at RIP (`lowerClaims`: `Str9V`'s
chain, its own forms, `std`/`cld`, or a string form with DF set), `step` is `Str9D.step` with
the x87 state kept, so every `Str9D` step is a step (`Thms.step_of_str9d`,
`Thms.extendsStr9D`). Elsewhere it fetches an `Fpu.Instr` (`Fpu.decode`, execute permission
on the consumed bytes) and runs `Fpu.exec` on the lane state `toF x`: the tower's core and
x87 state, with zero vector and mask registers and `MXCSR.reset`. `Fpu.exec` reads and writes
only the core, the x87 state and memory (`setX87`, `setCore`, `advance`), so the tower's
vector registers, ghost state and DF are kept. An x87 fault (`#MF`, a data fault) and an
`unmodeled` form (the transcendentals `F2XM1`, `FYL2X`, `FPTAN`, `FPATAN`, `FYL2XP1`,
`FSINCOS`, `FSIN`, `FCOS`) have no step.

**Features.** The lane's `requires` (x87; SSE3 for `FISTTP`) is not checked: every machine
the tower describes has them (the x86-64 baseline has the FPU, `Str9V` already assumes
AVX2, and SSE3 is part of x86-64-v2).

The listing decoder `decodeL` accepts an `Fpu.decode` form only where every decoder of
`Str9D` rejects the slice in a way no following byte changes (`Str9D.lowerBad`, not `std`
or `cld`, and not a string opcode), checked on each listing by `decide`.

The x87 semantics is the lane's (a handwritten model of the SDM, compared with hardware by
the lane's vectors); `Str9X.Vectors` runs the same vectors through `Str9X.step`.
-/

@[expose] public section

namespace Silmaril.X86.Str9X

open Silmaril.X86 (Reg Word State Byte fetchWindow maxInstrLength)
open Silmaril.X86.Str9D (DState)
open Silmaril.Process (Memory)

/-! ## State -/

/-- **The state**: a `Str9D` state and the x87 FPU. -/
structure XState where
  d : DState
  fpu : Silmaril.X86.Features.X87

/-- The core. -/
abbrev XState.core (x : XState) : State := x.d.core

/-- The memory. -/
abbrev XState.memory (x : XState) : Memory := x.d.memory

/-- The lane state of the x87 lane: the core and the x87 state; no vector, mask or MXCSR
state is read by `Fpu.exec`. -/
def toF (x : XState) : Silmaril.X86.Features.State :=
  ⟨x.core, fun _ => 0, fun _ => 0, Silmaril.X86.Float.MXCSR.reset, x.fpu⟩

/-! ## Decoding -/

/-- Some decoder of `Str9D` claims the bytes at RIP (decodes them, or faults fetching them). -/
def lowerClaims (d : DState) : Bool :=
  (d.df && Str9D.strClaims (fetchWindow d.memory maxInstrLength d.core.rip.toNat)) ||
    Str9V.lowerClaims d.v.g || (Str9V.fetchNew d.memory d.core.rip.toNat).isSome ||
    (Str9D.fetchFlag d.memory d.core.rip.toNat).isSome

/-- The listing decoder of an x87 form: `Fpu.decode` reads a form of at most 15 bytes, and
every decoder of `Str9D` rejects the slice in a way no following byte changes. -/
def decodeL (w : List Byte) : Option (Silmaril.X86.Features.Fpu.Instr × Nat) :=
  match Silmaril.X86.Features.Fpu.decode w with
  | some (i, n) =>
    if Str9D.lowerBad w = true ∧ Str9D.decodeFlag w = none ∧ Str9D.strClaims w = false ∧
        n ≤ maxInstrLength then some (i, n) else none
  | none => none

/-- Fetch an x87 form (`none`: not one; `some none`: not executable). -/
def fetchFpu (memory : Memory) (address : Nat) :
    Option (Option (Silmaril.X86.Features.Fpu.Instr × Nat)) :=
  (Silmaril.X86.Features.Fpu.decode (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-! ## Semantics and step -/

/-- **Execute an x87 form** of `n` bytes: `Fpu.exec` on `toF x`; the core, the x87 state and
the memory are taken back, everything else kept. Faults and `unmodeled` forms: no step. -/
def execFpu (i : Silmaril.X86.Features.Fpu.Instr) (n : Nat) (x : XState) : Option XState :=
  match Silmaril.X86.Features.Fpu.exec i n (toF x) x.memory with
  | .retired s m => some ⟨x.d.upd s.core m, s.x87⟩
  | _ => none

/-- **One step**: `Str9D.step` with the x87 state kept where `Str9D` claims the bytes;
otherwise an x87 form. -/
def step (x : XState) : Option XState :=
  if lowerClaims x.d then (Str9D.step x.d).map fun d => ⟨d, x.fpu⟩
  else
    match fetchFpu x.memory x.core.rip.toNat with
    | some (some (i, n)) => execFpu i n x
    | _ => none

end Silmaril.X86.Str9X
