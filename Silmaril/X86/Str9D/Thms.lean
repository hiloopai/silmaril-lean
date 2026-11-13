module

public import Silmaril.Raw.X86.Str9D

/-!
# `Str9D`: what lifts from `Str9V`, the laws of the layer's forms, the machine

* `step_of_str9v`, `run_of_str9v`, `reaches_of_str9v`: **every `Str9V` step, run and
  reachability from a state with DF clear holds here**, with DF still clear. There is no
  `Isa.Extends` from `Str9V`: with DF set its string forms are not steps.
* `step_of_listed_std`, `step_of_listed_cld`: `std` and `cld` at a listed offset.
* `step_of_listed_str`: a string form with DF set, executed downwards (`execStr true`).
* `step_of_listed`, `isa`: `Str9FsX`'s integer instructions that are not string forms, at
  either DF value.

The proofs are in `Silmaril.Raw.X86.Str9D` (valid, not yet in Isar style), re-exported here.
`Str9D/Vectors.lean` compares the machine with hardware.
-/

@[expose] public section

namespace Silmaril.X86.Str9D

open Silmaril.X86 (State Word Byte maxInstrLength)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Str9V (VState)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-- **A `Str9V` run from DF clear reaches the same state here**, DF still clear. -/
theorem reaches_of_str9v {v v' : VState} (h : Reaches Str9V.step v v') :
    Reaches step ⟨v, false⟩ ⟨v', false⟩ :=
  let ⟨n, hn⟩ := h; ⟨n, run_of_str9v hn⟩

/-! ## Decoding facts (kernel-checked) -/

/-- No layer of `Str9V` reads `std` (`FD`) or `cld` (`FC`). -/
theorem lowerBad_std : lowerBad [0xFD] = true := by decide

theorem lowerBad_cld : lowerBad [0xFC] = true := by decide

/-- The six string forms are claimed with DF set, and decode to themselves. -/
example : [Str.movsb, .repMovsb, .repMovsq, .repStosb, .repStosd, .repStosq].all
    (fun f => strClaims f.bytes && decodeStr f.bytes == some (f, f.bytes.length)) = true := by
  decide

/-- Other string instructions are claimed too (no step with DF set): `rep movsd` (`F3 A5`),
`movsq` (`48 A5`), `repne scasb` (`F2 AE`), `lodsb` (`AC`), `cmpsb` (`A6`). -/
example : [[0xF3, 0xA5], [0x48, 0xA5], [0xF2, 0xAE], [0xAC], [0xA6]].all
    (fun (w : List Byte) => strClaims w && decodeStr w == none) = true := by decide

/-- Non-string forms are not claimed: `lea -1(%rdi,%rcx), %rdi` (`48 8D 7C 0F FF`),
`ret` (`C3`), `vmovdqu (%rsi), %ymm0` (`C5 FE 6F 06`), `std` and `cld`. -/
example : [[0x48, 0x8D, 0x7C, 0x0F, 0xFF], [0xC3], [0xC5, 0xFE, 0x6F, 0x06], [0xFD], [0xFC]].all
    (fun (w : List Byte) => !strClaims w) = true := by decide

/-! ## The laws of the layer's forms -/

/-- **`std` at a listed offset** sets DF. -/
theorem step_of_listed_std {d : DState} {base : Word} {code : List Byte} {o : Nat}
    (hl : Loaded d.memory base code) (hrip : d.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + 1 ≤ code.length) (hb : (code.drop o).take 1 = [0xFD]) :
    step d = some ⟨Str9V.coreV d.v { d.core with rip := d.core.rip + BitVec.ofNat 64 1 } d.memory,
      true⟩ :=
  step_of_fetch_flag (fetched_of_listed hl hrip (by decide) hfit) (by rw [hb]; rfl)
    (by rw [hb]; exact lowerBad_std)

/-- **`cld` at a listed offset** clears DF. -/
theorem step_of_listed_cld {d : DState} {base : Word} {code : List Byte} {o : Nat}
    (hl : Loaded d.memory base code) (hrip : d.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + 1 ≤ code.length) (hb : (code.drop o).take 1 = [0xFC]) :
    step d = some ⟨Str9V.coreV d.v { d.core with rip := d.core.rip + BitVec.ofNat 64 1 } d.memory,
      false⟩ :=
  step_of_fetch_flag (fetched_of_listed hl hrip (by decide) hfit) (by rw [hb]; rfl)
    (by rw [hb]; exact lowerBad_cld)

/-- **A string form at a listed offset with DF set** runs one element downwards. -/
theorem step_of_listed_str {d : DState} {base : Word} {code : List Byte} {o : Nat} {f : Str}
    {c : State} {mem : Memory} (hdf : d.df = true) (hl : Loaded d.memory base code)
    (hrip : d.core.rip = base + BitVec.ofNat 64 o) (hfit : o + f.bytes.length ≤ code.length)
    (hb : (code.drop o).take f.bytes.length = f.bytes)
    (hx : execStr true f d.core d.memory (d.core.rip + BitVec.ofNat 64 f.bytes.length) =
      some (c, mem)) :
    step d = some (d.upd c mem) := by
  have hpos : 0 < f.bytes.length := by cases f <;> decide
  have h15 : f.bytes.length ≤ maxInstrLength := by cases f <;> decide
  have hdec : decodeStr f.bytes = some (f, f.bytes.length) := by cases f <;> decide
  have fetched := fetched_of_listed hl hrip hpos hfit
  rw [hb] at fetched
  exact step_of_fetch_str hdf fetched h15 hdec hx

/-! ## The machine -/

/-- **`Str9D` as a segment-VC instance** over `Str9FsX`'s integer instructions that are not
string forms; `std`, `cld` and the string forms have the laws above. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa DState where
  Instr := Silmaril.X86.Str9FsX.Instr
  instDecEq := inferInstance
  decode := decode
  exec := Silmaril.X86.Str9FsX.exec
  core := fun d => d.core
  mem := fun d => d.memory
  upd := fun d c m => d.upd c m
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_listed hl hrip hfit hdec hx

@[simp] theorem isa_step : isa.step = step := rfl

end Silmaril.X86.Str9D
