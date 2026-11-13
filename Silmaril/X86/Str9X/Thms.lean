module

public import Silmaril.Raw.X86.Str9X

/-!
# `Str9X`: the conservative extension of `Str9D`, the x87 listing law, the machine

* `step_of_str9d`: **every `Str9D` step is a step** (the x87 forms are tried only where every
  decoder of `Str9D` rejects the bytes), so `extendsStr9D : Str9D.isa.Extends isa` (lens
  `x ↦ x.d`, the x87 state the frame), and `run_of_str9v`: every `Str9V` run from DF clear is
  a run here.
* `step_of_fetch_fpu`, `step_of_listed_fpu`: the law of an x87 form (`decodeL`, `execFpu`).

The proofs are in `Silmaril.Raw.X86.Str9X` (valid, not yet in Isar style), re-exported here.
`Str9X/Vectors.lean` runs the x87 lane's native vectors through `Str9X.step`.
-/

@[expose] public section

namespace Silmaril.X86.Str9X

open Silmaril.X86 (Byte)
open Silmaril.Machine.Execution (run Reaches)

/-! ## Decoding facts (kernel-checked) -/

/-- The x87 forms of the census are listed x87 forms of their own length: `fldt 0x10(%rsp)`
(`DB 6C 24 10`), `fstpt (%rdi)` (`DB 3F`), `fld %st(1)` (`D9 C1`), `fxch %st(1)` (`D9 C9`),
`fmulp %st, %st(1)` (`DE C9`), `fucomip %st(1), %st` (`DF E9`), `fnstcw 0xe(%rsp)`
(`D9 7C 24 0E`), `fldcw 0xc(%rsp)` (`D9 6C 24 0C`), `fistpll (%rsp)` (`DF 3C 24`),
`fildll 0x8(%rsp)` (`DF 6C 24 08`), `fldt 0x10(%r12)` (`41 DB 6C 24 10`), `fwait` (`9B`). -/
example : [[0xDB, 0x6C, 0x24, 0x10], [0xDB, 0x3F], [0xD9, 0xC1], [0xD9, 0xC9], [0xDE, 0xC9],
    [0xDF, 0xE9], [0xD9, 0x7C, 0x24, 0x0E], [0xD9, 0x6C, 0x24, 0x0C], [0xDF, 0x3C, 0x24],
    [0xDF, 0x6C, 0x24, 0x08], [0x41, 0xDB, 0x6C, 0x24, 0x10], [0x9B]].all
    (fun (e : List Byte) => (decodeL e).map (·.2) == some e.length) = true := by decide

/-! ## The machine -/

/-- **`Str9X` as a segment-VC instance** over `Str9D`'s integer instructions; the x87 forms
have `step_of_listed_fpu`. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa XState where
  Instr := Silmaril.X86.Str9FsX.Instr
  instDecEq := inferInstance
  decode := Str9D.decode
  exec := Silmaril.X86.Str9FsX.exec
  core := fun x => x.core
  mem := fun x => x.memory
  upd := fun x c m => ⟨x.d.upd c m, x.fpu⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ =>
    step_of_str9d (Str9D.step_of_listed hl hrip hfit hdec hx)

@[simp] theorem isa_step : isa.step = step := rfl

/-- **`Str9X` extends `Str9D`** along `x ↦ x.d` (the x87 state is the frame). -/
@[reducible] def extendsStr9D : Str9D.isa.Extends isa where
  view x := x.d
  put x d := ⟨d, x.fpu⟩
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core _ := rfl
  mem _ := rfl
  upd _ _ _ := rfl
  live _ _ := trivial
  step h := step_of_str9d h

/-- **Every `Str9V` run from DF clear is a run**, with DF still clear and the x87 state
kept. -/
theorem run_of_str9v {n : Nat} {v v' : Str9V.VState} (fpu : Silmaril.X86.Features.X87)
    (h : run Str9V.step n v = some v') : run step n ⟨⟨v, false⟩, fpu⟩ = some ⟨⟨v', false⟩, fpu⟩ :=
  extendsStr9D.run n (x := ⟨⟨v, false⟩, fpu⟩) (Str9D.run_of_str9v h)

/-- A `Str9V` run from DF clear reaches the same state here. -/
theorem reaches_of_str9v {v v' : Str9V.VState} (fpu : Silmaril.X86.Features.X87)
    (h : Reaches Str9V.step v v') : Reaches step ⟨⟨v, false⟩, fpu⟩ ⟨⟨v', false⟩, fpu⟩ :=
  let ⟨n, hn⟩ := h; ⟨n, run_of_str9v fpu hn⟩

end Silmaril.X86.Str9X
