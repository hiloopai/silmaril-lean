module

public import Silmaril.Elf.Link.Dyn.Cert.Defs
public import Silmaril.Elf.Link.Dyn.Image.Thms
public import Silmaril.Elf.Link.Dyn.Proc.Defs

/-! # Block certificates: code is not writable, from the loader

`codeRO_of_imageOk`: any range of a `PT_LOAD` segment without the write flag is not writable in a
memory the loader relation (`ImageOk`) describes, so the `CodeRO` premise of `Cert.must_blk`
follows from the loader for code in an `r-x` segment.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Cert

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.Dyn

/-- **Code in a segment without the write flag is not writable.** -/
theorem codeRO_of_imageOk {o : Obj} {i : Elf.DynInfo} {T : List (Nat × Option Word)} {mem : Memory}
    (h : ImageOk o i T mem) {ph : Elf.Phdr} (hph : ph ∈ i.phs) (hk : ph.kind = 1)
    (hw : ph.flags / 2 % 2 = 0) {v : Nat} {code : List Byte} (hv : ph.vaddr ≤ v)
    (hend : v + code.length ≤ ph.vaddr + ph.memsz) : CodeRO mem (o.base + BitVec.ofNat 64 v) code := by
  intro k hk'
  obtain ⟨hwrap, -, -, hwp, -⟩ := h.point hph hk (v := v + k) (by omega) (by omega)
  rw [addr_toNat (by omega), Nat.add_assoc, hwp, hw]
  rfl

/-- `CodeRO` survives any change that keeps the code's addresses (`Keeps` keeps permissions). -/
theorem CodeRO.keep {m m' : Memory} {base : Word} {code : List Byte} (h : CodeRO m base code)
    {P : Nat → Prop} (hk : Proc.Keeps P m m') (hP : ∀ k, k < code.length → P (base.toNat + k)) :
    CodeRO m' base code := fun k hk' => by
  rw [(hk _ (hP k hk')).2]; exact h k hk'

end Silmaril.Elf.Link.Dyn.Cert
