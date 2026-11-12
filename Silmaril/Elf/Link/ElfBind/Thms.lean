module

public import Silmaril.Elf.Link.ElfBind.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms
public import Silmaril.Raw.Elf.Link.ElfBind

/-! # Code bound in a loaded file is fetchable

* `leBytes_valueLE`: the bytes of a byte list's little-endian value are the list.
* `codeAt_elim` (in `Silmaril.Raw.Elf.Link.ElfBind`): what `CodeAt` read (the segment and
  the file bytes).
* `code_loaded`: if `F` holds `code` at `v` (`CodeAt`) and its read-only segments are loaded
  at a placement `base` (`RoLoaded`, `Placement`), then `code` is fetchable at `base + v`,
  that address does not wrap, and every byte of the code lies in the file's image
  (`InImage`). This is the step from a binding fact about the file to the precondition of a
  function-level contract (`Silmaril.X86.Ext.Loaded`).
* `placement_zero`: a file whose type and `PT_LOAD`s pass `placeOk` has the placement `0`.

Standard axioms only.
-/

@[expose] public section

namespace Silmaril.Elf.Link.ElfBind

open Silmaril.Elf.Link.DynElf
open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)

theorem leBytes_succ (n w : Nat) :
    leBytes n (w + 1) = BitVec.ofNat 8 n :: leBytes (n >>> 8) w := by
  unfold leBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show 8 * (i + 1) = 8 + 8 * i by omega, Nat.shiftRight_add]

/-- **The bytes of a byte list's value are the list.** -/
theorem leBytes_valueLE : ∀ code : List Byte, leBytes (Blob.valueLE code) code.length = code
  | [] => rfl
  | b :: bs => by
    rw [List.length_cons, leBytes_succ]
    have hb := b.isLt
    have h1 : BitVec.ofNat 8 (Blob.valueLE (b :: bs)) = b := by
      apply BitVec.eq_of_toNat_eq
      simp only [Blob.valueLE, BitVec.toNat_ofNat]
      omega
    have h2 : Blob.valueLE (b :: bs) >>> 8 = Blob.valueLE bs := by
      simp only [Blob.valueLE, Nat.shiftRight_eq_div_pow]
      omega
    rw [h1, h2, leBytes_valueLE bs]

/-- **Bound code is fetchable where the file is loaded** (module doc). -/
theorem code_loaded {F : Blob} {base : Word} {mem : Memory} {v : Nat} {code : List Byte}
    (hc : CodeAt F v code) (hp : Placement F base) (hl : RoLoaded F base mem) :
    mem.fetchBytes (base + BitVec.ofNat 64 v).toNat code.length = some code ∧
      (base + BitVec.ofNat 64 v).toNat = base.toNat + v ∧
      ∀ a, base.toNat + v ≤ a → a < base.toNat + v + code.length → InImage F base a := by
  obtain ⟨phs, ph, hphs, hm, hld, hro, hx, hv, hw, hrd⟩ := codeAt_elim hc
  obtain ⟨t, phs', -, hphs', -, hok⟩ := hp
  rw [hphs] at hphs'
  cases hphs'
  obtain ⟨hfm, hlim⟩ := hok ph hm hld
  have hadd : (base + BitVec.ofNat 64 v).toNat = base.toNat + v := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : v < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  have hf := (hl phs hphs ph hm hld hro (ph.off + (v - ph.vaddr)) code.length (Blob.valueLE code)
    (by omega) (by omega) hrd).2 hx
  rw [show base.toNat + ph.vaddr + (ph.off + (v - ph.vaddr) - ph.off) = base.toNat + v by omega,
    leBytes_valueLE] at hf
  refine ⟨hadd ▸ hf, hadd, fun a h1 h2 => ⟨phs, hphs, ph, hm, hld, by omega, by omega⟩⟩

/-- A placement is page-aligned. -/
theorem placement_aligned {F : Blob} {base : Word} (h : Placement F base) : base.toNat % 4096 = 0 := by
  obtain ⟨t, phs, -, -, hb, -⟩ := h
  rcases hb with ⟨-, rfl⟩ | ⟨-, h⟩
  · rfl
  · exact h

/-- The placement check of `base = 0`: an `ET_EXEC` or `ET_DYN` file whose `PT_LOAD`s have
`filesz ≤ memsz` and end below `2^47`. -/
def placeOk (t : Nat) (phs : List DynElf.Elf.Phdr) : Bool :=
  (t == 2 || t == 3) && phs.all fun ph =>
    !isLoad ph || (decide (ph.filesz ≤ ph.memsz) && decide (ph.vaddr + ph.memsz ≤ 2 ^ 47))

/-- **The base `0` is a placement** of a file that passes `placeOk`. -/
theorem placement_zero {F : Blob} {t : Nat} {phs : List DynElf.Elf.Phdr}
    (ht : Elf.etype.run (blobRead F) = some t) (hp : phdrsOf F = some phs)
    (h : placeOk t phs = true) : Placement F 0 := by
  unfold placeOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨htt, hall⟩ := h
  refine ⟨t, phs, ht, hp, ?_, fun ph hm hld => ?_⟩
  · rcases htt with h2 | h3
    · exact .inl ⟨h2, rfl⟩
    · exact .inr ⟨h3, by decide⟩
  · rcases hall ph hm with h | ⟨h1, h2⟩
    · rw [hld] at h; cases h
    · exact ⟨h1, by simpa using h2⟩

/-- The placement check of `base = 0` as one reading program. -/
def placeOkRd : Rd Bool := do
  let t ← Elf.etype
  let phs ← DynElf.Elf.phdrs
  pure (placeOk t phs)

/-- **The base `0` is a placement** of a file on which `placeOkRd` reads `true`. -/
theorem placement_of_rd {F : Blob} (h : placeOkRd.run (blobRead F) = some true) :
    Placement F 0 := by
  unfold placeOkRd at h
  change ((Elf.etype).bind _).run _ = _ at h
  rw [Rd.run_bind] at h
  cases ht : Elf.etype.run (blobRead F) with
  | none => rw [ht] at h; cases h
  | some t =>
    rw [ht, Option.bind_some] at h
    change ((DynElf.Elf.phdrs).bind _).run _ = _ at h
    rw [Rd.run_bind] at h
    cases hp : DynElf.Elf.phdrs.run (blobRead F) with
    | none => rw [hp] at h; cases h
    | some phs =>
      rw [hp, Option.bind_some] at h
      exact placement_zero ht hp (Option.some.inj h)

end Silmaril.Elf.Link.ElfBind
