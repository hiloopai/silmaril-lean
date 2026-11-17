module

public import Silmaril.Elf.Load.Defs
public import Silmaril.Elf.Staged.Reader.Defs
public import Silmaril.Elf.Facts.Defs
import Silmaril.Proofs.Elf.Load

/-! # ELF adapters: theorems

* `readOnlyAt_of_kbytes`: `ReadOnlyAt` of an `include_bytes` file from one kernel read of its
  kernel bytes (as `Staged.Reader.codeAt_of_kbytes`); `readOnlyAt_segBytes`: it is `SegBytes` in a
  read-only segment.
* `byteAt_of_fileBytes`: the bytes `FileBytes` names are the file's bytes, one by one.
* `untouched_sub`: an untouched range is untouched byte by byte.
* `readWith_of_segBytes`: **in a memory holding the image at `base`, an untouched range of a
  segment reads back as the file's bytes at `base + v`** (any access the memory permits there:
  `.execute` for code, `.read` for data).
* `not_present_of_absent`: a name no table defines is not a present function.

Proofs: `Silmaril.Proofs.Elf.Load` (standard axioms only).
-/

@[expose] public section

namespace Silmaril.Elf.Load

open Silmaril.Elf.Image
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

theorem readOnlyAt_of_kbytes {x : KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) {A : File} (hp : Parses (blobOf ⟨raw⟩) A) {v : Nat}
    {bytes : List (BitVec 8)} {ph : Silmaril.Formats.ELF.ProgramHeader}
    (hf : A.phdrs.find? (roSeg v bytes.length) = some ph)
    (hc : Staged.Reader.kread x (ph.offset + (v - ph.virtualAddress)) bytes.length =
      some (Blob.valueLE bytes)) : ReadOnlyAt (blobOf ⟨raw⟩) v bytes :=
  ⟨A, hp, ph, hf, Staged.Reader.sub_kbytes hx h _ _ _ hc⟩

theorem readOnlyAt_segBytes {F : Blob} {v : Nat} {bytes : List (BitVec 8)}
    (h : ReadOnlyAt F v bytes) :
    ∃ A, Parses F A ∧ ∃ i ph, A.phdrs[i]? = some ph ∧ roSeg v bytes.length ph = true ∧
      SegBytes F A i v (ph.offset + (v - ph.virtualAddress)) bytes :=
  Proofs.Elf.Load.readOnlyAt_segBytes h

theorem byteAt_of_fileBytes {F : Blob} {o : Nat} {bytes : List (BitVec 8)}
    (h : FileBytes F o bytes) (k : Nat) (hk : k < bytes.length) :
    Blob.byteAt F.n (o + k) = bytes[k] :=
  Proofs.Elf.Load.byteAt_of_fileBytes h k hk

theorem untouched_sub {A : File} {v n k : Nat} (h : Untouched A v n) (hk : k < n) :
    Untouched A (v + k) 1 :=
  Proofs.Elf.Load.untouched_sub h hk

/-- **Loaded, untouched segment bytes read back as the file's.** -/
theorem readWith_of_segBytes {F : Blob} {A : File} {base : Nat} {mem : Silmaril.Process.Memory}
    (hL : ImageLoaded F A base mem) {i v o : Nat} {bytes : List (BitVec 8)}
    (hs : SegBytes F A i v o bytes) (hu : Untouched A v bytes.length)
    {acc : Silmaril.Process.Access} (hp : mem.Permitted acc (base + v) bytes.length) :
    mem.readWith acc (base + v) bytes.length = some bytes :=
  Proofs.Elf.Load.readWith_of_segBytes hL hs hu hp

theorem not_present_of_absent {F : Blob} {n : Silmaril.Formats.ELF.NameBytes}
    (ha : AbsentName F n) : ¬ PresentFn F n :=
  Proofs.Elf.Load.not_present_of_absent ha

/-- **`ReadOnlyAt` with `Unambiguous`: the read-only segment is the only one.** Every byte of the
range has exactly that segment as its origin, so no writable segment maps it. (`ReadOnlyAt`
alone is a first match: `Examples.overlap_first`.) -/
theorem readOnlyAt_unique {F : Blob} {A : File} (hA : Parses F A) {v : Nat}
    {bytes : List (BitVec 8)} (hr : ReadOnlyAt F v bytes) (hu : Unambiguous A v bytes.length) :
    ∃ i ph, A.phdrs[i]? = some ph ∧ roSeg v bytes.length ph = true ∧
      ∀ k, k < bytes.length →
        A.origins (v + k) = [(i, Origin.file (ph.offset + (v - ph.virtualAddress) + k))] :=
  Proofs.Elf.Load.readOnlyAt_unique hA hr hu

/-- **A `.symtab` lookup finds a defined function entry** with the name looked up. -/
theorem lookup_sym_entry {F : Blob} {n : Silmaril.Formats.ELF.NameBytes} {d : Def}
    (h : Lookup F (.sym n) (some d)) :
    ∃ A, Parses F A ∧ ∃ s, (A.symbols .symtab)[d.index]? = some s ∧ s.name = n ∧
      s.raw.sectionIndex ≠ 0 ∧ (s.raw.kind = 2 ∨ s.raw.kind = 10) :=
  Proofs.Elf.Load.lookup_sym_entry h

/-- For `.sym`, `LookupFn` is the lookup. -/
theorem lookupFn_sym {F : Blob} {n : Silmaril.Formats.ELF.NameBytes} {d : Def}
    (h : Lookup F (.sym n) (some d)) : LookupFn F (.sym n) d := by
  obtain ⟨A, hA, s, hs, -, -, hk⟩ := lookup_sym_entry h
  have hk' : s.kind = 2 ∨ s.kind = 10 := hk
  exact ⟨h, A, hA, by simp only [File.funcAt, selTable, hs]; rcases hk' with h' | h' <;> simp [h']⟩

/-- **In a memory holding the image at `base`, untouched code reads back** (`CodeAt` form). For
`ET_DYN`, `base` ranges over the bases `Placement F base` admits; nothing here says a loader
produced `mem` (`ImageLoaded` is the loading relation, a hypothesis). -/
theorem readWith_of_codeAt {F : Blob} {A : File} (hA : Parses F A) {base : Nat}
    {mem : Silmaril.Process.Memory} (hL : ImageLoaded F A base mem) {v : Nat}
    {code : List (BitVec 8)} (hc : CodeAt F v code) (hu : Untouched A v code.length)
    {acc : Silmaril.Process.Access} (hp : mem.Permitted acc (base + v) code.length) :
    mem.readWith acc (base + v) code.length = some code :=
  Proofs.Elf.Load.readWith_of_codeAt hA hL hc hu hp

/-- The same for read-only data. -/
theorem readWith_of_readOnlyAt {F : Blob} {A : File} (hA : Parses F A) {base : Nat}
    {mem : Silmaril.Process.Memory} (hL : ImageLoaded F A base mem) {v : Nat}
    {bytes : List (BitVec 8)} (hr : ReadOnlyAt F v bytes) (hu : Untouched A v bytes.length)
    {acc : Silmaril.Process.Access} (hp : mem.Permitted acc (base + v) bytes.length) :
    mem.readWith acc (base + v) bytes.length = some bytes :=
  Proofs.Elf.Load.readWith_of_readOnlyAt hA hL hr hu hp

end Silmaril.Elf.Load
